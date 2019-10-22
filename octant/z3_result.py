#    Copyright 2019 Orange
#
#    Licensed under the Apache License, Version 2.0 (the "License"); you may
#    not use this file except in compliance with the License. You may obtain
#    a copy of the License at
#
#         http://www.apache.org/licenses/LICENSE-2.0
#
#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
#    WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
#    License for the specific language governing permissions and limitations
#    under the License.

from __future__ import print_function

import collections
import csv
import itertools
from six import moves
import sys
import z3

from octant import base


class Any(object):
    """Representation of an unconstrained value"""
    def __repr__(self):
        return '*'


class Masked(tuple):
    """Representation of a value constrained over a mask of bits"""
    def __new__(self, x, y):
        return tuple.__new__(Masked, (x, y))

    def __repr__(self):
        return (
            str(self[0]) if self[1] is None
            else "*" if self[1] == 0 else "%s/%s" % self)


class Cube(object):
    """A cube: ie a set of constraints over different variables

    variables are in DeBruijn notation. Cube is defined as a dictionary
    """

    def __init__(self, faces):
        """Constructor for cube

        :param faces: dictionnary from variable index to constraint
           (Masked, value or Any)
        """
        self.faces = faces

    def __repr__(self):
        return str([self.faces[i] for i in range(len(self.faces))])

    def __eq__(self, x):
        return isinstance(x, self.__class__) and x.faces == self.faces


class Doc(object):
    """Difference of cubes"""

    def __init__(self, bas, diffs):
        """constructor for difference of cubes

        :param base: the base cube
        :param diffs: the array of cubes substracted from the base
        """
        self.base = bas
        self.diffs = diffs

    def __repr__(self):
        return "%s \\ (%s)" % (self.base, ", ".join(map(str, self.diffs)))

    def __eq__(self, x):
        return (
            isinstance(x, self.__class__) and
            x.base == self.base and x.diffs == self.diffs)


ResultItem = collections.namedtuple(
    'ResultItem',
    ['var', 'value', 'mask'])
"""A streamlined result as a variable.

its potential value, its mask and whether it is  substracted."""


def fuse(list, typ):
    """Coalesce an array of potential values into a single value/mask"""
    if len(list) == 1:
        elt = list[0]
        if elt.mask is None:
            res = typ.to_os(elt.value)
        else:
            res = Masked(typ.to_os(elt.value), typ.to_os(elt.mask))
        return res
    else:
        sort = list[0].value.sort()

        def compute(x, y):
            return (z3.simplify(x[0] | y.value), z3.simplify(x[1] | y.mask))

        zero = z3.BitVecVal(0, sort)
        pair = moves.reduce(compute, list, (zero, zero))
        return Masked(typ.to_os(pair[0]), typ.to_os(pair[1]))


def extract_equal(eq):
    """Transform equals in a triple: var index, value, mask"""
    if isinstance(eq.children()[0], z3.BitVecNumRef):
        rhs = eq.children()[0]
        lhs = eq.children()[1]
    else:
        rhs = eq.children()[1]
        lhs = eq.children()[0]
    if z3.is_var(lhs):
        return ResultItem(
            var=z3.get_var_index(lhs),
            value=rhs,
            mask=None)
    else:
        kind = lhs.decl().kind()
        if kind == z3.Z3_OP_EXTRACT:
            [high, low] = lhs.params()
            sort = lhs.children()[0].sort()
            val = rhs.as_long() << low
            mask = (1 << (high + 1)) - (1 << low)
            return ResultItem(
                var=z3.get_var_index(lhs.children()[0]),
                value=z3.BitVecVal(val, sort),
                mask=z3.BitVecVal(mask, sort))
        else:
            raise base.Z3NotWellFormed(
                "Bad lhs for equal  {}".format(eq))


def make_cube(itemlist, types):
    """Creates a cube from a list

    :param itemlist: a list of ResultItem
    :param types: types of variables so that we can translate back values to OS
    representation.
    :return: a cube
    """
    translist = [
        extract_equal(item)
        for item in itemlist
        if item.decl().kind() == z3.Z3_OP_EQ   # remove True
    ]
    return Cube({
        var: fuse(list(grp), types[var])
        for var, grp in itertools.groupby(translist, key=lambda t: t.var)})


def split_cubes(itemlist, types):
    """Split result formula in positive cube elements and substracted cubes"""

    def cube_list_from_not(item):
        """Auxiliary function for substracted cubes"""
        negated = item.children()[0]
        kind = negated.decl().kind()
        if kind == z3.Z3_OP_AND:
            return negated.children()
        else:
            return [negated]

    positive = filter(
        lambda item: item.decl().kind() != z3.Z3_OP_NOT, itemlist)
    subtracted = filter(
        lambda item: item.decl().kind() == z3.Z3_OP_NOT, itemlist)
    cube = make_cube(positive, types)
    neg_cubes = [
        make_cube(cube_list_from_not(item), types) for item in subtracted]
    return cube if neg_cubes == [] else Doc(cube, neg_cubes)


def extract_and(item, types):
    """Extract a row"""
    kind = item.decl().kind()
    if kind == z3.Z3_OP_AND:
        return split_cubes(item.children(), types)
    elif kind == z3.Z3_OP_EQ or kind == z3.Z3_OP_NOT:
        return split_cubes([item], types)
    else:
        raise base.Z3NotWellFormed(
            "Bad result  {}: {}".format(item, kind))


def z3_to_array(expr, types):
    """Compiles back a Z3 result to a matrix of values"""

    kind = expr.decl().kind()
    if kind == z3.Z3_OP_OR:
        return [extract_and(item, types) for item in expr.children()]
    elif kind == z3.Z3_OP_AND:
        return [split_cubes(expr.children(), types)]
    elif kind == z3.Z3_OP_EQ or kind == z3.Z3_OP_NOT:
        return [split_cubes([expr], types)]
    elif kind == z3.Z3_OP_FALSE:
        return False
    elif kind == z3.Z3_OP_TRUE:
        return True
    else:
        raise base.Z3NotWellFormed("Bad result {}: {}".format(expr, kind))


def print_pretty(vars, answers):
    """Pretty print a result.

    :param vars: list of requested variables
    :param answers: list of alternative doc results
    """
    # init length
    lengths = [len(var) for var in vars]

    # compute length
    def compute_len_cube(cube):
        for key, val in cube.faces.items():
            lengths[key] = max(lengths[key], len(str(val)))

    def compute_len(elt):
        if isinstance(elt, Cube):
            compute_len_cube(elt)
        elif isinstance(elt, Doc):
            compute_len_cube(elt.base)
            for d in elt.diffs:
                compute_len_cube(d)

    for doc in answers:
        compute_len(doc)

    def draw_sep(c):
        return (
            '+' + c * 3 + '+' +
            '+'.join(map(lambda l: c * (2 + l), lengths)) + '+')

    def print_elt(pair):
        (i, val) = pair
        full_len = lengths[i]
        out = str(val)
        return out + ' ' * (full_len - len(out))

    def draw_row(pos, l):
        return (
            '| ' + pos + ' | ' +
            ' | '.join(map(print_elt, enumerate(l))) + ' |')

    def draw_cube(pos, c):
        return draw_row(pos, [
            Any() if i not in c.faces else c.faces[i]
            for i in range(len(vars))])

    print(draw_sep('='))
    print(draw_row(' ', vars))
    print(draw_sep('='))
    for elt in answers:
        if isinstance(elt, Cube):
            print(draw_cube('+', elt))
        elif isinstance(elt, Doc):
            print(draw_cube('+', elt.base))
            print(draw_sep('-'))
            for d in elt.diffs:
                print(draw_cube('-', d))
        print(draw_sep('='))


def print_csv(variables, answers):
    """Print the result of a query in excel csv format

    :param vars: list of requested variables
    :param answers: list of alternative doc results
    """

    def row_of_cube(p, cube):
        return [p] + [cube.faces[i] if i in cube.faces else Any()
                      for i in range(len(variables))]
    if isinstance(answers, list):
        csvwriter = csv.writer(sys.stdout)
        csvwriter.writerow(['P'] + variables)
        for elt in answers:
            if isinstance(elt, Cube):
                csvwriter.writerow(row_of_cube('+', elt))
            elif isinstance(elt, Doc):
                csvwriter.writerow(row_of_cube('+', elt.base))
                for d in elt.diffs:
                    csvwriter.writerow(row_of_cube('-', d))
    else:
        print(str(answers))
    print()
