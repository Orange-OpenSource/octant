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

import csv
import sys

from octant.datalog import z3_result as z3r


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
        if isinstance(elt, z3r.Cube):
            compute_len_cube(elt)
        elif isinstance(elt, z3r.Doc):
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
            z3r.Any() if i not in c.faces else c.faces[i]
            for i in range(len(vars))])

    print(draw_sep('='))
    print(draw_row(' ', vars))
    print(draw_sep('='))
    for elt in answers:
        if isinstance(elt, z3r.Cube):
            print(draw_cube('+', elt))
        elif isinstance(elt, z3r.Doc):
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
        return [p] + [cube.faces[i] if i in cube.faces else z3r.Any()
                      for i in range(len(variables))]
    if isinstance(answers, list):
        csvwriter = csv.writer(sys.stdout)
        csvwriter.writerow(['P'] + variables)
        for elt in answers:
            if isinstance(elt, z3r.Cube):
                csvwriter.writerow(row_of_cube('+', elt))
            elif isinstance(elt, z3r.Doc):
                csvwriter.writerow(row_of_cube('+', elt.base))
                for d in elt.diffs:
                    csvwriter.writerow(row_of_cube('-', d))
    else:
        print(str(answers))
    print()
