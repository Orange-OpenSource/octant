# -*- coding: utf-8 -*-

#    Copyright 2018 Orange
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

import itertools
import six

from octant import ast


class UFType(object):
    """Base class for unfolding types"""
    pass


class UFBot(UFType):
    """Bottom type corresponds to no information at all"""
    def __eq__(self, other):
        return isinstance(other, self.__class__)

    def __hash__(self):
        return 1

    def __repr__(self):
        return "UFBot"


class UFTop(UFType):
    """Top type means any value"""
    def __eq__(self, other):
        return isinstance(other, self.__class__)

    def __hash__(self):
        return 2

    def __repr__(self):
        return "UFTop"


class UFGround(UFType):
    """Coerced to be a ground value of parameter at a given position

    .. py:attribute:: pos:

        position of the argument in the table (integer starting at 0)

    .. py:attribute:: table:

        table of the EDB defining the ground term (str)

    .. py:attribute:: occurrence:

        An occurrence list defining in a unique way the instance
        of the ground term in use. (linked list represented as pair or None.
        Elements are pairs of a rule identifier (int) and a position of the
        atom in the body (int))
    """

    def __init__(self, pos, table, occurrence):
        self.pos = pos
        self.table = table
        self.occurrence = occurrence

    def __eq__(self, other):
        return (
            isinstance(other, self.__class__) and other.pos == self.pos and
            other.table == self.table and other.occurrence == self.occurrence)

    def __hash__(self):
        return hash((self.pos, self.table, self.occurrence))

    def __repr__(self):
        return "UFGround(%s,%d,%s)" % (self.table, self.pos, self.occurrence)


class UFConj(UFType):
    """Conjunctions of types

    It represent a conjunct of constraints on the origin. It is usually
    simplified at some point as one of the origins.
    """
    def __init__(self, args):
        #: the members of the conjunct: args
        self.args = args

    def __eq__(self, other):
        return isinstance(other, self.__class__) and other.args == self.args

    def __hash__(self):
        return hash(self.args)

    def __repr__(self):
        return "UFConj(%s)" % (self.args,)


class UFDisj(UFType):
    """Disjunctions of types

    The values of the element may come from either origins.
    """

    def __init__(self, args):
        #: the members of the disjunct: args
        self.args = args

    def __eq__(self, other):
        return isinstance(other, self.__class__) and other.args == self.args

    def __hash__(self):
        return hash(self.args)

    def __repr__(self):
        return "UFDisj(%s)" % (self.args,)


top = UFTop()
bot = UFBot()


def is_ground(t):
    """Return true is object is a ground object

    :param UFType t: type to check
    :return: true if ground false otehrwise
    :rtype: bool
    """
    return isinstance(t, UFGround)


def is_disj(t):
    """Return true is object is a disjonction

    :param UFType t: type to check
    :return: true if disjonction false otehrwise
    :rtype: bool
    """
    return isinstance(t, UFDisj)


def occurrence(t):
    """Computes an occurrence for the whole types

    Occcurrence shouldbe seen as unique ID
    :param UFType t: type to analyze
    :return: all the occurrences
    :rtype: tuple
    """
    if is_ground(t):
        return t.occurrence
    if is_disj(t):
        return tuple(occurrence(a) for a in t.args)
    return None


def simplify_to_ground_types(t):
    """Gives back simple ground or disjunction"""
    if is_ground(t) or is_disj(t):
        return [t]
    if isinstance(t, UFConj):
        return [g for a in t.args for g in simplify_to_ground_types(a)]
    return []


def contains_mark(occ, mark):
    if isinstance(occ, tuple) and len(occ) == 2:
        if mark == occ[0]:
            return True
        return contains_mark(occ[1], mark)
    return False


def len_occ(occ):
    """Compute length of the occurrence pseudo list

    We use pairs and not regular lists because we want a hashable
    non mutable element.
    """
    count = 0
    while isinstance(occ, tuple) and len(occ) == 2:
        count = count + 1
        occ = occ[1]
    return count


def weight_type(t):
    """Weight function for types.

    To use in sorting but also min/max.
    The smaller, the better. Returns a pair for lexicographic ordering.
    """
    if is_ground(t):
        return 0, len_occ(t.occurrence)
    if isinstance(t, (UFDisj, UFConj)):
        return 1, len(t.args)
    else:
        return 2, 0


def wrap_type(typ, mark):
    """Identifies the provenance of type as a given atom

    :param type: the type to wrap
    :param mark: mark to add. usually the identifier of rule containing the
        atom occurrence and the position of this atom in the body of the rule
    :return: modified type
    """
    if is_ground(typ):
        if contains_mark(typ.occurrence, mark):
            return typ
        return UFGround(typ.pos, typ.table, (mark, typ.occurrence))
    if is_disj(typ):
        return UFDisj(tuple(wrap_type(t, mark) for t in typ.args))
    if isinstance(typ, UFConj):
        return UFConj(tuple(wrap_type(t, mark) for t in typ.args))
    return typ


def head_table(rule):
    """Table name of the head of a rule"""
    return rule.head.table


def reduce_disj(l):
    """Disjunction simplification

    First it removes embedded disjunction.
    """
    flat = {
        x
        for e in l
        for x in (e.args if is_disj(e) else (e,))}
    if len(flat) == 1:
        return flat.pop()
    disj = top if top in flat else UFDisj(tuple(flat))
    return disj


def reduce_conj(l):
    """Conjunct simplification

    First it removes embedded conjunctions.
    If there is at least one ground type in the conjunct, keep all those ground
    types. Otherwise only keep the best of the conjunct and throw away the
    others.

    :param l: the list of types that could build the conjunct. It
        must be sorted.
    :return: a conjunct with more than one type or what was considered as the
        best type
    :rtype: UFType
    """
    flat = [
        x
        for e in l
        for x in (e.args if isinstance(e, UFConj) else (e,))]
    flat.sort(key=weight_type)
    if len(flat) > 1 and is_ground(flat[0]):
        return UFConj(tuple(filter(is_ground, flat)))
    return flat[0]


class Origin(object):
    """Origin computes types for unfolding."""

    def __init__(self, rules, extensible_tables):
        """Unfolding constructor

        :param rules: A list of rules as AST with unique variables and
          primitive tables with labels solved.
        :param extensible_tables: A mapping from table names to a pair of
          boolean and number specifying if the table is extentional and
          the arity of the table.
        :param compiler: a compiler of constants to Z3
        """
        self.rules = rules
        self.rules.sort(key=head_table)
        self.tables = {}
        self.grounds = {}
        self.table_types = {}
        self.var_types = {}
        self.populate_tables(extensible_tables)

    def populate_tables(self, extensible_tables):
        """Initialize tables field

        It is a map from table name to their arity and the fact they are
        in the IDB or the EDB
        """
        for table, args in six.iteritems(extensible_tables):
            self.tables[table] = (len(args), True)
        for table, group_rule in itertools.groupby(self.rules, key=head_table):
            self.tables[table] = (len(list(group_rule)[0].head.args), False)

    def get_partially_ground_preds(self):
        """Gives back a map of the ground arguments of a table

        An intentional table is ground at argument i, if in all rules
        defining it, the ith argument in the head is ground.

        :return: a dictionary mapping each table name to the set of argument
                 positions (integers) that are ground for this table.
        """
        return {
            table: set.intersection(
                *({i
                   for i, term in enumerate(r.head.args)
                   if not (isinstance(term, ast.Variable))}
                  for r in group_rule))
            for table, group_rule in itertools.groupby(self.rules,
                                                       key=head_table)}

    def initialize_types(self):
        """initialize table_types

        The type is either bottom or Ground: arguments are the position of the
        argument, the name of the table and an empty context.
        """
        ground_info = self.get_partially_ground_preds()

        def initialize_table(tname, is_ext, arity):
            grounds = ground_info[tname]
            return [
                UFGround(i, tname, None) if i in grounds else UFBot()
                for i in range(arity)]

        self.table_types = {
            tname: initialize_table(tname, is_ext, arity)
            for (tname, (arity, is_ext)) in six.iteritems(self.tables)
            if not is_ext}

    def get_atom_type(self, atom, i):
        """Computes the type of argument at position i of an atom atom

        :param ast.Atom atom: the atom to type
        :param int i: the position
        :return: a type or None if not typable.
        """

        table = atom.table
        # This is a primitive
        if table not in self.tables:
            return None
        # This is an extensible predicate: ground
        if self.tables[table][1]:
            return UFGround(i, table, None)

        # This is an intentional one: get the previous approximation
        if table in self.table_types:
            typ = self.table_types[table]
            return typ[i] if i < len(typ) else None
        return None

    def type_variables(self):
        """Builds a variables type from table types.

        Several types may be found for each variables as they are constrained
        by multiple tables.

        var_types is updated with a map from variable full ids to types.
        """
        constraints = [
            (arg.full_id(), wrap_type(typ_arg, (rule.id, j)))
            for rule in self.rules                  # iterate over rules
            for (j, atom) in enumerate(rule.body)   # iterate over body atoms
            for (i, arg) in enumerate(atom.args)    # iterate over args
            if isinstance(arg, ast.Variable)        # that are variables
            # This is a let: get the type of the ith argument of table.
            for typ_arg in (self.get_atom_type(atom, i),)
            # discard it if we did not find it.
            if typ_arg is not None
        ]
        constraints.sort(key=lambda p: p[0])

        self.var_types = {
            # The true type would be a conjunction. But we do not want to
            # make the type unduly complex and we just keep the "Best"
            # value restriction proposed so far.
            # If we had the size of the constants pools, we could do a better
            # informed choice.
            id: reduce_conj([t for _, t in g])
            for id, g in itertools.groupby(constraints, lambda p: p[0])}

    def type_tables(self):
        """Builds table types from variable types

        Table types are the conjunction of the types found for each rule.
        :returns: next value of table types.
        :rtype: map from string to array of type.
        """
        def type_arg_at(arg, table, i):
            return (
                self.var_types.get(arg.full_id(), top)
                if isinstance(arg, ast.Variable)
                else UFGround(i, table, None))

        return {
            table: [
                reduce_disj({type_arg_at(arg, table, i) for arg in args})
                for i, args in enumerate(zip(*(rule.head.args
                                               for rule in group_rule)))]
            for table, group_rule in itertools.groupby(self.rules,
                                                       key=head_table)}

    def type(self):
        """Type a set of rules.

        :returns: a dictionary from variable names to their type.

        Performs a fixpoint. Each iteration type variables then type rule
        heads. Table types are comparable and the fixpoint is achieved when
        table types do not evolve.

        It is the type structure that guarantees convergence.
        """
        self.initialize_types()
        while True:
            self.type_variables()
            new_table_types = self.type_tables()
            if (new_table_types == self.table_types):
                break
            self.table_types = new_table_types
        return self.var_types
