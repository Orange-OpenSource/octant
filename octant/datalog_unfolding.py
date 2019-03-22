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
import logging
import six

from octant import datalog_ast as ast
from octant import datalog_primitives as primitives


class UFBot:
    """Bottom type corresponds to no information at all"""
    def __eq__(self, other):
        return isinstance(other, self.__class__)

    def __hash__(self):
        return 1


class UFTop:
    """Top type means any value"""
    def __eq__(self, other):
        return isinstance(other, self.__class__)

    def __hash__(self):
        return 2


class UFGround:
    """Coerced to be a ground value of parameter at a given position

    .. py:attribute:: pos:

        position of the argument in the table (integer starting at 0)

    .. py:attribute:: table:

        table defining the ground term (str)

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


class UFConj:
    """Conjunctions of types

    It represent a conjunct of constraints on the origin. It is usually
    simplified at some point as one of the origins.
    """
    def __init__(self, args):
        self.args = args

    def __eq__(self, other):
        return isinstance(other, self.__class__) and other.args == self.args

    def __hash__(self):
        return hash(self.args)


class UFDisj:
    """Disjunctions of types

    The values of the element may come from either origins.
    """

    def __init__(self, args):
        self.args = args

    def __eq__(self, other):
        return isinstance(other, self.__class__) and other.args == self.args

    def __hash__(self):
        return hash(self.args)


class UnfoldPlan:
    """Result of unfolding as a plan

    .. py:attribute:: plan
        the full plan to follow for unfolding. For each rule that needs
        simplification the plan associate to the id of the rule, a list of
        simplification actions. An action is a list of elementary actions
        taking place at the same time. An elementary action specifies a table
        and a column in that table and the variable that will receive the
        content of this table.

    .. py: attribute:: tables
        a dictionary with keys the tables to retrieve and values the list of
        column positions to retrieve

    .. py: attribute:: contents
        a dictionnary from table to retrieve to list of actual content tuples
        the columns given are as specified by the tables field.
    """
    def __init__(self, plan, tables, contents):
        self.plan = plan
        self.contents = contents
        self.tables = tables

    def __eq__(self, other):
        return (
            isinstance(other, self.__class__) and other.plan == self.plan and
            other.tables == self.tables and other.contents == self.contents)

    def __hash__(self):
        return hash((self.plan, self.tables, self.contents))


top = UFTop()
bot = UFBot()


def is_ground(t):
    return isinstance(t, UFGround)


def simplify_to_ground_types(t):
    """Gives back simple ground or disjunction"""
    if is_ground(t) or isinstance(t, UFDisj):
        return [t]
    if isinstance(t, UFConj):
        return [g for a in t.args for g in simplify_to_ground_types(a)]
    return []


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
        return UFGround(typ.pos, typ.table, (mark, typ.occurrence))
    if isinstance(typ, UFDisj):
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
        for x in (e.args if isinstance(e, UFDisj) else (e,))}
    if len(flat) == 1:
        return flat.pop()
    print("FLAT IS " + str(flat))
    print(top in flat)
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
    :returns: a conjunct with more than one type or what was considered as the
        best type
    """
    flat = [
        x
        for e in l
        for x in (e.args if isinstance(e, UFConj) else (e,))]
    flat.sort(key=weight_type)
    if len(flat) > 1 and is_ground(flat[0]):
        return UFConj(tuple(filter(is_ground, flat)))
    return flat[0]


def get_to_solve(rule):
    """Gets the position where there is a predicate to simplify.

    A primitive predicate with more than one variable will not be handled
    correctly by the difference of cube domain. It must be simplified to
    reach only one free variable.
    """
    return [
        (pos, vlist)
        for pos, atom in enumerate(rule.body)
        for vlist in (atom.variables(),)
        if primitives.is_primitive(atom) and len(vlist) > 1]


def candidates(problems):
    """Get the set of candidate variables."""
    return {var for (_, vl) in problems for var in vl}


def environ_from_plan(unfold_plan):
    """Takes a plan and compile it to a dictionnary of envs for rules

    :param unfold_plan:
    :return: a dictionnary.
    """
    def merge_env(envs):
        result = []
        for tuple in envs:
            cell = {}
            for env in tuple:
                cell.update(env)
            result.append(cell)
        return result

    def expand(group):
        table = group[0][0]
        index_map = unfold_plan.tables[table]
        contents = unfold_plan.contents[table]
        return [
            {v: record[index_map.index(pos)] for (_, pos, v) in group}
            for record in contents
        ]
    env = {
        rule_id: merge_env(itertools.product(*(
            expand(group)
            for group in plan)
        ))
        for rule_id, plan in unfold_plan.plan
    }
    logging.getLogger().debug("Environment for unfolding:\n%s" % env)
    return env


class Unfolding(object):

    def __init__(self, rules, extensible_tables, compiler):
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
        self.compiler = compiler
        self.populate_tables(extensible_tables)

    def populate_tables(self, extensible_tables):
        for table, args in six.iteritems(extensible_tables):
            self.tables[table] = (len(args), True)
        for table, group_rule in itertools.groupby(self.rules, key=head_table):
            self.tables[table] = (len(list(group_rule)[0].head.args), False)

    def get_partially_ground_preds(self):
        """Gives back a map of the ground arguments of a table

        An intentional table is ground at argument i, if in all rules
        defining it, the ith argument in the head is ground.
        :returns: a map from table names to set of argument positions
          (integers) that are ground for this table.
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
            if is_ext:
                return [UFGround(i, tname, None) for i in range(arity)]
            else:
                grounds = ground_info[tname]
                return [
                    UFGround(i, tname, None) if i in grounds else UFBot()
                    for i in range(arity)]

        self.table_types = {
            tname: initialize_table(tname, is_ext, arity)
            for (tname, (arity, is_ext)) in six.iteritems(self.tables)}

    def get_atom_type(self, atom, i):
        table = atom.table
        # This is a primitive
        if table not in self.tables:
            return None
        # This is an extensible predicate: ground
        if self.tables[table][1]:
            return UFGround(i, table, None)
        # This is an intentional one: get the previous approximation
        if table in self.table_types:
            return self.table_types.get(table, [])[i]
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

    def debug_fixpoint(self):
        """Prints out the results of computations."""
        for var, typ in six.iteritems(self.var_types):
            print("=" * 20)
            print("Variable {} in {}".format(var[0], var[1]))
            print("-" * 20)
            print(str(typ))
        for tab, typ in six.iteritems(self.table_types):
            print("=" * 20)
            print("Table {}".format(tab))
            print("-" * 20)
            for (i, t) in enumerate(typ):
                print("{}: {}".format(i, t))

    def type(self):
        self.initialize_types()
        while True:
            self.type_variables()
            new_table_types = self.type_tables()
            if (new_table_types == self.table_types):
                break
            self.table_types = new_table_types

    def rule_strategy(self, rule):
        debug = logging.getLogger().debug
        problems = get_to_solve(rule)
        if problems == []:
            return None
        debug("*" * 60)
        debug("Rule to unfold: %s", rule)
        debug("*" * 60)
        plan = []
        while problems != []:
            debug("Current problem\n:%s", problems)
            candidate_vars = candidates(problems)
            candidate_types = [
                (t, v)
                for v in candidate_vars
                for t in simplify_to_ground_types(
                    self.var_types.get(v, []))
            ]
            simple_types = [p for p in candidate_types if is_ground(p[0])]
            debug("Simple types for problem\n:%s", simple_types)
            if simple_types == []:
                raise Exception('Cannot handle non simple yet.')

            def by_occ(p):
                return p[0].occurrence

            simple_types.sort(key=by_occ)
            simple_types_by_occ = [
                (occ, list(grp))
                for (occ, grp) in itertools.groupby(simple_types, key=by_occ)]
            simple_types_by_occ.sort(reverse=True, key=lambda p: len(p[1]))
            debug("Sorted simple types:\n%s", simple_types_by_occ)
            (_, solved) = simple_types_by_occ[0]
            plan.append([(t.table, t.pos, v) for (t, v) in solved])
            solved_vars = [v[1] for v in solved]
            debug("Solved variables:\n%s", solved_vars)
            # We expect less problems to solve and at least simpler ones.
            problems = [
                (pos, vlist_reduced)
                for (pos, vlist) in problems
                for vlist_reduced in (
                    [v for v in vlist if v not in solved_vars], )
                if len(vlist_reduced) > 1
            ]
            debug('-' * 80)
        return plan

    def idb_extract(self, table_spec):
        """Enumerates the ground idb tables used"""
        grouped_rules = {
            headname: list(group)
            for (headname, group) in itertools.groupby(
                self.rules, key=head_table)
        }
        return {
            table: [
                [self.compiler(args[pos]) for pos in poslist]
                for rule in group
                for args in (rule.head.args,)
            ]
            for (table, poslist) in six.iteritems(table_spec)
            if table in grouped_rules
            for group in (grouped_rules[table],)
        }

    def strategy(self):
        plans = [
            (rule.id, plan)
            for rule in self.rules
            for plan in (self.rule_strategy(rule),)
            if plan is not None
        ]
        table_accesses = {
            (t, p)
            for _, plan in plans
            for group in plan
            for (t, p, _) in group
        }
        tables = {
            table: [pos for _, pos in group]
            for (table, group) in itertools.groupby(
                sorted(list(table_accesses), key=lambda p: p[0]),
                key=lambda p: p[0])
        }
        idb_tables = self.idb_extract(tables)
        logger = logging.getLogger()
        logger.debug("Unfolding plans:\n%s" % plans)
        logger.debug("Tables used by unfolding: %s" % tables)
        logger.debug("IDB for unfolding: %s" % idb_tables)
        return UnfoldPlan(plans, tables, idb_tables)

    def proceed(self):
        self.type()
        return self.strategy()
