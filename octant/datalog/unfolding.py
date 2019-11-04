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

from octant.datalog import origin
from octant import primitives


class UnfoldPlan(object):
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

    :param unfold_plan: the complete plan
    :return: All the environments to which one must expand the ground
       variables.
    :rtype: an array of dictionnary.
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
        (spec, vars) = group
        return [
            # pylint: disable=unsubscriptable-object
            {vars[i]: record[index_map.index(pos)]
             for (i, pos) in enumerate(positions)}
            for (table, positions) in spec
            for index_map in (unfold_plan.tables[table],)
            for record in unfold_plan.contents[table]
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
        self.rules.sort(key=origin.head_table)
        self.compiler = compiler
        self.extensible_tables = extensible_tables

    def rule_strategy(self, var_types, rule):
        """Strategy for a rule

        :param var_types: typing of the variables.
        :param ast.Rule rule: the rule on which to compute a strategy
        :return: a plan for the rule which is a list of pairs

                 * a tuple of tables to unfold with the position to unfold
                 * a list of variables solved
        """
        debug = logging.getLogger().debug
        problems = get_to_solve(rule)
        if problems == []:
            return None
        debug("Rule to unfold: %s", rule)
        plan = []
        while problems != []:
            debug("Current problem\n:%s", problems)
            candidate_vars = candidates(problems)
            candidate_types = [
                (t, v)
                for v in candidate_vars
                for t in origin.simplify_to_ground_types(var_types.get(v, []))
            ]
            simple_types = [
                p for p in candidate_types if origin.is_ground(p[0])]
            debug("Simple types for problem\n:%s", simple_types)
            is_simple = True
            if simple_types == []:
                is_simple = False
                simple_types = [
                    p for p in candidate_types if origin.is_disj(p[0])]
                if simple_types == []:
                    debug("Non simple types %s", candidate_types)
                    debug("Plan may be incomplete.")
                    return plan

            def by_occ(p):
                return origin.occurrence(p[0])

            simple_types.sort(key=by_occ)
            simple_types_by_occ = [
                (occ, list(grp))
                for (occ, grp) in itertools.groupby(simple_types, key=by_occ)]
            simple_types_by_occ.sort(reverse=True, key=lambda p: len(p[1]))
            debug("Sorted simple types:\n%s", simple_types_by_occ)
            (_, solved) = simple_types_by_occ[0]
            solved_vars = [pair[1] for pair in solved]
            if is_simple:
                tspec = ((solved[0][0].table, [t.pos for (t, v) in solved]), )
            else:
                skeleton = solved[0][0].args
                tspec = tuple(
                    (a.table, [t.args[i].pos for (t, _) in solved])
                    for (i, a) in enumerate(skeleton))
            plan.append((tspec, solved_vars))
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
        """Enumerates the ground idb tables used

        :param table_spec: a map from tablenames to array of argument positions
                           used.
        :return: a map from tablenames to arrays of records. Records contain
                 compiled values.
        :rtype: dictionnary
        """
        grouped_rules = {
            headname: list(group)
            for (headname, group) in itertools.groupby(
                self.rules, key=origin.head_table)
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

    def strategy(self, var_types):
        """Computes a strategy to unfold.

        :param var_types: the typing of variables computed by origin
        :returns: an unfoldplan made of three parts:

                 * the plan itself as a sequence of rules to unfold
                 * the ground tables that are needed associated with the list
                   of columns used
                 * the contents of IDB tables (programmatically defined) that
                   are ground and used for the expansion.
        """
        plans = [
            (rule.id, plan)
            for rule in self.rules
            for plan in (self.rule_strategy(var_types, rule),)
            if plan is not None
        ]
        table_accesses = {
            (t, p)
            for _, plan in plans
            for (group, _) in plan
            for (t, l) in group
            for p in l
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
        """The main entry point: type, then compute a strategy"""
        origins = origin.Origin(self.rules, self.extensible_tables)
        var_types = origins.type()
        return self.strategy(var_types)
