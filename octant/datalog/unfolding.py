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

from collections import namedtuple
import itertools
import logging
import six
import z3

from octant.common import ast
from octant.datalog import operations
from octant.datalog import origin
from octant.datalog import z3_result


loc_type = namedtuple("loc_type", ["type", "occ"])
candidate = namedtuple("candidate", ["type", "occ", "var"])
typvar = namedtuple("typvar", ["type", "var"])


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

    .. py: attribute:: idb

        a dictionnary from table to retrieve to list of actual content tuples
        the columns given are as specified by the tables field.
    """
    def __init__(self, plan, idb):
        self.plan = plan
        self.idb = idb

    def __eq__(self, other):
        return (
            isinstance(other, self.__class__) and other.plan == self.plan and
            other.idb == self.idb)

    def __str__(self):
        return (
            "PLAN: %s\nCONTENTS: %s\n" %
            (self.plan, str(self.idb)[:512]))

    def __hash__(self):
        return hash((self.plan, self.idb))


def get_to_solve(rule):
    """Gets the position where there is a predicate to simplify.

    A primitive predicate with more than one variable will not be handled
    correctly by the difference of cube domain. It must be simplified to
    reach only one free variable.

    :returns: a list of triples made of position of atom to simplify, the
        variable list associated to the atom and the size of the list expected.
    """
    vars = {
        var
        for atom in rule.body
        for var in atom.args
        if isinstance(var, ast.Variable) and var.type == 'id'
    }
    id_problems = [([var], 0) for var in vars]
    strength_problems = [
        (vlist, 1)
        for atom in rule.body
        for vlist in (atom.variables(),)
        if operations.is_primitive(atom) and len(vlist) > 1]
    if len(strength_problems) > 0:
        return id_problems + strength_problems
    else:
        return id_problems


def candidates(problems):
    """Get the set of candidate variables.

    :param problems: a list of pairs position of atom to simplify and the
        variable list associated to the atom.
    :returns: a set of variables.
    """
    return {var for (vl, _) in problems for var in vl}


def plan_to_program(unfold_plan, context, datasource, relations, rules):
    """Extracts the specialization environment

    Transform a plan into a program and executes the program to extract
    a list of potential environments for each rule.

    :param unfold_plan: the plan to execute
    :param context: a compilation context for Z3
    :param datasource: the datasource for constant compilation
    :param relations: A dictionary from table name to z3 function
    :param rules: all the rules
    :returns: a dictionary for each rule id the list of potential
        environments. Each environment associates full id of expanded
        variable to their value.
    """
    debug = logging.getLogger().debug
    z3bool = z3.BoolSort()

    def mk_type(typ):
        return datasource.types[typ].type()

    def mk_pred(name, avars):
        param_types = [mk_type(var.type) for var in avars]
        param_types.append(z3bool)
        relation = z3.Function(name, *param_types)
        context.register_relation(relation)
        return relation

    def comp_constant(expr):
        return datasource.types[expr.type].to_z3(expr.val)

    result = {}
    idb = unfold_plan.idb
    needed = {}

    for rule in rules:
        rid = rule.id
        plan = unfold_plan.plan.get(rid, None)
        if plan is None:
            continue
        debug("Generating rules for %s" % rule)
        used_vars = list({var for (_, varlist) in plan for var in varlist})
        used_vars.sort(key=lambda v: v.full_id())
        name = "_env_%d" % rid
        main_pred = mk_pred(name, used_vars)
        main_pred_body = []
        for (i, (subplan, subvars)) in enumerate(plan):
            # TODO(pc) may be we can avoid this predicate if there is only one
            # level. But we need to take care of the variable order.
            # Defereed for later optimization.
            subname = "_env_%d_%d" % (rid, i)
            subpred = mk_pred(subname, subvars)
            main_pred_body.append((subpred, subvars))
            for (table, positions) in subplan:
                if isinstance(table, origin.GroundHead):
                    rid = table.rid
                    rule = next(rule for rule in rules if rule.id == rid)
                    head_args = rule.head.args
                    args = [comp_constant(head_args[pos]) for pos in positions]
                    rule = subpred(*args)
                else:
                    if table in idb:
                        pred_table = needed.get(table, None)
                        if pred_table is None:
                            back_table = relations[table]
                            argtyps = [
                                back_table.domain(i)
                                for i in range(back_table.arity())]
                            argtyps.append(z3bool)
                            gname = "_ground_%s" % table
                            pred_table = z3.Function(gname, *argtyps)
                            context.register_relation(pred_table)
                            # Now we have a declared name for it.
                            needed[table] = pred_table
                            # We inject the ground idb content.
                            for row in idb[table]:
                                context.rule(pred_table(*row))
                    else:
                        pred_table = relations[table]
                    pred_args = [
                        z3.Const("V%d" % i, pred_table.domain(i))
                        for i in range(pred_table.arity())]
                    head_args = [pred_args[pos] for pos in positions]
                    rule = z3.ForAll(
                        pred_args,
                        z3.Implies(
                            pred_table(*pred_args), subpred(*head_args)))
                debug("  Subrule: %s " % rule)
                context.rule(rule)
        env = {
            var: z3.Const(var.id, mk_type(var.type)) for var in used_vars
        }
        row = [env[var] for var in used_vars]
        head = main_pred(*row)
        body = [
            pred(*[env[var] for var in predvars])
            for (pred, predvars) in main_pred_body
        ]
        debug("-" * 80)
        mainrule = z3.ForAll(row, z3.Implies(z3.And(body), head))
        debug(mainrule)
        context.rule(mainrule)
        query = z3.Exists(row, head)
        context.query(query)
        raw_answer = context.get_answer()
        used_varsid = [var.full_id() for var in used_vars]
        records = z3_result.z3_to_array_simple(raw_answer, used_varsid)
        debug("Found %d records" % len(records))
        result[rid] = records
        debug("=" * 80)
    return result


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
        all_vars = rule.body_variables()
        all_types = {
            v: [loc_type(t, origin.occurrence(t))
                for t in origin.simplify_to_ground_types(
                    var_types.get(v.full_id(), []))
                ]
            for v in all_vars
        }
        debug("Rule to unfold: %s", rule)
        plan = []
        while problems != []:
            debug("Current problem\n:%s", problems)
            candidate_vars = candidates(problems)
            candidate_types = [
                candidate(pair.type, pair.occ, v)
                for v in candidate_vars
                for pair in all_types.get(v, [])]
            simple_types = [
                p for p in candidate_types if origin.is_ground(p.type)]
            debug("Simple types for problem\n:%s", simple_types)
            is_simple = True
            if simple_types == []:
                is_simple = False
                simple_types = [
                    p for p in candidate_types if origin.is_disj(p.type)]
                if simple_types == []:
                    debug("Non simple types %s", candidate_types)
                    debug("Plan may be incomplete.")
                    return plan
            simple_occ = list(map(lambda p: p.occ, simple_types))
            simple_occ.sort()
            simple_occ_count = [
                (occ, len(list(grp)))
                for (occ, grp) in itertools.groupby(simple_occ)
            ]
            simple_occ_count.sort(reverse=True, key=lambda p: p[1])
            debug("Sorted simple occs:\n%s", simple_occ_count)
            occ = simple_occ_count[0][0]
            solved = [
                typvar(t, v)
                for (v, l) in six.iteritems(all_types)
                for (t, o) in l
                if o == occ
            ]
            solved_vars = [pair.var for pair in solved]
            if is_simple:
                typ = solved[0].type
                if typ.occurrence[1] is None:
                    # get the index of the atom
                    pos = typ.occurrence[0][1]
                    atom = rule.body[pos]
                    if all(isinstance(a, ast.Variable) for a in atom.args):
                        rule.body[pos] = None
                tspec = ((typ.table, [t.pos for (t, v) in solved]),)
            else:
                skeleton = solved[0][0].args
                tspec = tuple(
                    (a.table, [t.args[i].pos for (t, _) in solved])
                    for (i, a) in enumerate(skeleton))
            plan.append((tspec, solved_vars))
            debug("Solved variables:\n%s", solved_vars)
            # We expect less problems to solve and at least simpler ones.
            problems = [
                (vlist_reduced, size)
                for (vlist, size) in problems
                for vlist_reduced in (
                    [v for v in vlist if v not in solved_vars], )
                if len(vlist_reduced) > size
            ]
            debug('-' * 80)
        return plan

    def idb_extract(self):
        """Enumerates the ground idb tables

        :return: a map from tablenames to arrays of records. Records contain
                 compiled values.
        :rtype: dictionnary
        """
        grouped_rules = {
            headname: list(group)
            for (headname, group) in itertools.groupby(
                self.rules, key=origin.head_table)
        }
        idb = {
            table: [
                [self.compiler(arg) for arg in args]
                for rule in group
                for args in (rule.head.args,)
                if all(not isinstance(arg, ast.Variable) for arg in args)
            ]
            for table, group in grouped_rules.items()
        }
        return idb

    def strategy(self, var_types):
        """Computes a strategy to unfold.

        :param var_types: the typing of variables computed by origin
        :returns: an unfoldplan made of two parts:

                 * the plan itself as a sequence of rules to unfold
                 * the contents of IDB tables (programmatically defined) that
                   are ground and used for the expansion.
        """
        plans = {
            rule.id: plan
            for rule in self.rules
            for plan in (self.rule_strategy(var_types, rule),)
            if plan is not None
        }
        idb_tables = self.idb_extract()
        logger = logging.getLogger()
        logger.debug("Unfolding plans:\n%s" % plans)
        logger.debug("IDB for unfolding: %s" % idb_tables)
        return UnfoldPlan(plans, idb_tables)

    def proceed(self):
        """The main entry point: type, then compute a strategy"""
        origins = origin.Origin(self.rules, self.extensible_tables)
        var_types = origins.type()
        return self.strategy(var_types)
