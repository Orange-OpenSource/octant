# -*- coding: utf-8 -*-

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
import itertools
import six
import z3

from octant.common import ast


def head_table(rule):
    """Table name of the head of a rule"""
    return rule.head.table


def extract_vars_from_plan(unfold_plan):
    return {
        v
        for plan in unfold_plan.plan.values()
        for (_, variables) in plan
        for v in variables}


class Projection(object):
    """Projection column away in the IDB

    The goal of projection is to find predicate columns that are always
    defined. eg.:

        p(1, 2, X) :- Q(X).
        p(2, X, Z) :- R(X, Y).

    Column 1 of p is always defined but not column 2 or 3. We can then
    replace p with p_1 and p_2:

        p_1(2, X) :- Q(X).
        p_2(X, Z) :- R(X, Y).

    We still need a definition of p for cases where it is used without
    specialization:

        p(1, X) :- p_1(X).
        p(2, X) :- p_2(X).

    On the other hand a rule like this one:

        S(X, Y) :- p(1, X, Y).

    should be replaced by:

        S(X, Y) :- p_1(X, Y)

    This phase is done after unfolding and will probably benefit from columns
    made constant by unfolding. But we must use the representation of expanded
    variables in unfold plans.
    """

    def __init__(self, rules, unfold_plan):
        self.rules = rules
        self.rules.sort(key=head_table)
        self.bool = z3.BoolSort()
        if unfold_plan is not None:
            self.unfolded = extract_vars_from_plan(unfold_plan)
        else:
            self.unfolded = set()
        self.grounded = {}
        self.items = {}
        self.count = 0
        self.relations = None

    def compute(self):
        self.grounded = self.get_partially_ground_preds()

    def set_relations(self, relations):
        self.relations = relations
        # We initialize items with the case no var. We need it for queries.
        # We could optimize queries but it may prove rather tough to perform
        # because relation definition should be "done" at this point.
        self.items = {
            table: {(): {(): relations[table]}} for table in self.grounded
        }

    def translate(self, context, atom, args):
        """Translate to specialized atom.

        Given an atom using a predicate to specialize, gives back the
        specialisation predicate and stores the ground parts for
        reconciliation later.
        :param atom: the atom to specialized.
        :returns: a specialized atom (with usually less variables).
        """

        table = atom.table
        if table in self.grounded:
            expanded_pos = self.grounded[table]
            fix = (
                i
                for (i, arg) in enumerate(atom.args)
                if not self.is_variable(arg) and i in expanded_pos)
            fixed_pos = tuple(sorted(fix))
            fixed_args = tuple([args[pos] for pos in fixed_pos])
            pred = self.get_pred(context, table, fixed_pos, fixed_args)

            remain_args = (
                arg
                for (pos, arg) in enumerate(args)
                if pos not in fixed_pos)
            return pred(*remain_args)
        else:
            raise Exception("Bad call")

    def is_specialized(self, table):
        return table in self.grounded

    def get_pred(self, context, table, fixed_pos, fixed_args):
        """Find the specialized predicate.

        :param table: the table that is specialized
        :param fixed_pos: the tuple of positions that are specialized
        :param fixed_args: the values at those positions
        :return: a new predicate unique for those positions and values.
        """
        table_row = self.items.setdefault(table, {})
        row = table_row.setdefault(fixed_pos, {})
        pred = row.get(fixed_args, None)
        if pred is not None:
            return pred
        f = self.relations[table]
        pred_typs = [
            f.domain(pos)
            for pos in range(f.arity())
            if pos not in fixed_pos
        ]
        pred_typs.append(self.bool)
        pred_name = "%s_%d" % (table, self.count)
        self.count += 1
        pred = z3.Function(pred_name, *pred_typs)
        context.register_relation(pred)
        row[fixed_args] = pred
        return pred

    def reconciliate(self, context):
        """Generate specialization predicates

        Translation has generated semi specialized predicates. It is time now
        to define those semi specialized predicates using the fully specialized
        ones.

        :param context: A Z3 context to create the new rules.
        """
        for table, fixed_pos in six.iteritems(self.grounded):
            base_pred = self.relations[table]
            arity = base_pred.arity()
            # For each argument of the base pred we build a variable
            vars = [
                z3.Const("V_{}_{}".format(table, i), base_pred.domain(i))
                for i in range(arity)
            ]
            # All the tuples of ground values associated to our pred.
            row = self.items.get(table, {})
            # from argument position to index in the tuple of ground value.
            idx = {i: p for p, i in enumerate(fixed_pos)}
            # enumerate all the values and associated pred.
            for val1, pred1 in six.iteritems(row.get(fixed_pos, {})):
                # get partial predicates
                for partial_pos, valpred in six.iteritems(row):
                    if partial_pos == fixed_pos:
                        # not this one: it is not partial
                        continue
                    # project our full tuple to what is fixed for this
                    # combination
                    val2 = tuple([val1[idx[pos]] for pos in partial_pos])
                    pred2 = valpred.get(val2, None)
                    if pred2 is None:
                        continue
                    # We found a predicate. We build the rule.
                    #    forall args1. pred2(args2) :- pred1(args1)
                    # args2 is args1 augmented with fixed args from the record
                    # not captured by pred2.
                    args1 = [
                        vars[i]
                        for i in range(arity)
                        if i not in fixed_pos
                    ]
                    args2 = [
                        (val1[idx[i]] if i in fixed_pos else vars[i])
                        for i in range(arity)
                        if i not in partial_pos
                    ]
                    rule = z3.Implies(pred1(*args1), pred2(*args2))
                    if len(args1) > 0:
                        rule = z3.ForAll(args1, rule)
                    context.rule(rule)

    def get_partially_ground_preds(self):
        """Gives back a map of the ground arguments of a table

        An intentional table is ground at argument i, if in all rules
        defining it, the ith argument in the head is ground. This version
        differs from the one in origin because we also take into account
        the variables inlined after unfolding.

        :return: a dictionary mapping each table name to the set of argument
                 positions (integers) that are ground for this table.
        """
        return {
            table: tuple(sorted(set.intersection(
                *({i
                   for i, term in enumerate(r.head.args)
                   if not self.is_variable(term)}
                  for r in group_rule))))
            for table, group_rule in itertools.groupby(self.rules,
                                                       key=head_table)}

    def is_variable(self, term):
        return (
            isinstance(term, ast.Variable) and
            term not in self.unfolded)
