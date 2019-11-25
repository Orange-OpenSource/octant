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
import collections
import itertools
import six

from octant.common import ast

#: Inclusion tree. Sons of a node are subsets of the root of the node.
#: .. py:attribute:: root
#:    The set represented by this tree node
#: .. py:attribute: children
#     Nodes representing subsets of the root set
InclusionTree = collections.namedtuple('InclusionTree', ['root', 'children'])


def inclusion_tree(elt):
    return InclusionTree(elt, [])


def add_inclusion(elt, tree):
    """Adds an element to an inclusion tree

    :param elt: element to add
    :param tree: the inclusion tree to complete
    :returns: True iff elt is a subset of tree.root
    """
    if elt <= tree.root:
        return False
    if all(not add_inclusion(elt, child) for child in tree.children):
        tree.children.append(inclusion_tree(elt))
    return True


def head_table(rule):
    """Table name of the head of a rule"""
    return rule.head.table


def extract_vars_from_plan(unfold_plan):
    return (
        v
        for (_, plan) in unfold_plan.plan
        for (_, variables) in plan
        for v in variables)


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
        self.unfolded = extract_vars_from_plan(unfold_plan)
        self.grounded = {}

    def compute(self):
        grounded = self.get_partially_ground_preds()
        partials = {}
        for rule in self.rules:
            for atom in rule.body:
                partial = {
                    i
                    for i in grounded.get(atom.table, [])
                    if self.is_variable(atom.args[i])}
                if len(partial) == 0:
                    continue
                partials.setdefault(atom.table, set()).add(
                    frozenset(partial))

        for table, gdvars in six.iteritems(grounded):
            base = inclusion_tree(gdvars)
            subs = list(partials.get(table, set()))
            subs.sort(key=lambda e: len(e), reverse=True)
            for partial in subs:
                add_inclusion(partial, base)
            self.grounded[table] = base

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
            table: set.intersection(
                *({i
                   for i, term in enumerate(r.head.args)
                   if not self.is_variable(term)}
                  for r in group_rule))
            for table, group_rule in itertools.groupby(self.rules,
                                                       key=head_table)}

    def is_variable(self, term):
        return (
            isinstance(term, ast.Variable) and
            term.full_id() not in self.unfolded)
