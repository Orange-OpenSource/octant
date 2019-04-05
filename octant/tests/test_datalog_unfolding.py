# -*- coding: utf-8 -*-

# Copyright 2018 Orange
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may
# not use this file except in compliance with the License. You may obtain
# a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.

"""Tests for datalog_unfolding module"""

from octant import datalog_ast as ast
from octant import datalog_parser as parser
from octant import datalog_unfolding as unfolding
from octant.tests import base


prog0 = """
    t(X, 1) :- p(X).
    t(X,2) :- p(X).
    s(X, 1) :- p(X).
    s(X, Y) :- q(X,Y).
    """

prog1 = """
    t(X, Y) :- s(X1, X2, Y2), p(X1), q(X2, Y2), r(X2),
               r(Y2), X1 = X & X2, Y2 = Y & 15.
    """

prog2 = """
    t(X, Y) :- p(X1), s(X2), X1 = X & X2.
    s(X) :- p(X).
    s(X) :- q(X).
    """


class TestUnfolding(base.TestCase):
    """Tests of utility functions"""

    def test_simplify_to_ground_types(self):
        t1 = unfolding.UFGround(1, "t", None)
        t2 = unfolding.UFGround(1, "t", None)
        t3 = unfolding.UFDisj((t1, t2))
        t4 = unfolding.UFConj((
            t1, unfolding.UFConj((t2, t1)),
            unfolding.UFBot(), t3))
        expected = [t1, t2, t1, t3]
        self.assertEqual(
            expected,
            unfolding.simplify_to_ground_types(t4))

    def test_len_occ(self):
        self.assertEqual(0, unfolding.len_occ(None))
        self.assertEqual(1, unfolding.len_occ(('m', None)))
        self.assertEqual(2, unfolding.len_occ(('n', ('m', None))))

    def test_weight_type(self):
        t1 = unfolding.UFGround(1, "t", ('m', None))
        t2 = unfolding.UFBot()
        t3 = unfolding.UFDisj((t1, t2))
        t4 = unfolding.UFConj((t1, t2, t1))
        self.assertEqual((0, 1), unfolding.weight_type(t1))
        self.assertEqual((2, 0), unfolding.weight_type(t2))
        self.assertEqual((1, 2), unfolding.weight_type(t3))
        self.assertEqual((1, 3), unfolding.weight_type(t4))

    def test_wrap_type(self):
        mark = 'm'
        t1 = unfolding.UFGround(1, "t", None)
        t2 = unfolding.UFGround(1, "t", ('n', None))
        t3 = unfolding.UFDisj((t1, t2))
        t4 = unfolding.UFConj((
            t1, unfolding.UFConj((t2, t1)),
            unfolding.UFBot(), t3))
        e1 = unfolding.UFGround(1, "t", (mark, None))
        e2 = unfolding.UFGround(1, "t", (mark, ('n', None)))
        e3 = unfolding.UFDisj((e1, e2))
        e4 = unfolding.UFConj((
            e1, unfolding.UFConj((e2, e1)),
            unfolding.UFBot(), e3))
        self.assertEqual(e4, unfolding.wrap_type(t4, mark))

    def test_reduce_disj(self):
        t1 = unfolding.UFGround(1, "t", None)
        t2 = unfolding.UFGround(2, "u", None)
        t3 = unfolding.UFBot()
        t4 = unfolding.UFDisj((t1, t2))
        t5 = unfolding.UFDisj((t1, t3))
        t6 = unfolding.UFDisj((t1, unfolding.top))
        result = unfolding.reduce_disj([t4, t1, t5])
        self.assertIsInstance(result, unfolding.UFDisj)
        self.assertEqual(3, len(result.args))
        self.assertEqual(unfolding.top, unfolding.reduce_disj([t4, t1, t6]))

    def test_reduce_conj(self):
        t1 = unfolding.UFGround(1, "t", None)
        t2 = unfolding.UFGround(2, "u", None)
        t3 = unfolding.UFGround(2, "v", None)
        t4 = unfolding.UFDisj((t1, t2))
        t5 = unfolding.UFDisj((t1, t3))
        self.assertEqual(
            unfolding.UFConj((t1, t2)),
            unfolding.reduce_conj([t1, t2, t4, t5]))
        self.assertEqual(t4, unfolding.reduce_conj([t4, t5]))

    def test_get_to_solve(self):
        prog = parser.wrapped_parse("t(X) :- p(X,Y), X = Y & 1, q(X), X < 10.")
        rule = prog[0]
        id = rule.id
        vars = {('X', id), ('Y', id)}
        # Only the first is to solve. There is only one variable in the
        # equality.
        expected = [(1, vars)]
        self.assertEqual(expected, unfolding.get_to_solve(prog[0]))

    def test_candidates(self):
        v1, v2, v3 = (('X', 0), ('Y', 0), ('Z', 0))
        problems = [(1, {v1, v2}), (2, {v1, v3}), (3, {v1})]
        self.assertEqual({v1, v2, v3}, unfolding.candidates(problems))

    def test_environ_from_plan(self):
        plan = unfolding.UnfoldPlan(
            plan=[
                (1, [((('u', [2]),), ['x'])]),
                (3, [((('t', [0, 3]),), ['x', 'y']),
                     ((('u', [2]),), ['z'])])],
            tables={'t': [0, 3], 'u': [2]},
            contents={
                't': [[0, 1], [2, 3]],
                'u': [[4], [5]]
            }
        )
        result = unfolding.environ_from_plan(plan)
        expected1 = {(('x', 4),), (('x', 5),)}
        expected3 = {
            (('x', 0), ('y', 1), ('z', 4)), (('x', 0), ('y', 1), ('z', 5)),
            (('x', 2), ('y', 3), ('z', 4)), (('x', 2), ('y', 3), ('z', 5))}
        self.assertEqual({1, 3}, set(result.keys()))

        def normalize(list):
            return {tuple(sorted(record.items())) for record in list}
        self.assertEqual(expected3, normalize(result[3]))
        self.assertEqual(expected1, normalize(result[1]))

    def test_unfolding(self):
        prog = "t(X) :- p(X,Y), X = Y & 1.\ns(X) :- t(X), 2 = X & 2."
        rules = parser.wrapped_parse(prog)
        extensible = {"p": ["int", "int"]}
        unfold = unfolding.Unfolding(rules, extensible, (lambda t: t))
        self.assertEqual((2, True), unfold.tables["p"])
        self.assertEqual((1, False), unfold.tables["t"])

    def test_partially_ground(self):
        rules = parser.wrapped_parse(prog0)
        unfold = unfolding.Unfolding(rules, {}, (lambda t: t))
        result = unfold.get_partially_ground_preds()
        self.assertEqual({'s': set(), 't': set([1])}, result)

    def test_initialize_types_and_get_atom_types(self):
        rules = parser.wrapped_parse(prog0)
        atom_t = rules[0].head
        atom_z = ast.Atom('z', [])
        external = {'q': ['int', 'int'], 'p': ['int']}
        unfold = unfolding.Unfolding(rules, external, (lambda t: t))
        unfold.initialize_types()
        self.assertEqual(
            [unfolding.UFBot(), unfolding.UFGround(1, "t", None)],
            unfold.table_types['t'])
        self.assertEqual(
            unfolding.UFBot(),
            unfold.get_atom_type(atom_t, 0))
        self.assertEqual(None, unfold.get_atom_type(atom_t, 3))
        self.assertEqual(None, unfold.get_atom_type(atom_z, 0))

    def test_type_variables(self):
        rules = parser.wrapped_parse(prog0)
        vars = [rules[rid].head.args[pos].full_id()
                for (rid, pos) in [(1, 0), (3, 0), (3, 1)]]
        external = {'q': ['int', 'int'], 'p': ['int']}
        unfold = unfolding.Unfolding(rules, external, (lambda t: t))
        unfold.initialize_types()
        unfold.type_variables()
        typs = [unfold.var_types[v] for v in vars]
        self.assertEqual(['p', 'q', 'q'], [t.table for t in typs])
        self.assertEqual([0, 0, 1], [t.pos for t in typs])
        occs = [t.occurrence for t in typs]
        self.assertEqual(occs[1], occs[2])
        self.assertEqual(False, occs[0] == occs[1])

    def test_type_tables(self):
        rules = parser.wrapped_parse(prog0)
        external = {'q': ['int', 'int'], 'p': ['int']}
        unfold = unfolding.Unfolding(rules, external, (lambda t: t))
        unfold.initialize_types()
        unfold.type_variables()
        result = unfold.type_tables()
        typ_s0 = result['s'][0]
        self.assertIsInstance(typ_s0, unfolding.UFDisj)
        self.assertEqual(['p', 'q'], sorted([t.table for t in typ_s0.args]))
        self.assertEqual(
            ['q', 's'],
            sorted([t.table for t in result['s'][1].args]))

    def test_type(self):
        rules = parser.wrapped_parse(prog0)
        external = {'q': ['int', 'int'], 'p': ['int']}
        unfold = unfolding.Unfolding(rules, external, (lambda t: t))
        unfold.type()
        result = unfold.table_types
        typ_s0 = result['s'][0]
        self.assertIsInstance(typ_s0, unfolding.UFDisj)
        self.assertEqual(['p', 'q'], sorted([t.table for t in typ_s0.args]))
        self.assertEqual(
            ['q', 's'],
            sorted([t.table for t in result['s'][1].args]))

    def test_strategy_1(self):
        rules = parser.wrapped_parse(prog1)
        external = {'q': ['int', 'int'], 'p': ['int'], 'r': ['int']}
        unfold = unfolding.Unfolding(rules, external, (lambda t: t))
        unfold.type()
        result = unfold.rule_strategy(rules[0])
        filtered = [(t, sorted(pos)) for (((t, pos),), _) in result]
        self.assertEqual([('q', [0, 1]), ('p', [0])], filtered)

    def test_strategy_2(self):
        rules = parser.wrapped_parse(prog2)
        rule = rules[0]
        external = {'q': ['int'], 'p': ['int']}
        unfold = unfolding.Unfolding(rules, external, (lambda t: t))
        unfold.type()
        result = unfold.rule_strategy(rule)
        filtered = [
            sorted([(t, sorted(pos)) for (t, pos) in plan],
                   key=lambda p: p[0])
            for (plan, _) in result]
        print(filtered)
        self.assertEqual([[('p', [0])], [('p', [0]), ('q', [0])]], filtered)
