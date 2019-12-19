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

"""
test_datalog_project
----------------------------------

Tests for `datalog.project` module.
"""

import z3

from octant.common import ast
from octant.datalog import projection
from octant.tests import base


class TestDatalogProject(base.TestCase):

    def test_translate(self):
        fp = z3.Fixedpoint()
        atom1 = ast.Atom('p', [
            ast.NumConstant(2, 'int4'),
            ast.NumConstant(3, 'int4'),
            ast.Variable('X', 'int4')])
        atom2 = ast.Atom('p', [
            ast.NumConstant(2, 'int4'),
            ast.NumConstant(3, 'int4'),
            ast.Variable('Y', 'int4')])
        int4 = z3.BitVecSort(4)
        p = z3.Function('p', int4, int4, int4, z3.BoolSort())
        a0 = z3.BitVecVal(2, int4)
        a1 = z3.BitVecVal(3, int4)
        a2 = z3.Const('X', int4)
        a3 = z3.Const('Y', int4)
        args1 = [a0, a1, a2]
        args2 = [a0, a1, a3]
        project = projection.Projection([], None)
        project.grounded = {'p': (0, 1)}
        project.items = {'p': {}}
        project.relations = {'p': p}
        result = project.translate(fp, atom1, args1)
        self.assertIn((0, 1), project.items['p'])
        self.assertIn((a0, a1), project.items['p'][(0, 1)])
        p0 = project.items['p'][(0, 1)][(a0, a1)]
        self.assertIs(True, z3.is_true(z3.simplify(p0(a2) == result)))
        result2 = project.translate(fp, atom2, args2)
        self.assertIs(True, z3.is_true(z3.simplify(p0(a3) == result2)))

    def test_reconciliate(self):
        fp = z3.Fixedpoint()
        int4 = z3.BitVecSort(4)
        p = z3.Function('p', int4, int4, int4, z3.BoolSort())
        p_0 = z3.Function('p_0', int4, z3.BoolSort())
        p_1 = z3.Function('p_1', int4, z3.BoolSort())
        p_2 = z3.Function('p_2', int4, z3.BoolSort())
        p_3 = z3.Function('p_3', int4, int4, z3.BoolSort())
        for r in [p, p_0, p_1, p_2, p_3]:
            fp.register_relation(r)

        def n(v):
            return z3.BitVecVal(v, int4)

        project = projection.Projection([], None)
        project.relations = {'p': p}
        project.grounded = {'p': (0, 1)}
        project.items = {
            'p': {
                (): {(): p},
                (0, 1): {
                    (n(2), n(2)): p_0, (n(1), n(2)): p_1, (n(1), n(3)): p_2
                },
                (0,): {(n(1),): p_3}}}
        project.reconciliate(fp)
        result = fp.get_rules()
        self.assertEqual(5, len(result))
        for f in result:
            self.assertIs(True, f.is_forall())
            imp = f.children()[0]
            self.assertEqual("=>", imp.decl().name())
            [le, ri] = imp.children()
            self.assertIn(le.decl(), [p_0, p_1, p_2])
            self.assertIn(ri.decl(), [p, p_3])
