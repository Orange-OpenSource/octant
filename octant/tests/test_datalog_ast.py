#    Copyright 2018 Orange
#
# Licensed under the Apache License, Version 2.0 (the 'License'); you may
# not use this file except in compliance with the License. You may obtain
# a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an 'AS IS' BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.

'''
test_datalog_ast
----------------------------------

Tests for `datalog_ast` module.
'''

from octant import datalog_ast as ast
from octant.tests import base


class TestVariable(base.TestCase):
    '''Test AST generation and basic utilities'''

    def test_var(self):
        '''constructor'''
        v = ast.Variable('id')
        self.assertEqual('id', v.id)
        self.assertIsNone(v.label)
        self.assertIsNone(v.type)
        v = ast.Variable('id', label='l', type='string')
        self.assertEqual('l', v.label)
        self.assertEqual('string', v.type)

    def test_variables(self):
        v = ast.Variable('id')
        l = v.variables()
        self.assertEqual(1, len(l))
        self.assertIs(True, 'id' in l)

    def test_renaming(self):
        v = ast.Variable('id')
        v.rename_variables({'a': 'b', 'c': 'd'})
        self.assertEqual('id', v.id)
        v.rename_variables({'a': 'b', 'c': 'd', 'id': 'new'})
        self.assertEqual('new', v.id)

    def test_str(self):
        v = ast.Variable('V', label='l', type='string')
        self.assertEqual('l=V:string', str(v))


class TestConstant(base.TestCase):

    def test_num(self):
        c = ast.NumConstant(5)
        self.assertEqual(5, c.val)
        self.assertEqual('int', c.type)
        self.assertIsNone(c.label)
        self.assertEqual(0, len(c.variables()))
        c = ast.NumConstant(3, type='int4')
        self.assertEqual(3, c.val)
        self.assertEqual('int4', c.type)
        c = ast.NumConstant(2, label='l')
        self.assertEqual('l', c.label)

    def test_string(self):
        c = ast.StringConstant('foo')
        self.assertEqual('foo', c.val)
        self.assertEqual('string', c.type)
        self.assertIsNone(c.label)
        self.assertEqual(0, len(c.variables()))
        c = ast.NumConstant('aaa-bbb', type='id')
        self.assertEqual('aaa-bbb', c.val)
        self.assertEqual('id', c.type)

    def test_bool(self):
        c = ast.BoolConstant(True)
        self.assertIs(True, c.val)
        self.assertEqual('bool', c.type)
        self.assertEqual(0, len(c.variables()))

    def test_ip(self):
        c = ast.IpConstant('192.168.0.1')
        self.assertEqual('192.168.0.1', c.val)
        self.assertEqual('ip_address', c.type)
        self.assertEqual(0, len(c.variables()))


def mk_o():
    v1 = ast.Variable('V1')
    v2 = ast.Variable('V2')
    v3 = ast.Variable('V3')
    n = ast.NumConstant(1)
    o1 = ast.Operation('+', [v1, n])
    o2 = ast.Operation('+', [v1, v2])
    o = ast.Operation('+', [o1, o2, v3])
    return o, v1, v2, v3


class TestOperation(base.TestCase):

    def test_operation(self):
        v = ast.Variable('V')
        n = ast.NumConstant(3)
        o = ast.Operation('+', [v, n])
        self.assertEqual('+', o.operation)
        self.assertEqual([v, n], o.args)

    def test_variables(self):
        o, _, _, _ = mk_o()
        l = o.variables()
        self.assertEqual(3, len(l))
        self.assertIs(True, 'V1' in l)
        self.assertIs(True, 'V2' in l)
        self.assertIs(True, 'V3' in l)

    def test_renaming(self):
        o, v1, v2, v3 = mk_o()
        o.rename_variables({'V1': 'R1', 'V3': 'R3'})
        self.assertEqual(v1.id, 'R1')
        self.assertEqual(v2.id, 'V2')
        self.assertEqual(v3.id, 'R3')


def mk_a():
    o, v1, v2, v3 = mk_o()
    a = ast.Atom('p', [o, v1])
    return a, v1, v2, v3


class TestAtom(base.TestCase):

    def test_atom(self):
        v = ast.Variable('V')
        n = ast.NumConstant(3)
        a = ast.Atom('p', [v, n])
        self.assertEqual('p', a.table)
        self.assertEqual([v, n], a.args)
        self.assertIs(False, a.negated)
        self.assertEqual('p', str(a)[0])
        a = ast.Atom('p', [v, n], negated=True)
        self.assertEqual('p', a.table)
        self.assertIs(True, a.negated)
        self.assertEqual('~p', str(a)[0:2])

    def test_variables(self):
        a, _, _, _ = mk_o()
        l = a.variables()
        self.assertEqual(3, len(l))
        self.assertIs(True, 'V1' in l)
        self.assertIs(True, 'V2' in l)
        self.assertIs(True, 'V3' in l)

    def test_renaming(self):
        a, v1, v2, v3 = mk_a()
        a.rename_variables({'V1': 'R1', 'V2': 'R2'})
        self.assertEqual(v1.id, 'R1')
        self.assertEqual(v2.id, 'R2')
        self.assertEqual(v3.id, 'V3')


def mk_r():
    v1 = ast.Variable('V1')
    v2 = ast.Variable('V2')
    v3 = ast.Variable('V3')
    a1 = ast.Atom('p', [v1, v2])
    a2 = ast.Atom('q', [v1, v3])
    a3 = ast.Atom('r', [v3, v2])
    r = ast.Rule(a1, [a2, a3])
    return r, v1, v2, v3


class TestRule(base.TestCase):

    def test_rule(self):
        r, _, _, _ = mk_r()
        self.assertIsInstance(r.head, ast.Atom)
        self.assertEqual(2, len(r.body))
        self.assertIsInstance(r.body[0], ast.Atom)
        self.assertIsInstance(r.body[1], ast.Atom)

    def test_head_table(self):
        r, _, _, _ = mk_r()
        self.assertEqual('p', r.head_table())

    def test_head_variables(self):
        r, _, _, _ = mk_r()
        l = r.head_variables()
        self.assertEqual(2, len(l))
        self.assertIs(True, 'V1' in l)
        self.assertIs(False, 'V3' in l)

    def test_body_variables(self):
        r, _, _, _ = mk_r()
        l = r.body_variables()
        self.assertEqual(3, len(l))
        self.assertIs(True, 'V1' in l)

    def test_body_tables(self):
        r, _, _, _ = mk_r()
        l = r.body_tables()
        self.assertEqual(2, len(l))
        self.assertIs(True, 'q' in l)
        self.assertIs(True, 'r' in l)

    def test_renaming(self):
        r, v1, v2, v3 = mk_r()
        r.rename_variables({'V1': 'R1', 'V2': 'R2'})
        self.assertEqual(v1.id, 'R1')
        self.assertEqual(v2.id, 'R2')
        self.assertEqual(v3.id, 'V3')
