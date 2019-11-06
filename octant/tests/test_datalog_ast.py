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


'''
test_datalog_ast
----------------------------------

Tests for `datalog_ast` module.
'''

from octant.common import ast
from octant.tests import base


class TestVariable(base.TestCase):
    '''Test AST generation and basic utilities'''

    def test_var(self):
        '''constructor'''
        v = ast.Variable('id')
        self.assertEqual('id', v.id)
        self.assertIsNone(v.type)
        v = ast.Variable('id', dtype='string')
        self.assertEqual('string', v.type)

    def test_variables(self):
        v = ast.Variable('id')
        lvars = v.variables()
        self.assertEqual(1, len(lvars))
        lvars = [x[0] for x in lvars]
        self.assertIs(True, 'id' in lvars)

    def test_renaming(self):
        v1 = ast.Variable('id')
        v2 = ast.Variable('id')
        v3 = ast.Variable('id')
        self.assertEqual(v1, v2)
        v1.pin_variables(1)
        v2.pin_variables(1)
        v3.pin_variables(2)
        self.assertEqual(v1, v2)
        self.assertIs(False, v1 == v3)

    def test_str(self):
        v = ast.Variable('V', dtype='string')
        self.assertEqual('V:string', str(v))

    def test_eq(self):
        self.assertIs(True, ast.Variable('V') == ast.Variable('V'))
        self.assertIs(False, ast.Variable('V') == ast.Variable('W'))


class TestConstant(base.TestCase):

    def test_num(self):
        c = ast.NumConstant(5)
        self.assertEqual(5, c.val)
        self.assertEqual('int', c.type)
        self.assertEqual(0, len(c.variables()))
        c = ast.NumConstant(3, dtype='int4')
        self.assertEqual(3, c.val)
        self.assertEqual('int4', c.type)

    def test_num_eq(self):
        self.assertIs(True, ast.NumConstant(2) == ast.NumConstant(2))
        self.assertIs(False, ast.NumConstant(3) == ast.NumConstant(2))
        self.assertIs(False,
                      ast.NumConstant(2) == ast.NumConstant(2, dtype='int4'))

    def test_string(self):
        c = ast.StringConstant('foo')
        self.assertEqual('foo', c.val)
        self.assertEqual('string', c.type)
        self.assertEqual(0, len(c.variables()))
        c = ast.NumConstant('aaa-bbb', dtype='id')
        self.assertEqual('aaa-bbb', c.val)
        self.assertEqual('id', c.type)

    def test_string_eq(self):
        self.assertIs(True, ast.StringConstant('a') == ast.StringConstant('a'))
        self.assertIs(
            False, ast.StringConstant('b') == ast.StringConstant('a'))
        self.assertIs(
            False,
            ast.StringConstant('a') == ast.StringConstant('a', dtype='id'))

    def test_bool(self):
        c = ast.BoolConstant(True)
        self.assertIs(True, c.val)
        self.assertEqual('bool', c.type)
        self.assertEqual(0, len(c.variables()))

    def test_bool_eq(self):
        self.assertIs(True, ast.BoolConstant(True) == ast.BoolConstant(True))
        self.assertIs(False, ast.BoolConstant(False) == ast.BoolConstant(True))

    def test_ip(self):
        c = ast.IpConstant('192.168.0.1')
        self.assertEqual('192.168.0.1', c.val)
        self.assertEqual('ip_address', c.type)
        self.assertEqual(0, len(c.variables()))

    def test_ip_eq(self):
        self.assertIs(
            True,
            ast.IpConstant('192.168.0.1') == ast.IpConstant('192.168.0.1'))


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

    def test_eq(self):
        v = ast.Variable('V')
        n = ast.NumConstant(3)
        self.assertIs(
            True, ast.Operation('+', [v, n]) == ast.Operation('+', [v, n]))
        self.assertIs(
            False, ast.Operation('+', [v, n]) == ast.Operation('+', [n, n]))

    def test_variables(self):
        o, _, _, _ = mk_o()
        lvars = o.variables()
        self.assertEqual(3, len(lvars))
        lvars = [x[0] for x in lvars]
        self.assertIs(True, 'V1' in lvars)
        self.assertIs(True, 'V2' in lvars)
        self.assertIs(True, 'V3' in lvars)


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
        lvars = a.variables()
        self.assertEqual(3, len(lvars))
        lvars = [x[0] for x in lvars]
        self.assertIs(True, 'V1' in lvars)
        self.assertIs(True, 'V2' in lvars)
        self.assertIs(True, 'V3' in lvars)

    def test_eq(self):
        v = ast.Variable('V')
        n = ast.NumConstant(3)
        self.assertIs(True, ast.Atom('p', [v]) == ast.Atom('p', [v]))
        self.assertIs(
            False, ast.Atom('p', [v], negated=True) == ast.Atom('p', [v]))
        self.assertIs(
            False, ast.Atom('p', [v]) == ast.Atom('p', [n]))


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
        lvars = r.head_variables()
        self.assertEqual(2, len(lvars))
        lvars = [x[0] for x in lvars]
        self.assertIs(True, 'V1' in lvars)
        self.assertIs(False, 'V3' in lvars)

    def test_body_variables(self):
        r, _, _, _ = mk_r()
        lvars = r.body_variables()
        self.assertEqual(3, len(lvars))
        lvars = [x[0] for x in lvars]
        self.assertIs(True, 'V1' in lvars)

    def test_body_tables(self):
        r, _, _, _ = mk_r()
        ltables = r.body_tables()
        self.assertEqual(2, len(ltables))
        self.assertIs(True, 'q' in ltables)
        self.assertIs(True, 'r' in ltables)

    def test_pinning(self):
        r, v1, v2, v3 = mk_r()
        self.assertEqual(v1.rule_id, r.id)
        self.assertEqual(v2.rule_id, r.id)
        self.assertEqual(v3.rule_id, r.id)

    def test_eq(self):
        a1 = ast.Atom('p', [])
        a2 = ast.Atom('q', [])
        a3 = ast.Atom('r', [])
        self.assertIs(True, ast.Rule(a1, [a2, a3]) == ast.Rule(a1, [a2, a3]))
        self.assertIs(False, ast.Rule(a2, [a2, a3]) == ast.Rule(a1, [a2, a3]))
        self.assertIs(False, ast.Rule(a1, [a1, a3]) == ast.Rule(a1, [a2, a3]))
