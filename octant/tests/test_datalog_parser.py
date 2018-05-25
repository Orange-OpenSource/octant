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
test_datalog_compiler
----------------------------------

Tests for `datalog_compiler` module which preprocess Datalog rules.
'''

from octant import datalog_ast as ast
from octant import datalog_parser as parser
from octant.tests import base


class TestLexer(base.TestCase):

    def test_ident(self):
        lex = parser.lexer
        for s in ['aaa', 'aAa', 'aa_aa_34']:
            lex.input(s)
            t = lex.token()
            self.assertEqual('IDENT', t.type)
            self.assertEqual(s, t.value)
            self.assertIs(None, lex.token())

    def test_var(self):
        lex = parser.lexer
        for s in ['Aaa', 'AaaBbb', 'A_34']:
            lex.input(s)
            t = lex.token()
            self.assertEqual('VAR', t.type)
            self.assertEqual(s, t.value)
            self.assertIs(None, lex.token())

    def test_number(self):
        lex = parser.lexer
        for n in [123, 1456234789, -234, 0]:
            lex.input(str(n))
            t = lex.token()
            self.assertEqual('NUMBER', t.type)
            self.assertEqual(n, t.value)
            self.assertIs(None, lex.token())

    def test_ip(self):
        lex = parser.lexer
        for s in ['192.168.122.1', '255.255.0.0']:
            lex.input(s)
            t = lex.token()
            self.assertEqual('IP', t.type)
            self.assertEqual(s, t.value)
            self.assertIs(None, lex.token())

    def test_string(self):
        lex = parser.lexer
        for s, r in [('"192.168.122.1"', '192.168.122.1'),
                     ('"aaa"', 'aaa'),
                     ('"aa\\"bb"', 'aa"bb'),
                     ('"aa\\\\bb"', 'aa\\bb')]:
            lex.input(s)
            t = lex.token()
            self.assertEqual('STRING', t.type)
            self.assertEqual(r, t.value)
            self.assertIs(None, lex.token())

    def test_token(self):
        lex = parser.lexer
        for s, r in [
            (':-', 'ENTAIL'), ('(', 'OPAR'), ('!', 'BANG'),
            (')', 'CPAR'), (':', 'COLON'), (',', 'COMMA'),
            ('=', 'EQUAL'), ('.', 'DOT'), ('~', 'TILDE'),
            ('&', 'AMPERSAND'), ('|', 'BAR'), ('<', 'LT'),
            ('<=', 'LE'), ('>', 'GT'), ('>=', 'GE')
        ]:
            lex.input(s)
            t = lex.token()
            self.assertEqual(r, t.type)
            self.assertIs(None, lex.token())


def pp(s):
    return parser.wrapped_parse(s)


class TestParser(base.TestCase):

    def test_parser_simple_head(self):
        r = pp("p().")
        self.assertEqual(
            [ast.Rule(ast.Atom('p', []), [])],
            r)

    def test_parser_two_rules(self):
        r = pp("p(). q().")
        self.assertEqual(
            [ast.Rule(ast.Atom('p', []), []),
             ast.Rule(ast.Atom('q', []), [])],
            r)

    def test_parser_simple_body(self):
        r = pp("p() :- q().")
        self.assertEqual(
            [ast.Rule(ast.Atom('p', []), [ast.Atom('q', [])])],
            r)

    def test_parser_two_body(self):
        r = pp("p() :- q(), r().")
        self.assertEqual(
            [ast.Rule(ast.Atom('p', []),
                      [ast.Atom('q', []), ast.Atom('r', [])])],
            r)

    def test_parser_negated_atom(self):
        r = pp("p() :- !q().")
        self.assertEqual(
            [ast.Rule(ast.Atom('p', []), [ast.Atom('q', [], negated=True)])],
            r)

    def test_expr_one(self):
        r = pp("p(1).")
        self.assertEqual(
            [ast.Rule(ast.Atom('p', [ast.NumConstant(1)]), [])],
            r)

    def test_expr_multi(self):
        r = pp("p(1, 2, 3).")
        self.assertEqual(
            [ast.Rule(ast.Atom('p', [ast.NumConstant(i) for i in [1, 2, 3]]),
                      [])],
            r)

    def test_expr_string(self):
        r = pp('p("aaa").')
        self.assertEqual(
            [ast.Rule(ast.Atom('p', [ast.StringConstant("aaa")]), [])],
            r)

    def test_expr_ip(self):
        r = pp("p(192.168.0.1).")
        self.assertEqual(
            [ast.Rule(ast.Atom('p', [ast.IpConstant('192.168.0.1')]), [])],
            r)

    def test_expr_constant(self):
        r = pp("p(c).")
        self.assertEqual(
            [ast.Rule(ast.Atom('p', [ast.Constant('c')]), [])],
            r)

    def test_expr_var(self):
        r = pp("p(X).")
        self.assertEqual(
            [ast.Rule(ast.Atom('p', [ast.Variable('X')]), [])],
            r)

    def test_expr_label(self):
        r = pp("p(X) :- q(l1=X, l2=3).")
        self.assertEqual(
            [ast.Rule(ast.Atom('p', [ast.Variable('X')]),
                      [ast.Atom('q', [ast.Variable('X'), ast.NumConstant(3)],
                                labels=['l1', 'l2'])])],
            r)

    def test_comparison(self):
        r = pp("p(X) :- X=2, X>1, X<3, X<=4, X>=0.")
        self.assertEqual(
            [ast.Rule(ast.Atom('p', [ast.Variable('X')]),
                      [ast.Atom('=', [ast.Variable('X'), ast.NumConstant(2)]),
                       ast.Atom('>', [ast.Variable('X'), ast.NumConstant(1)]),
                       ast.Atom('<', [ast.Variable('X'), ast.NumConstant(3)]),
                       ast.Atom('<=', [ast.Variable('X'), ast.NumConstant(4)]),
                       ast.Atom('>=', [ast.Variable('X'), ast.NumConstant(0)])
                       ])],
            r)

    def test_operation(self):
        r = pp("p(X) :- X=1&2, X=3|4, X=~5.")
        self.assertEqual(
            [ast.Rule(ast.Atom('p', [ast.Variable('X')]), [
                ast.Atom('=', [
                    ast.Variable('X'),
                    ast.Operation('&', [ast.NumConstant(1),
                                        ast.NumConstant(2)])]),
                ast.Atom('=', [
                    ast.Variable('X'),
                    ast.Operation('|', [ast.NumConstant(3),
                                        ast.NumConstant(4)])]),
                ast.Atom('=', [
                    ast.Variable('X'),
                    ast.Operation('~', [ast.NumConstant(5)])])
                ])],
            r
        )
