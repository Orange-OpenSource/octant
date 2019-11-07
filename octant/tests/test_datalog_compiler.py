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

from octant.common import ast
from octant.common import base as obase
from octant.datalog import compiler
from octant.front import parser
from octant.tests import base


class MockDatasource(object):

    def __init__(self, prims):
        self.prims = prims

    def is_extensible(self, atom):
        return atom.table in self.prims


def pp(str):
    return parser.wrapped_parse(str)


PROG1 = """
    p(X,{0}) :- q(X,{1}), X={2} & X.
    p(X, "b") :- !r(l1=X, l2={1}).
"""

PROG2 = """
    p({0}) :- q({0}).
    p({1}) :- r({1},{2}), s({2}).
    r({3}).
"""

PROG3 = """
    p(X1) :- q(l1=X1, l2=2).
    p(X2) :- q(l1=X2, l3=3).
    p(X3) :- q(l4=X3).
"""

PROG3B = """
    p(X1) :- q(X1, 2, any, any).
    p(X2) :- q(X2, any, 3, any).
    p(X3) :- q(any, any, any, X3).
"""


def distinct(l):
    return len(l) < 2 or (lambda r: not l[0] in r and distinct(r))(l[1:])


class Any(ast.Variable):

    def __init__(self):
        super(Any, self).__init__('_')

    # We rely heavily on the fact that == is asymetric here
    def __eq__(self, other):
        return isinstance(other, ast.Variable)


class TestCompiler(base.TestCase):

    def test_constants(self):
        ast.Rule.rule_counter = 0
        rules = pp(PROG1.format('a', 'b', 'c'))
        constants = {
            'a': ast.StringConstant('n'),
            'b': ast.NumConstant(2),
            'c': ast.NumConstant(0)}
        comp = compiler.Z3Compiler(rules, constants, None)
        comp.substitute_constants()
        ast.Rule.rule_counter = 0
        expected = pp(PROG1.format('"n"', '2', '0'))
        self.assertEqual(expected, rules)

    def test_constants_unknown(self):
        rules = pp(PROG1.format('a', 'b', 'd'))
        constants = {
            'a': ast.StringConstant('n'),
            'b': ast.NumConstant(2),
            'c': ast.NumConstant(0)}
        comp = compiler.Z3Compiler(rules, constants, None)
        self.assertRaises(obase.Z3NotWellFormed, comp.substitute_constants)

    def test_flatten(self):
        ast.Rule.rule_counter = 0
        rules = pp(PROG3)
        comp = compiler.Z3Compiler(rules, None, MockDatasource(['q']))
        comp.find_base_relations()
        ast.Rule.rule_counter = 0
        rules2 = pp(PROG3B)
        # uses compiler to inject custom variable Any as a replacement
        # for constant any.
        comp2 = compiler.Z3Compiler(rules2, {'any': Any()}, None)
        comp2.substitute_constants()
        # This is a hack. We had to reset the rule_counter
        self.assertEqual(rules2, rules)
        # check that all the variables are fresh
        vars = [
            rules[0].body[0].args[2].id,
            rules[0].body[0].args[3].id,
            rules[1].body[0].args[1].id,
            rules[1].body[0].args[3].id,
            rules[2].body[0].args[0].id,
            rules[2].body[0].args[1].id,
            rules[2].body[0].args[2].id
        ]
        self.assertIs(True, distinct(vars))
