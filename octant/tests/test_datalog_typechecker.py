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
test_datalog_typechecker
----------------------------------

Tests for `datalog_typecheker` module.
"""

from octant import base as obase
from octant.datalog import typechecker
from octant import parser
from octant.tests import base


class MockSource(object):

    def __init__(self, table_types):
        self.table_types = table_types

    def get_table_types(self, table, fields):
        field_types = self.table_types[table]
        return [field_types[field] for field in fields]


PROG1 = "p(X,Y) :- q(X), r(Y)."
PRIM1 = {"q": ["q1"], "r": ["r1"]}
SRC1 = {"q": {"q1": "t1"}, "r": {"r1": "t2"}}

PROG2 = "p(X) :- X >= 3. q(Y) :- 3 >= Y."

PROG3 = """
   p(X) :- X = Y & Y, Y >= 3: int4.
   q(Z) :- 4 = Z & Z.
   """

PROG4 = "p(X) :- X:int4 >= 3."

PROG5 = "p(X) :- X = Y & 2, Y >= 3: int4."

PROG6 = "p(X) :- 3 = 2 & (X & 6)."

PROG7 = "p(X, Y) :- Y = (X & 2: int4) :int."

PROG8 = "p(X) :- X <= 3. q(Y) :- p(Y, Y)."

PROG9 = "p(X:int, X: int4)."

PROG10 = "p(3). p(4:int4)."


class TestTypechecker(base.TestCase):
    """Test the typechecker

    The typechecker ensures the coherence of data between sources and Z3
    """

    def test_simple(self):
        prog = parser.wrapped_parse(PROG1)
        tables = typechecker.type_theory(prog, PRIM1, MockSource(SRC1))
        self.assertIn("p", tables)
        self.assertEqual(["t1", "t2"], tables['p'])
        self.assertIn("q", tables)
        self.assertEqual(["t1"], tables['q'])
        self.assertIn("r", tables)
        self.assertEqual(["t2"], tables['r'])

    def test_compare(self):
        prog = parser.wrapped_parse(PROG2)
        tables = typechecker.type_theory(prog, {}, MockSource({}))
        self.assertIn("p", tables)
        self.assertEqual(["int"], tables['p'])
        self.assertIn("q", tables)
        self.assertEqual(["int"], tables['q'])

    def test_operation(self):
        prog = parser.wrapped_parse(PROG3)
        tables = typechecker.type_theory(prog, {}, MockSource({}))
        self.assertIn("p", tables)
        self.assertEqual(["int4"], tables['p'])
        self.assertIn("q", tables)
        self.assertEqual(["int"], tables['q'])

    def test_bad_compare(self):
        prog = parser.wrapped_parse(PROG4)
        self.assertRaises(
            obase.Z3TypeError,
            lambda: typechecker.type_theory(prog, {}, MockSource({})))

    def test_bad_operation(self):
        prog = parser.wrapped_parse(PROG5)
        self.assertRaises(
            obase.Z3TypeError,
            lambda: typechecker.type_theory(prog, {}, MockSource({})))

    def test_sub_operation(self):
        prog = parser.wrapped_parse(PROG6)
        tables = typechecker.type_theory(prog, {}, MockSource({}))
        self.assertIn("p", tables)
        self.assertEqual(["int"], tables['p'])

    def test_clash_on_expr(self):
        prog = parser.wrapped_parse(PROG7)
        self.assertRaises(
            obase.Z3TypeError,
            lambda: typechecker.type_theory(prog, {}, MockSource({})))

    def test_arity_check(self):
        prog = parser.wrapped_parse(PROG8)
        self.assertRaises(
            obase.Z3TypeError,
            lambda: typechecker.type_theory(prog, {}, MockSource({})))

    def test_constraint_check(self):
        prog = parser.wrapped_parse(PROG9)
        self.assertRaises(
            obase.Z3TypeError,
            lambda: typechecker.type_theory(prog, {}, MockSource({})))

    def test_atom_column(self):
        prog = parser.wrapped_parse(PROG10)
        self.assertRaises(
            obase.Z3TypeError,
            lambda: typechecker.type_theory(prog, {}, MockSource({})))
