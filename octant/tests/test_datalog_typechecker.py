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
from octant import datalog_ast as ast
from octant import datalog_parser as parser
from octant import datalog_typechecker as typechecker
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

PROG2 = "p(X) :- X >= 3."
PRIM2 = {}
SRC2 = {}


class TestTypechecker(base.TestCase):
    """Test the typechecker

    The typechecker ensures the coherence of data between sources and Z3
    """

    def test_simple(self):
        prog = parser.wrapped_parse(PROG1)
        tables = typechecker.type_theory(prog, PRIM1, MockSource(SRC1))
        self.assertIn("p", tables)
        self.assertEqual(ast.TypedTable("p", ["t1", "t2"]), tables['p'])
        self.assertIn("q", tables)
        self.assertEqual(ast.TypedTable("q", ["t1"]), tables['q'])
        self.assertIn("r", tables)
        self.assertEqual(ast.TypedTable("r", ["t2"]), tables['r'])

    def test_compare(self):
        prog = parser.wrapped_parse(PROG2)
        tables = typechecker.type_theory(prog, PRIM2, MockSource(SRC2))
        self.assertIn("p", tables)
        self.assertEqual(ast.TypedTable("p", ["int"]), tables['p'])
