# -*- coding: utf-8 -*-

#  Copyright 2018 Orange
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
test_datalog_source
----------------------------------

Tests for `datalog_source` module.
"""

from octant import datalog_ast as ast
from octant import datalog_primitives as primitives
from octant import datalog_source as source
from octant.tests import base


class T(primitives.Z3Type):
    """Fake Z3 type"""

    def to_z3(self, val):
        return "z3" + val

    def to_os(self, val):
        return val[2:]

    def marshall(self, val):
        return val

    def unmarshall(self, val):
        return val


class TestDatasource(base.TestCase):
    """Basic test class"""
    def setUp(self):
        self.mysession = {"session": "S0"}
        self.types = {n: T(n, 'Z3') for n in ["t1", "t2", "t3", "t4", "t5"]}
        self.content = {
            "T1": (
                lambda s: ["T1-{}-{}".format(s['session'], r)
                           for r in ["R1", "R2", "R3"]],
                {"f1": ("t1", lambda s: s + "x1"),
                 "f2": ("t2", lambda s: s + "x2"),
                 "f3": ("t3", lambda s: s + "x3")}),
            "T2": (
                lambda s: ["T2-" + s['session'] + "-R"],
                {"f4": ("t4", lambda s: s + "x4"),
                 "f5": ("t5", lambda s: s + "x5")})
        }
        self.src = source.Datasource(self.types)
        self.src.register(self.mysession, self.content)
        super(TestDatasource, self).setUp()

    def test_register(self):
        """Registration"""
        self.assertIs(True, "T1" in self.src.datasources)

    def test_primitive(self):
        """Registration"""
        self.assertIs(True, self.src.is_primitive(ast.Atom("T1", [])))
        self.assertIs(False, self.src.is_primitive(ast.Atom("G3", [])))

    def test_types(self):
        l = self.src.get_table_types("T1", ["f3", "f2"])
        self.assertEqual(["t3", "t2"], l)

    def test_retrieve(self):
        buffer = []

        def mk_relation(l):
            buffer.append(" ".join(l))
        self.src.retrieve_table("T1", ["f3", "f2"], mk_relation)
        expected = [
            "z3T1-S0-R1x3 z3T1-S0-R1x2", "z3T1-S0-R2x3 z3T1-S0-R2x2",
            "z3T1-S0-R3x3 z3T1-S0-R3x2"]
        self.assertEqual(expected, buffer)
