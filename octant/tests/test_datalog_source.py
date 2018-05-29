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
test_octant
----------------------------------

Tests for `octant` module.
"""

from octant import datalog_ast as ast
from octant import datalog_primitives as primitives
from octant import datalog_source as source
from octant.tests import base


class TestDatasource(base.TestCase):
    """Basic test class"""
    def setUp(self):
        self.mysession = {"session": "abc"}
        self.types = primitives.TYPES
        self.content = {
            "T1": (
                lambda s: "T1-" + s.session,
                {"f1": ("t1", lambda s: s + "x1"),
                 "f2": ("t2", lambda s: s + "x2"),
                 "f3": ("t3", lambda s: s + "x3")}),
            "T2": (
                lambda s: "T2-" + s.session,
                {"f4": ("t4", lambda s: s + "x4"),
                 "f5": ("t5", lambda s: s + "x5")})
        }
        super(TestDatasource, self).setUp()

    def test_register(self):
        """Registration"""
        src = source.Datasource(self.types)
        src.register(self.mysession, self.content)
        self.assertIs(True, "T1" in src.datasources)

    def test_primitive(self):
        """Registration"""
        src = source.Datasource(self.types)
        src.register(self.mysession, self.content)
        self.assertIs(True, src.is_primitive(ast.Atom("T1", [])))
        self.assertIs(False, src.is_primitive(ast.Atom("G3", [])))

    def test_types(self):
        src = source.Datasource(self.types)
        src.register(self.mysession, self.content)
        l = src.get_table_types("T1", ["f3", "f2"])
        self.assertEqual(["t3", "t2"], l)
