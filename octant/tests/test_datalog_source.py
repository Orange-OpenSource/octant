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

import mock

from octant import base as obase
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


BACKUP_FILE = (
    "T1,f3,f2\r\n"
    "T1,T1-S1-R1x3,T1-S1-R1x2\r\n"
    "T1,T1-S1-R2x3,T1-S1-R2x2\r\n"
    "T1,T1-S1-R3x3,T1-S1-R3x2\r\n")


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
        self.assertIs(True, self.src.is_extensible(ast.Atom("T1", [])))
        self.assertIs(False, self.src.is_extensible(ast.Atom("G3", [])))

    def test_types(self):
        ltypes = self.src.get_table_types("T1", ["f3", "f2"])
        self.assertEqual(["t3", "t2"], ltypes)

    def test_retrieve(self):
        buffer = []

        def mk_relation(l):
            buffer.append(" ".join(l))
        self.src.retrieve_table("T1", ["f3", "f2"], mk_relation)
        expected = [
            "z3T1-S0-R1x3 z3T1-S0-R1x2", "z3T1-S0-R2x3 z3T1-S0-R2x2",
            "z3T1-S0-R3x3 z3T1-S0-R3x2"]
        self.assertEqual(expected, buffer)

    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.datalog_source.open")
    def test_save(self, mock_open, mock_conf):
        mock_conf.save = "file"
        mock_conf.restore = None
        mock.mock_open(mock=mock_open)
        with self.src:
            self.src.retrieve_table("T1", ["f3", "f2"], lambda x: ())
        mock_open.assert_called_once_with('file', mode='w')
        mock_open.write.has_calls([
            mock.call('T1,f3,f2\r\n'),
            mock.call('T1,T1-S0-R1x3,T1-S0-R1x2\r\n'),
            mock.call('T1,T1-S0-R2x3,T1-S0-R2x2\r\n'),
            mock.call('T1,T1-S0-R3x3,T1-S0-R3x2\r\n')
        ])

    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.datalog_source.open")
    def test_restore(self, mock_open, mock_conf):
        mock_conf.save = None
        mock_conf.restore = "file"
        mock.mock_open(mock=mock_open, read_data=BACKUP_FILE)
        # Patch the mock_open file to support iteration.
        mock_open.return_value.__iter__ = lambda x: iter(x.readline, '')
        buffer = []

        def mk_relation(l):
            buffer.append(" ".join(l))
        with self.src:
            self.src.retrieve_table("T1", ["f3", "f2"], mk_relation)
        # Note that we have renamed S0 in S1 in the backup file.
        expected = [
            "z3T1-S1-R1x3 z3T1-S1-R1x2", "z3T1-S1-R2x3 z3T1-S1-R2x2",
            "z3T1-S1-R3x3 z3T1-S1-R3x2"]
        self.assertEqual(expected, buffer)

    @mock.patch("oslo_config.cfg.CONF")
    def test_use_cache(self, mock_conf):
        mock_conf.restore = None
        self.assertIs(False, self.src.use_cache())
        mock_conf.restore = "file"
        self.assertIs(True, self.src.use_cache())

    def test_retrieve_failures(self):
        def fail1():
            self.src.retrieve_table("T4", ["f3", "f2"], lambda x: ())

        def fail2():
            self.src.retrieve_table("T1", ["f5", "f2"], lambda x: ())

        self.assertRaises(obase.Z3TypeError, fail1)
        self.assertRaises(obase.Z3TypeError, fail2)

    def test_types_failures(self):
        def fail1():
            self.src.get_table_types("T4", ["f3", "f2"])

        def fail2():
            self.src.get_table_types("T1", ["f5", "f2"])

        self.assertRaises(obase.Z3TypeError, fail1)
        self.assertRaises(obase.Z3TypeError, fail2)
