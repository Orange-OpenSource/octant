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
test_datalog_theory
----------------------------------

Tests for `datalog_theory` module.
"""

import mock

from octant.common import base as obase
from octant.datalog import theory
from octant.datalog import z3_result as z3r
from octant.front import parser
from octant.tests import base


def pp(text):
    return parser.wrapped_parse(text)


def standard_cfg(mock_cfg):
    mock_cfg.doc = False
    mock_cfg.smt2 = None
    mock_cfg.csv = False
    mock_cfg.time = True
    mock_cfg.query = ["p(X)"]
    mock_cfg.theory = ["file"]
    mock_cfg.restore = None
    mock_cfg.save = None
    mock_cfg.debug = False
    mock_cfg.smt2 = None
    mock_cfg.filesource = []


PROG1 = """
    p(X) :- X = 3:int4.
    q(X) :- X = 3:int4.
    q(X) :- X = 3:int4 & 6:int4.
    r(X) :- X = 2:int4, !X = 3:int4.
"""


def mocked_register(ds):
    content = {
        "q": (
            lambda s: [422, 568],
            {"a": ("int", lambda s: s - 1),
                "b": ("t2", lambda s: s)})
    }
    ds.register({}, content)


class TestDatalogTheory(base.TestCase):
    """Test datalog_theory"""

    @mock.patch("octant.source.openstack_source.register")
    @mock.patch("octant.source.skydive_source.register")
    @mock.patch("oslo_config.cfg.CONF")
    def test_build_theory_simple(self, mock_cfg, src1, src2):
        standard_cfg(mock_cfg)
        theo = theory.Z3Theory(pp(PROG1))
        theo.build_theory()
        r = theo.query(parser.parse_atom("p(X)"))
        self.assertEqual((['X'], [z3r.Cube({0: 3}, 1)]), r)
        r = theo.query(parser.parse_atom("q(X)"))
        self.assertEqual(
            (['X'], [z3r.Cube({0: 2}, 1), z3r.Cube({0: 3}, 1)]),
            r)

    @mock.patch("octant.source.openstack_source.register")
    @mock.patch("octant.source.skydive_source.register")
    @mock.patch("oslo_config.cfg.CONF")
    def test_query_bad(self, mock_cfg, src1, src2):
        standard_cfg(mock_cfg)
        theo = theory.Z3Theory(pp(PROG1))
        theo.build_theory()
        self.assertRaises(
            obase.Z3NotWellFormed,
            lambda: theo.query(parser.parse_atom("h(X)")))
        self.assertRaises(
            obase.Z3NotWellFormed,
            lambda: theo.query(parser.parse_atom("p(X,Y)")))

    @mock.patch("octant.source.openstack_source.register")
    @mock.patch("octant.source.skydive_source.register")
    @mock.patch("oslo_config.cfg.CONF")
    def test_build_bad(self, mock_cfg, src1, src2):
        standard_cfg(mock_cfg)
        theo = theory.Z3Theory(pp("p(X:ukw_type)."))
        self.assertRaises(obase.Z3TypeError, theo.build_theory)

    @mock.patch("octant.source.openstack_source.register")
    @mock.patch("octant.source.skydive_source.register")
    @mock.patch("oslo_config.cfg.CONF")
    def test_simple_result(self, mock_cfg, src1, src2):
        standard_cfg(mock_cfg)
        theo = theory.Z3Theory(pp("p(). q() :- !p()."))
        theo.build_theory()
        self.assertEqual(([], True), theo.query(parser.parse_atom("p()")))
        self.assertEqual(([], False), theo.query(parser.parse_atom("q()")))

    @mock.patch("octant.source.openstack_source.register", new=mocked_register)
    @mock.patch("octant.source.skydive_source.register")
    @mock.patch("oslo_config.cfg.CONF")
    def test_with_source(self, mock_cfg, src1):
        standard_cfg(mock_cfg)
        theo = theory.Z3Theory(pp("p(X) :- q(a=X)."))
        theo.build_theory()
        self.assertEqual(
            (['X'], [z3r.Cube({0: 421}, 1), z3r.Cube({0: 567}, 1)]),
            theo.query(parser.parse_atom("p(X)")))
