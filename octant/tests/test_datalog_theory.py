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

from contextlib import contextmanager
import mock
import six
import sys

from octant import datalog_compiler as compiler
from octant import datalog_parser as parser
from octant import datalog_theory as theory
from octant import datalog_typechecker as typechecker
from octant.tests import base
from octant import z3_result as z3r


def pp(text):
    return parser.wrapped_parse(text)


@contextmanager
def capture_stdout():
    old = sys.stdout
    try:
        sys.stdout = six.StringIO()
        yield sys.stdout
    finally:
        sys.stdout = old


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


def standard_cfg(mock_cfg):
    mock_cfg.pretty = True
    mock_cfg.csv = False
    mock_cfg.time = True
    mock_cfg.query = ["p(X)"]
    mock_cfg.theory = ["file"]
    mock_cfg.restore = None
    mock_cfg.save = None
    mock_cfg.debug = False


class TestDatalogTheory(base.TestCase):
    """Test datalog_theory"""

    @mock.patch("octant.source_openstack.register")
    @mock.patch("octant.source_skydive.register")
    def test_build_theory_simple(self, src1, src2):
        theo = theory.Z3Theory(pp(PROG1))
        theo.build_theory()
        r = theo.query("p(X)")
        self.assertEqual((['X'], [z3r.Cube({0: 3})]), r)
        r = theo.query("q(X)")
        self.assertEqual((['X'], [z3r.Cube({0: 2}), z3r.Cube({0: 3})]), r)

    @mock.patch("octant.source_openstack.register")
    @mock.patch("octant.source_skydive.register")
    def test_query_bad(self, src1, src2):
        theo = theory.Z3Theory(pp(PROG1))
        theo.build_theory()
        self.assertRaises(compiler.Z3NotWellFormed, lambda: theo.query("h(X)"))
        self.assertRaises(
            compiler.Z3NotWellFormed, lambda: theo.query("p(X,Y)"))

    @mock.patch("octant.source_openstack.register")
    @mock.patch("octant.source_skydive.register")
    def test_build_bad(self, src1, src2):
        theo = theory.Z3Theory(pp("p(X:ukw_type)."))
        self.assertRaises(typechecker.Z3TypeError, theo.build_theory)

    @mock.patch("octant.source_openstack.register")
    @mock.patch("octant.source_skydive.register")
    def test_simple_result(self, src1, src2):
        theo = theory.Z3Theory(pp("p(). q() :- !p()."))
        theo.build_theory()
        self.assertEqual(([], True), theo.query("p()"))
        self.assertEqual(([], False), theo.query("q()"))

    @mock.patch("octant.source_openstack.register", new=mocked_register)
    @mock.patch("octant.source_skydive.register")
    def test_with_source(self, src1):
        theo = theory.Z3Theory(pp("p(X) :- q(a=X)."))
        theo.build_theory()
        self.assertEqual(
            (['X'], [z3r.Cube({0: 421}), z3r.Cube({0: 567})]),
            theo.query("p(X)"))

    def test_print_result_pretty(self):
        with capture_stdout() as out:
            theory.print_result(
                "query", ["VarX", "Y"],
                [z3r.Cube({0: 2134, 1: 3}), z3r.Cube({0: 4, 1: 572})],
                3.5, True)
        result = out.getvalue()
        self.assertIs(True, "2134" in result)
        self.assertIs(True, "572" in result)
        self.assertIs(True, "VarX" in result)
        with capture_stdout() as out:
            theory.print_result(
                "query", [], True, None, True)
        result = out.getvalue()
        self.assertIs(True, "True" in result)

    def test_print_result_standard(self):
        with capture_stdout() as out:
            theory.print_result(
                "query", ["VarX", "Y"], [[2134, 3], [4, 572]], 3.5, False)
        result = out.getvalue()
        self.assertIs(True, "2134" in result)
        self.assertIs(True, "572" in result)
        with capture_stdout() as out:
            theory.print_result(
                "query", [], True, None, False)
        result = out.getvalue()
        self.assertIs(True, "True" in result)

    @mock.patch("octant.datalog_theory.sys.exit")
    @mock.patch("octant.source_openstack.register")
    @mock.patch("octant.source_skydive.register")
    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.datalog_parser.open")
    def test_main(self, mock_open, mock_cfg, mock_src1, mock_src2, mock_exit):
        standard_cfg(mock_cfg)
        mock.mock_open(mock=mock_open, read_data="p(3452).")
        with capture_stdout() as out:
            theory.main()
        result = out.getvalue()
        self.assertIs(True, "3452" in result)

    @mock.patch("octant.datalog_theory.sys.exit")
    @mock.patch("octant.source_openstack.register")
    @mock.patch("octant.source_skydive.register")
    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.datalog_parser.open")
    def test_main_no_time(self, mock_open, mock_cfg, mock_src1, mock_src2,
                          mock_exit):
        standard_cfg(mock_cfg)
        mock_cfg.time = False
        mock_cfg.query = ["p(X)", "q(X)"]
        mock.mock_open(mock=mock_open, read_data="p(3452). q(421).")
        with capture_stdout() as out:
            theory.main()
        result = out.getvalue()
        self.assertIs(True, "3452" in result)
        self.assertIs(True, "421" in result)

    @mock.patch("octant.datalog_theory.sys.exit")
    @mock.patch("octant.source_openstack.register")
    @mock.patch("octant.source_skydive.register")
    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.datalog_parser.open")
    def test_main_incompat(
            self, mock_open, mock_cfg, mock_src1,
            mock_src2, mock_exit):
        standard_cfg(mock_cfg)
        mock_cfg.csv = True
        mock.mock_open(mock=mock_open, read_data="p(3452).")
        with capture_stdout():
            theory.main()
        mock_exit.assert_called_once_with(1)

    @mock.patch("octant.datalog_theory.sys.exit")
    @mock.patch("octant.source_openstack.register")
    @mock.patch("octant.source_skydive.register")
    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.datalog_parser.open")
    def test_main_parse_error(
            self, mock_open, mock_cfg, mock_src1,
            mock_src2, mock_exit):
        standard_cfg(mock_cfg)
        mock.mock_open(mock=mock_open, read_data="p(.")
        with capture_stdout():
            theory.main()
        # Weird case. Because we do not really exit, we proceed too far.
        # exit is called twice.
        mock_exit.assert_called_with(1)

    @mock.patch("octant.datalog_theory.sys.exit")
    @mock.patch("octant.source_openstack.register")
    @mock.patch("octant.source_skydive.register")
    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.datalog_parser.open")
    def test_main_type_error(
            self, mock_open, mock_cfg, mock_src1,
            mock_src2, mock_exit):
        standard_cfg(mock_cfg)
        mock.mock_open(mock=mock_open, read_data="p(3452:ukw_type).")
        with capture_stdout():
            theory.main()
        mock_exit.assert_called_once_with(1)

    @mock.patch("octant.datalog_theory.sys.exit")
    @mock.patch("octant.source_openstack.register")
    @mock.patch("octant.source_skydive.register")
    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.datalog_parser.open")
    def test_main_parse_error_query(
            self, mock_open, mock_cfg, mock_src1,
            mock_src2, mock_exit):
        standard_cfg(mock_cfg)
        mock_cfg.query = ["p("]
        mock.mock_open(mock=mock_open, read_data="p().")
        with capture_stdout():
            theory.main()
        mock_exit.assert_called_once_with(1)
