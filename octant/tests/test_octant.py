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

import mock

from octant.datalog import z3_result as z3r
from octant.front import main as octant
from octant.tests import base


def standard_cfg(mock_cfg):
    mock_cfg.pretty = True
    mock_cfg.csv = False
    mock_cfg.time = True
    mock_cfg.query = ["p(X)"]
    mock_cfg.theory = ["file"]
    mock_cfg.restore = None
    mock_cfg.save = None
    mock_cfg.debug = False
    mock_cfg.smt2 = None
    mock_cfg.filesource = []


class TestDatalogTheory(base.TestCase):

    def test_print_result_pretty(self):
        with base.capture_stdout() as out:
            octant.print_result(
                "query", ["VarX", "Y"],
                [z3r.Cube({0: 2134, 1: 3}), z3r.Cube({0: 4, 1: 572})],
                3.5, True)
        result = out.getvalue()
        self.assertIs(True, "2134" in result)
        self.assertIs(True, "572" in result)
        self.assertIs(True, "VarX" in result)
        with base.capture_stdout() as out:
            octant.print_result(
                "query", [], True, None, True)
        result = out.getvalue()
        self.assertIs(True, "True" in result)

    def test_print_result_standard(self):
        with base.capture_stdout() as out:
            octant.print_result(
                "query", ["VarX", "Y"], [[2134, 3], [4, 572]], 3.5, False)
        result = out.getvalue()
        self.assertIs(True, "2134" in result)
        self.assertIs(True, "572" in result)
        with base.capture_stdout() as out:
            octant.print_result(
                "query", [], True, None, False)
        result = out.getvalue()
        self.assertIs(True, "True" in result)

    @mock.patch("octant.front.main.sys.exit")
    @mock.patch("octant.source.openstack_source.register")
    @mock.patch("octant.source.skydive_source.register")
    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.front.parser.open")
    def test_main(self, mock_open, mock_cfg, mock_src1, mock_src2, mock_exit):
        standard_cfg(mock_cfg)
        mock.mock_open(mock=mock_open, read_data="p(3452).")
        with base.capture_stdout() as out:
            octant.main()
        result = out.getvalue()
        print(result)
        self.assertIs(True, "3452" in result)

    @mock.patch("octant.front.main.sys.exit")
    @mock.patch("octant.source.openstack_source.register")
    @mock.patch("octant.source.skydive_source.register")
    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.front.parser.open")
    def test_main_no_time(self, mock_open, mock_cfg, mock_src1, mock_src2,
                          mock_exit):
        standard_cfg(mock_cfg)
        mock_cfg.time = False
        mock_cfg.query = ["p(X)", "q(X)"]
        mock.mock_open(mock=mock_open, read_data="p(3452). q(421).")
        with base.capture_stdout() as out:
            octant.main()
        result = out.getvalue()
        self.assertIs(True, "3452" in result)
        self.assertIs(True, "421" in result)

    @mock.patch("octant.front.main.sys.exit")
    @mock.patch("octant.source.openstack_source.register")
    @mock.patch("octant.source.skydive_source.register")
    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.front.parser.open")
    def test_main_incompat(
            self, mock_open, mock_cfg, mock_src1,
            mock_src2, mock_exit):
        standard_cfg(mock_cfg)
        mock_cfg.csv = True
        mock.mock_open(mock=mock_open, read_data="p(3452).")
        with base.capture_stdout():
            octant.main()
        mock_exit.assert_called_once_with(1)

    @mock.patch("octant.front.main.sys.exit")
    @mock.patch("octant.source.openstack_source.register")
    @mock.patch("octant.source.skydive_source.register")
    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.front.parser.open")
    def test_main_parse_error(
            self, mock_open, mock_cfg, mock_src1,
            mock_src2, mock_exit):
        standard_cfg(mock_cfg)
        mock.mock_open(mock=mock_open, read_data="p(.")
        with base.capture_stdout():
            octant.main()
        # Weird case. Because we do not really exit, we proceed too far.
        # exit is called twice.
        mock_exit.assert_called_with(1)

    @mock.patch("octant.front.main.sys.exit")
    @mock.patch("octant.source.openstack_source.register")
    @mock.patch("octant.source.skydive_source.register")
    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.front.parser.open")
    def test_main_type_error(
            self, mock_open, mock_cfg, mock_src1,
            mock_src2, mock_exit):
        standard_cfg(mock_cfg)
        mock.mock_open(mock=mock_open, read_data="p(3452:ukw_type).")
        with base.capture_stdout():
            octant.main()
        mock_exit.assert_called_once_with(1)

    @mock.patch("octant.front.main.sys.exit")
    @mock.patch("octant.source.openstack_source.register")
    @mock.patch("octant.source.skydive_source.register")
    @mock.patch("oslo_config.cfg.CONF")
    @mock.patch("octant.front.parser.open")
    def test_main_parse_error_query(
            self, mock_open, mock_cfg, mock_src1,
            mock_src2, mock_exit):
        standard_cfg(mock_cfg)
        mock_cfg.query = ["p("]
        mock.mock_open(mock=mock_open, read_data="p().")
        with base.capture_stdout():
            octant.main()
        mock_exit.assert_called_once_with(1)
