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
test_z3_result
--------------

Tests for `z3_result` module.
"""

from contextlib import contextmanager
import six
import sys
import textwrap
import z3

from octant.common import base as obase
from octant.common import primitives
from octant.front import z3_result as z3r
from octant.tests import base


@contextmanager
def capture_stdout():
    old = sys.stdout
    try:
        sys.stdout = six.StringIO()
        yield sys.stdout
    finally:
        sys.stdout = old


class TestZ3Result(base.TestCase):
    def test_z3_to_array(self):
        s = z3.BitVecSort(4)

        def bv(x):
            return z3.BitVecVal(x, s)

        x = z3.Var(0, s)
        y = z3.Var(1, s)
        z = z3.Var(2, s)
        types = [primitives.TYPES['int4']] * 3

        def project(grid):
            return [{k: x for k, x in row.faces.items()} for row in grid]

        e0 = x == bv(3)
        e1 = z3.And(x == bv(3), y == bv(2), z == bv(1))
        e2 = z3.Or(e1, z3.And(x == bv(13), y == bv(12), z == bv(11)))
        e3 = z3.Or(x == bv(6), y == bv(5), z == bv(4))
        self.assertEqual([{0: 3}], project(z3r.z3_to_array(e0, types)))
        self.assertEqual(
            [{0: 3, 1: 2, 2: 1}],
            project(z3r.z3_to_array(e1, types)))
        self.assertEqual(
            [{0: 3, 1: 2, 2: 1}, {0: 13, 1: 12, 2: 11}],
            project(z3r.z3_to_array(e2, types)))
        self.assertEqual(
            [{0: 6}, {1: 5}, {2: 4}],
            project(z3r.z3_to_array(e3, types)))
        self.assertIs(
            True,
            z3r.z3_to_array(z3.simplify(z3.And(True, True)), z3r))
        self.assertIs(
            False,
            z3r.z3_to_array(z3.simplify(z3.And(True, False)), z3r))

    def test_z3_to_array_fails(self):
        s = z3.BitVecSort(4)
        x = z3.Const('x', s)
        types = [primitives.TYPES['int4']]
        self.assertRaises(
            obase.Z3NotWellFormed,
            lambda: z3r.z3_to_array(x, types))
        self.assertRaises(
            obase.Z3NotWellFormed,
            lambda: z3r.z3_to_array(z3.Or(x > 2, x < 1), types))

    def test_z3_to_array_doc(self):
        s = z3.BitVecSort(8)
        s2 = z3.BitVecSort(2)

        def bv(x):
            return z3.BitVecVal(x, s)

        def bv2(x):
            return z3.BitVecVal(x, s2)

        x = z3.Var(0, s)
        y = z3.Var(1, s)
        types = [primitives.TYPES['int4']] * 2
        e1 = z3.Extract(3, 2, x) == bv2(3)
        e2 = z3.And(z3.Extract(3, 2, x) == bv2(3),
                    z3.Extract(7, 6, x) == bv2(2))
        e3 = z3.And(
            z3.Extract(3, 2, x) == bv2(3), z3.Extract(7, 6, x) == bv2(2),
            y == bv(4))
        e4 = z3.And(
            z3.Extract(5, 4, x) == bv2(1),
            z3.Not(z3.And(
                z3.Extract(3, 2, x) == bv2(3),
                z3.Extract(7, 6, x) == bv2(2), y == bv(4))))
        e5 = z3.And(
            True,
            z3.Not(
                z3.Extract(5, 4, x) == bv2(1)),
            z3.Not(z3.And(
                z3.Extract(3, 2, x) == bv2(3),
                z3.Extract(7, 6, x) == bv2(2), y == bv(4))))

        r1 = [z3r.Cube({0: z3r.Masked(0xc, 0xc)})]
        r2 = [z3r.Cube({0: z3r.Masked(0x8c, 0xcc)})]
        r3 = [z3r.Cube({0: z3r.Masked(0x8c, 0xcc), 1: 4})]
        r4 = [
            z3r.Doc(
                z3r.Cube({0: z3r.Masked(0x10, 0x30)}),
                [z3r.Cube({0: z3r.Masked(0x8c, 0xcc), 1: 4})])]
        r5 = [
            z3r.Doc(
                z3r.Cube({}),
                [z3r.Cube({0: z3r.Masked(0x10, 0x30)}),
                 z3r.Cube({0: z3r.Masked(0x8c, 0xcc), 1: 4})])]
        for (r, e) in [(r1, e1), (r2, e2), (r3, e3), (r4, e4), (r5, e5)]:
            self.assertEqual(r, z3r.z3_to_array(e, types))

    def test_print_csv(self):
        with capture_stdout() as out:
            z3r.print_csv(
                ["X", "Y"],
                [z3r.Cube({0: 2, 1: 3}), z3r.Cube({0: 4, 1: 5})])
        self.assertEqual('P,X,Y\r\n+,2,3\r\n+,4,5\r\n\n', out.getvalue())
        with capture_stdout() as out:
            z3r.print_csv([], True)
        self.assertIs(True, "True" in out.getvalue())

    def test_print_csv_doc(self):
        answer = [
            z3r.Doc(
                z3r.Cube({0: z3r.Masked(0x10, 0x30)}),
                [z3r.Cube({0: z3r.Masked(0x8c, 0xcc), 1: 4})]),
            z3r.Doc(
                z3r.Cube({}),
                [z3r.Cube({0: z3r.Masked(0x10, 0x30)}),
                 z3r.Cube({0: z3r.Masked(0x8c, 0xcc), 1: 4})])]
        formatted = textwrap.dedent("""\
                    P,X,Y\r
                    +,16/48,*\r
                    -,140/204,4\r
                    +,*,*\r
                    -,16/48,*\r
                    -,140/204,4\r\n
                    """)
        with capture_stdout() as out:
            z3r.print_csv(["X", "Y"], answer)
        self.assertEqual(formatted, out.getvalue())

    def test_print_pretty_doc(self):
        answer = [
            z3r.Doc(
                z3r.Cube({0: z3r.Masked(0x10, 0x30)}),
                [z3r.Cube({0: z3r.Masked(0x8c, 0xcc), 1: 4})]),
            z3r.Doc(
                z3r.Cube({}),
                [z3r.Cube({0: z3r.Masked(0x10, 0x30)}),
                 z3r.Cube({0: z3r.Masked(0x8c, 0xcc), 1: 4})])]
        formatted = textwrap.dedent("""\
            +===+=========+===+
            |   | X       | Y |
            +===+=========+===+
            | + | 16/48   | * |
            +---+---------+---+
            | - | 140/204 | 4 |
            +===+=========+===+
            | + | *       | * |
            +---+---------+---+
            | - | 16/48   | * |
            | - | 140/204 | 4 |
            +===+=========+===+
            """)
        with capture_stdout() as out:
            z3r.print_pretty(["X", "Y"], answer)
        self.assertEqual(formatted, out.getvalue())
