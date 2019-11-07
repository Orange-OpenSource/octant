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
test_datalog_primitives
----------------------------------

Tests for `primitives` module.
"""

import z3

from octant.common import primitives
from octant.tests import base


class TestBoolType(base.TestCase):
    """Z3 Boolean values"""
    bool_false = z3.BitVecVal(0, 1)
    bool_true = z3.BitVecVal(1, 1)

    def setUp(self):
        self.type = primitives.BoolType()
        super(TestBoolType, self).setUp()

    def test_marshal(self):
        self.assertEqual('True', self.type.marshall(True))
        self.assertEqual('False', self.type.marshall(False))

    def test_unmarshal(self):
        self.assertEqual(True, self.type.unmarshall('True'))
        self.assertEqual(False, self.type.unmarshall('False'))

    def test_to_z3(self):
        self.assertEqual(TestBoolType.bool_true, self.type.to_z3(True))
        self.assertEqual(TestBoolType.bool_false, self.type.to_z3(False))

    def test_from_z3(self):
        self.assertEqual(True, TestBoolType.bool_true)
        self.assertEqual(False, TestBoolType.bool_false)


class TestStringType(base.TestCase):
    """Z3 Boolean values"""

    def setUp(self):
        self.type = primitives.StringType('string', size=8)
        super(TestStringType, self).setUp()

    def test_marshal(self):
        self.assertEqual('aaa', self.type.marshall('aaa'))
        self.assertEqual(primitives.MARSHALLED_NONE, self.type.marshall(None))

    def test_unmarshal(self):
        self.assertEqual('aaa', self.type.unmarshall('aaa'))
        self.assertEqual(None,
                         self.type.unmarshall(primitives.MARSHALLED_NONE))

    def test_to_z3(self):
        x = self.type.to_z3('aaaa')
        self.assertEqual(8, x.size())
        # Do not try to use equality on Z3 values.
        self.assertEqual(self.type.to_z3('aaaa').as_long(), x.as_long())
        self.assertIs(False,
                      self.type.to_z3('bbbb').as_long() == x.as_long())

    def test_from_z3(self):
        self.assertEqual('aaaa', self.type.to_os(self.type.to_z3('aaaa')))


class TestNumType(base.TestCase):
    """Z3 Num values"""

    def setUp(self):
        self.type = primitives.NumType('int', size=16)
        super(TestNumType, self).setUp()

    def test_marshalling(self):
        self.assertEqual(10, self.type.marshall(10))
        self.assertEqual(20, self.type.unmarshall(20))

    def test_to_z3(self):
        x = self.type.to_z3(342)
        self.assertEqual(16, x.size())
        self.assertEqual(342, x.as_long())

    def test_from_z3(self):
        self.assertEqual(421, self.type.to_os(self.type.to_z3(421)))


class TestIpType(base.TestCase):
    """Z3 Num values"""

    def setUp(self):
        self.type = primitives.IpAddressType()
        super(TestIpType, self).setUp()

    def test_marshalling(self):
        # Pure identity - no handling of None
        self.assertEqual(u'192.168.0.1', self.type.marshall(u'192.168.0.1'))
        self.assertEqual(u'192.168.0.1', self.type.unmarshall(u'192.168.0.1'))

    def test_to_z3(self):

        x = self.type.to_z3(u'10.0.0.4')
        self.assertEqual(32, x.size())
        self.assertEqual(0x0a000004, x.as_long())

    def test_from_z3(self):
        self.assertEqual(
            u'192.168.0.1',
            self.type.to_os(self.type.to_z3(u'192.168.0.1')))


class TestPrimitives(base.TestCase):

    def test_bit_of_masks(self):
        self.assertEqual(8, primitives.bits_of_mask(0xff000000))
        self.assertEqual(16, primitives.bits_of_mask(0xffff0000))
        self.assertEqual(32, primitives.bits_of_mask(0xffffffff))
        self.assertEqual(0, primitives.bits_of_mask(0x00000000))

    def test_prefix_of_network(self):
        self.assertEqual(u'0.0.0.0', primitives.prefix_of_network(None))
        self.assertEqual(
            u'192.168.0.0', primitives.prefix_of_network(u'192.168.0.0/24'))
        self.assertEqual(
            u'10.0.0.0', primitives.prefix_of_network(u'10.0.0.0/8'))

    def test_mask_of_network(self):
        self.assertEqual(u'0.0.0.0', primitives.mask_of_network(None))
        self.assertEqual(
            u'255.255.255.0', primitives.mask_of_network(u'192.168.0.0/24'))
        self.assertEqual(
            u'255.0.0.0', primitives.mask_of_network(u'10.0.0.0/8'))
