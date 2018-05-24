#    Copyright 2018 Orange
#
#    Licensed under the Apache License, Version 2.0 (the "License"); you may
#    not use this file except in compliance with the License. You may obtain
#    a copy of the License at
#
#         http://www.apache.org/licenses/LICENSE-2.0
#
#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
#    WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
#    License for the specific language governing permissions and limitations
#    under the License.

"""Primitive tables exported from OpenStack for Datalog"""
import abc
import collections
import ipaddress
import six
import z3

from octant import datalog_ast as ast


MARSHALLED_NONE = "-*-None-*-"


@six.add_metaclass(abc.ABCMeta)
class Z3Type(object):
    """Translate Openstack values to Z3"""

    def __init__(self, name, type_instance):
        self.name = name
        self.type_instance = type_instance

    @abc.abstractmethod
    def to_z3(self, val):
        """Transforms a value from OpenStack in a Z3 value"""
        raise NotImplementedError

    @abc.abstractmethod
    def to_os(self, val):
        """Transforms a value from Z3 back to python"""
        raise NotImplementedError

    @abc.abstractmethod
    def marshall(self, val):
        """Transforms a value from OpenStack in a string or int."""
        raise NotImplementedError

    @abc.abstractmethod
    def unmarshall(self, val):
        """Transforms back a string to a raw OpenStack value."""
        raise NotImplementedError

    def type(self):
        """Gives back the Z3 type"""
        return self.type_instance


class BoolType(Z3Type):
    """Transcode boolean in Z3"""

    def __init__(self):
        super(BoolType, self).__init__('bool', z3.BoolSort())

    def to_z3(self, val):
        return z3.BoolVal(val)

    def marshall(self, val):
        return str(val)

    def unmarshall(self, val):
        return val == 'True'

    def to_os(self, val):
        return val.decl().name() == 'true'


class StringType(Z3Type):
    """Transcode strings in Z3"""

    def __init__(self, name, size=16):
        super(StringType, self).__init__(name, z3.BitVecSort(size))
        self.map = {}
        self.back = {}

    def to_z3(self, val):
        if val in self.map:
            return self.map[val]
        code = len(self.map)
        bvect = z3.BitVecVal(code, self.type_instance)
        self.map[val] = bvect
        self.back[code] = val
        return bvect

    def marshall(self, val):
        return MARSHALLED_NONE if val is None else val

    def unmarshall(self, val):
        return None if val == MARSHALLED_NONE else val

    def to_os(self, val):
        return self.back[val.as_long()]


class NumType(Z3Type):
    """Transcode numbers in Z3"""

    def __init__(self, name, size=32):
        super(NumType, self).__init__(name, z3.BitVecSort(size))
        self.map = {}
        self.back = {}

    def to_z3(self, val):
        return z3.BitVecVal(val, self.type_instance)

    def marshall(self, val):
        return val

    def unmarshall(self, val):
        return val

    def to_os(self, val):
        return val.as_long()


IpAddressSort = z3.BitVecSort(32)


class IpAddressType(Z3Type):
    """Transcode IP address in Z3"""

    def __init__(self):
        super(IpAddressType, self).__init__('ipaddress', IpAddressSort)

    def to_z3(self, val):
        return z3.BitVecVal(int(ipaddress.ip_address(val)), self.type_instance)

    def marshall(self, val):
        return val

    def unmarshall(self, val):
        return val

    def to_os(self, val):
        return ipaddress.ip_address(val.as_long()).compressed


TYPES = {
    'bool': BoolType(),
    'string': StringType('string'),
    'id': StringType('id'),
    'int': NumType('int'),
    'int4': NumType('int4', size=4),
    'direction': StringType('direction', size=2),
    'status': StringType('status', size=3),
    'ip_address': IpAddressType(),
    'ip_version': StringType('ip_version', size=2),
    'fw_action': StringType('fw_action', size=2)
}


def bits_of_mask(mask):
    """Bit size of a network mask

    From an integer representing a network mask, extract
    the number of bits of the mask (for cidr notation).
    """
    bits = 0
    while mask > 0:
        bits += 1
        mask = (mask & 0x7fffffff) << 1
    return bits


def prefix_of_network(cidr):
    """Returns the prefix of a network in CIDR format

    If cidr is a single address, returns that address.
    """
    return (
        u'0.0.0.0' if cidr is None
        else ipaddress.ip_network(
            cidr, strict=False).network_address.compressed)


def mask_of_network(cidr):
    """Returns the mask of a network in CIDR format

    If cidr is a single address, the mask will be 255.255.255.255
    """
    return (
        u'0.0.0.0' if cidr is None
        else ipaddress.ip_network(cidr, strict=False).netmask.compressed)


Operation = collections.namedtuple(
    'Operation',
    ['args', 'result', 'ty_vars', 'z3'])

OPERATIONS = {
    "&": Operation(args=[0, 0], result=0, ty_vars=1, z3=(lambda x, y: x & y)),
    "|": Operation(args=[0, 0], result=0, ty_vars=1, z3=(lambda x, y: x | y)),
    "~": Operation(args=[0], result=0, ty_vars=1, z3=(lambda x: x))
}

COMPARISON = {
    "=": (lambda args: args[0] == args[1]),
    ">": (lambda args: args[0] > args[1]),
    ">=": (lambda args: args[0] >= args[1]),
    "<": (lambda args: args[0] < args[1]),
    "<=": (lambda args: args[0] <= args[1]),
}

CONSTANTS = {
    "none": ast.StringConstant(None, type='id'),
    "ingress": ast.StringConstant('ingress', type='direction'),
    "egress": ast.StringConstant('egress', type='direction'),
    "ipv4": ast.StringConstant('ipv4', type='ip_version'),
    "ipv6": ast.StringConstant('ipv6', type='ip_version'),
    "active": ast.StringConstant('active', type='status'),
    "down": ast.StringConstant('down', type='status'),
    "build": ast.StringConstant('build', type='status'),
    "error": ast.StringConstant('error', type='status'),
    "other": ast.StringConstant('other', type='status'),
    "allow": ast.StringConstant('allow', type='fw_action'),
    "reject": ast.StringConstant('reject', type='fw_action'),
    "deny": ast.StringConstant('deny', type='fw_action'),
    "true": ast.BoolConstant(True),
    "false": ast.BoolConstant(False)
}
