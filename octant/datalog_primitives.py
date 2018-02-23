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


@six.add_metaclass(abc.ABCMeta)
class Z3Type(object):
    """Translate Openstack values to Z3"""

    def __init__(self, name, type_instance):
        self.name = name
        self.type_instance = type_instance

    @abc.abstractmethod
    def z3(self, val):
        """Transforms a value from OpenStack in a Z3 value"""
        raise NotImplementedError

    @abc.abstractmethod
    def os(self, val):
        """Transforms a value from Z3 back to python"""
        raise NotImplementedError

    def type(self):
        """Gives back the Z3 type"""
        return self.type_instance


class BoolType(Z3Type):
    """Transcode boolean in Z3"""

    def __init__(self):
        super(BoolType, self).__init__('bool', z3.BoolSort())

    def z3(self, val):
        return z3.BoolVal(val)

    def os(self, val):
        return val.decl().name() == 'true'


class StringType(Z3Type):
    """Transcode strings in Z3"""

    def __init__(self, name, size=16):
        super(StringType, self).__init__(name, z3.BitVecSort(size))
        self.map = {}
        self.back = {}

    def z3(self, str):
        if str in self.map:
            return self.map[str]
        else:
            code = len(self.map)
            val = z3.BitVecVal(code, self.type_instance)
            self.map[str] = val
            self.back[code] = str
            return val

    def os(self, val):
        return self.back[val.as_long()]


class NumType(Z3Type):
    """Transcode numbers in Z3"""

    def __init__(self, name, size=32):
        super(NumType, self).__init__(name, z3.BitVecSort(size))
        self.map = {}
        self.back = {}

    def z3(self, val):
        return z3.BitVecVal(val, self.type_instance)

    def os(self, val):
        return val.as_long()


IpAddressSort = z3.BitVecSort(32)


class IpAddressType(Z3Type):
    """Transcode IP address in Z3"""

    def __init__(self):
        super(IpAddressType, self).__init__('ipaddress', IpAddressSort)

    def z3(self, val):
        return z3.BitVecVal(int(ipaddress.ip_address(val)), self.type_instance)

    def os(self, val):
        return ipaddress.ip_address(val.as_long()).compressed


TYPES = {
    'bool': BoolType(),
    'string': StringType('string'),
    'id': StringType('id'),
    'int': NumType('int'),
    'int4': NumType('int', size=4),
    'direction': StringType('direction', size=2),
    'status': StringType('status', size=3),
    'ip_address': IpAddressType(),
    'ip_version': StringType('direction', size=2),
}


def bits_of_mask(mask):
    """Bit size of a network mask

    From an integer representing a network mask, extract
    the number of bits of the mask (for cidr notation).
    """
    bits = 0
    while(mask > 0):
        bits += 1
        mask = (mask & 0x7fffffff) << 1
    return bits


def normalize_status(raw):
    """Normalize status values

    Gives back a value between active,down,build,error and other
    """
    lower = raw.lower()
    if lower in ['active', 'down', 'build', 'error']:
        return lower
    return 'other'


def prefix_of_network(cidr):
    return (
        '0.0.0.0' if cidr is None
        else ipaddress.ip_network(
            cidr, strict=False).network_address.compressed)


def mask_of_network(cidr):
    return (
        '0.0.0.0' if cidr is None
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
    "true": ast.BoolConstant(True),
    "false": ast.BoolConstant(False)
}


def _get_port_ips(conn):
    return (
        (p.id, fixed_ip)
        for p in conn.network.ports()
        for fixed_ip in p.fixed_ips)


def _get_port_sgs(conn):
    return (
        (p.id, sg_id)
        for p in conn.network.ports()
        for sg_id in p.security_group_ids
    )


def _get_subnet_pool_prefixes(conn):
    return (
        (snp.id, prefix)
        for snp in conn.network.subnet_pools()
        for prefix in snp.prefixes)


def ip_version(n):
    return 'ipv4' if n == 4 else 'ipv6'


def _project_scope(p):
    return (
        p.scope['project']['id']
        if p.scope is not None and p.scope.get('project', None) is not None
        else None)


# Describes how to bind values extracted from the to Python table.
TABLES = {
    "network": (lambda conn: conn.network.networks(), {
        "id": ("id", lambda n: n.id),
        "project_id": ("id", lambda n: n.project_id),
        "name": ("string", lambda n: n.name),
        "status": ("status", lambda n: normalize_status(n.status))
    }),
    "router": (lambda conn: conn.network.routers(), {
        "id": ("id", lambda r: r.id),
        "project_id": ("id", lambda r: r.project_id),
        "status": ("status", lambda r: normalize_status(r.status)),
        "name": ("string", lambda r: r.name)
    }),
    "port": (lambda conn: conn.network.ports(), {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "host": ("string", lambda p: p.binding_host_id),
        "network_id": ("id", lambda p: p.network_id),
        "project_id": ("id", lambda p: p.project_id),
        "device_id": ("id", lambda p: p.device_id),
        "status": ("status", lambda p: normalize_status(p.status))
    }),
    "port_ip": (_get_port_ips, {
        "port_id": ("id", lambda pi: pi[0]),
        "subnet_id": ("id", lambda pi: pi[1]['subnet_id']),
        "ip": ("ip_address", lambda pi: pi[1]['ip_address']),
    }),
    "port_sg": (_get_port_sgs, {
        "port_id": ("id", lambda psg: psg[0]),
        "sg_id": ("id", lambda psg: psg[1]),
    }),
    "subnet": (lambda conn: conn.network.subnets(), {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "network_id": ("id", lambda p: p.network_id),
        "project_id": ("id", lambda p: p.project_id),
        "cidr_prefix": ("ip_address", lambda s: prefix_of_network(s.cidr)),
        "cidr_mask": ("ip_address", lambda s: mask_of_network(s.cidr)),
        "gateway_ip": ("ip_address", lambda s: s.gateway_ip),
        "ip_version": ("ip_version", lambda s: ip_version(s.ip_version))
    }),
    "subnet_pool": (lambda conn: conn.network.subnet_pools(), {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "ip_version": ("ip_version", lambda s: ip_version(s.ip_version)),
        "project_id": ("id", lambda p: p.project_id),
        "address_scope_id": ("id", lambda p: p.address_scope_id),
    }),
    "subnet_pool_prefixes": (_get_subnet_pool_prefixes, {
        "id": ("id", lambda p: p[0]),
        "prefix": ("ip_address", lambda p: prefix_of_network(p[1])),
        "mask": ("ip_address", lambda p: mask_of_network(p[1]))
    }),
    "address_scope": (lambda conn: conn.network.address_scopes(), {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
    }),
    "sg": (lambda conn: conn.network.security_groups(), {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "project_id": ("id", lambda p: p.project_id),
    }),
    "rule": ((lambda conn: conn.network.security_group_rules(), {
        "id": ("id", lambda p: p.id),
        "direction": ("string", lambda p: p.direction),
        "ip_version": (
            "ip_version",
            lambda p: ip_version(4 if p.ether_type == 'IPv4' else 6)
        ),
        "port_range_max": ("int", (
            lambda p: 65536 if p.port_range_max is None else p.port_range_max
        )),
        "port_range_min": ("int", (
            lambda p: 0 if p.port_range_min is None else p.port_range_min
        )),
        "protocol": ("string", (lambda p: p.protocol)),
        "project_id": ("id", lambda p: p.project_id),
        "remote_group_id": ("id", lambda p: p.remote_group_id),
        "remote_ip_prefix": ("ip_address", (
            lambda p: prefix_of_network(p.remote_ip_prefix)
        )),
        "remote_ip_mask": ("ip_address", (
            lambda p: mask_of_network(p.remote_ip_prefix)
        )),
        "security_group_id": ("id", lambda p: p.security_group_id)
    })),
    "server": (lambda conn: conn.compute.servers(), {
        "id": ("id", lambda s: s.id),
        "project_id": ("id", lambda s: s.project_id),
        "name": ("string", lambda s: s.name),
        "host": ("string", lambda s: s.hypervisor_hostname),
        "image_id": ("id", lambda s: s.image['id']),
        "flavor_id": ("id", lambda s: s.flavor['id'])
    }),
    "flavor": (lambda conn: conn.compute.flavors(), {
        "id": ("id", lambda f: f.id),
        "name": ("string", lambda f: f.name),
        "vcpus": ("int", lambda f: f.vcpus),
        "ram": ("int", lambda f: f.ram),
        "disk": ("int", lambda f: f.disk),
        "public": ("bool", lambda f: f.is_public)
    }),
    "image": (lambda conn: conn.image.images(), {
        "id": ("id", lambda f: f.id),
        "name": ("string", lambda f: f.name),
    }),
    "project": (lambda conn: conn.identity.projects(), {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "domain_id": ("id", lambda p: p.domain_id),
        "parent_id": ("id", (lambda p: p.parent_id))
    }),
    "region": (lambda conn: conn.identity.regions(), {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "parent_id": ("id", (lambda p: p.parent_region_id)),
    }),
    "domain": (lambda conn: conn.identity.domains(), {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name)
    }),
    "role": (lambda conn: conn.identity.roles(), {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name)
    }),
    "user": (lambda conn: conn.identity.users(), {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "domain_id": ("id", lambda p: p.domain_id)
    }),
    "service": (lambda conn: conn.identity.services(), {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "type": ("string", lambda p: p.type)
    }),
    "endpoint": (lambda conn: conn.identity.endpoints(), {
        "id": ("id", lambda p: p.id),
        "url": ("string", lambda p: p.url),
        "interface": ("string", lambda p: p.interface),
        "service_id": ("id", lambda p: p.service_id),
        "region_id": ("id", lambda p: p.region_id)
    }),
    "group": (lambda conn: conn.identity.groups(), {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "domain_id": ("id", lambda p: p.domain_id)
    }),
    "role_assignment": (lambda conn: conn.identity.role_assignments(), {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "group_id": ("id", (
            lambda p: p.group['id'] if p.group is not None else None
        )),
        "role_id": ("id", lambda p: p.role['id']),
        "project_id": ("id", _project_scope),
        "user_id": ("id", (
            lambda p: p.user['id'] if p.user is not None else None
        ))
    })
}


def is_primitive_atom(atom):
    "Check if a atom refers to a primitive table."
    return atom.table in TABLES
