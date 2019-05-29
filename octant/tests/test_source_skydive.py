# -*- coding: utf-8 -*-

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
test_source_openstack
----------------------------------

Tests Openstack datasource
"""
import mock
import six
import z3

from octant import datalog_primitives as primitives
from octant import datalog_source as datasource
from octant import source_skydive as source
from octant.tests import base

NODES = [
    # Host
    {'revision': 2, 'created_at': 1528701912194, 'updated_at': 1528701912194,
     'host': u'ctrl', 'deleted_at': 0,
     'id': u'faf49edc-9ee0-4ca4-7ca9-b3bee2b8c2b0',
     'metadata': {
         u'KernelVersion': u'4.4.0-127-generic',
         u'info': u'This is compute node', u'VirtualizationSystem': u'kvm',
         u'Name': u'ctrl', u'TID': u'da63195d-a44b-5588-5c46-1d8184dcb824',
         u'PlatformFamily': u'debian', u'InstanceID': u'ds1', u'Type': u'host',
         u'VirtualizationRole': u'guest', u'Platform': u'ubuntu',
         u'PlatformVersion': u'16.04', u'OS': u'linux',
         u'CPU': [
             {u'Model': u'6', u'VendorID': u'GenuineIntel',
              u'ModelName': u'QEMU Virtual CPU version 2.5+', u'Family': u'6',
              u'PhysicalID': u'0', u'CoreID': u'0', u'Mhz': 2666,
              u'Stepping': 3, u'CacheSize': 4096, u'Cores': 1,
              u'Microcode': u'0x1', u'CPU': 0},
             {u'Model': u'6', u'VendorID': u'GenuineIntel',
              u'ModelName': u'QEMU Virtual CPU version 2.5+', u'Family': u'6',
              u'PhysicalID': u'1', u'CoreID': u'0', u'Mhz': 2666,
              u'Stepping': 3, u'CacheSize': 4096, u'Cores': 1,
              u'Microcode': u'0x1', u'CPU': 1}]}},
    # OVS
    {'revision': 3, 'created_at': 1528701912315, 'updated_at': 1528701917322,
     'host': u'ctrl', 'deleted_at': 0,
     'id': u'a8ea6374-ecc2-4e9e-7767-d0bf8a103c5d',
     'metadata': {
         u'FDB': [{
             u'IfIndex': 4, u'MAC': u'33:33:00:00:00:01',
             u'Flags': [u'NTF_SELF'], u'State': [u'NUD_PERMANENT']}],
         u'Features': {
             u'rx-lro': False, u'tx-vlan-stag-hw-insert': False,
             u'rx-vlan-stag-filter': False, u'highdma': True,
             u'tx-tcp-segmentation': True, u'tx-nocache-copy': False,
             u'rx-checksum': False, u'tx-tcp6-segmentation': True,
             u'tx-generic-segmentation': True, u'netns-local': True,
             u'tx-checksum-ip-generic': True, u'l2-fwd-offload': False,
             u'vlan-challenged': False, u'tx-scatter-gather': True,
             u'loopback': False, u'tx-ipip-segmentation': True,
             u'tx-udp_tnl-segmentation': True, u'tx-gre-segmentation': True,
             u'fcoe-mtu': False, u'rx-vlan-stag-hw-parse': False,
             u'rx-hashing': False, u'tx-gso-robust': False,
             u'tx-checksum-sctp': False, u'tx-checksum-ipv4': False,
             u'tx-scatter-gather-fraglist': True, u'tx-checksum-ipv6': False,
             u'tx-sit-segmentation': True, u'busy-poll': False,
             u'tx-checksum-fcoe-crc': False, u'tx-udp-fragmentation': True,
             u'rx-all': False, u'rx-vlan-hw-parse': False,
             u'tx-tcp-ecn-segmentation': True, u'rx-ntuple-filter': False,
             u'rx-gro': True, u'tx-fcoe-segmentation': False,
             u'tx-lockless': True, u'rx-vlan-filter': False,
             u'tx-vlan-hw-insert': True, u'rx-fcs': False,
             u'hw-tc-offload': False},
         u'State': u'DOWN', u'Metric': {}, u'Driver': u'openvswitch',
         u'EncapType': u'ether', u'MTU': 1500,
         u'TID': u'a5b3ee29-3fe3-50ce-6243-d6d7743a74cd',
         u'MAC': u'0a:9f:d9:d6:9a:b3', u'IfIndex': 4, u'Type': u'openvswitch',
         u'Name': u'ovs-system'}},
    # OVS Bridge
    {'revision': 2, 'created_at': 1528701912220, 'updated_at': 1528701912220,
     'host': u'ctrl', 'deleted_at': 0,
     'id': u'd984f64c-6113-4b6d-7500-a71cdb3d55f7',
     'metadata': {
         u'TID': u'21493be0-e7b9-5099-690e-085e75d24cf2',
         u'Type': u'ovsbridge', u'Name': u'br-ex',
         u'UUID': u'259bd2c7-50b2-4c46-b5b3-0e0bc6ece147'}},
    {'revision': 2, 'created_at': 1528701912218, 'updated_at': 1528701912218,
     'host': u'ctrl', 'deleted_at': 0,
     'id': u'70b727e0-c779-47e9-409a-337ed06bdb62',
     'metadata': {
         u'TID': u'3802da4b-0129-52c9-4c45-b2d5b6aeee20',
         u'Type': u'ovsbridge', u'Name': u'br-int',
         u'UUID': u'd0b1431f-5ccc-4e76-ba66-fc7f26580e2b'}},
    # OVSPort
    {'created_at': 1528701912238, 'updated_at': 1528701912238,
     'id': 'ce59a8fd-0cd5-4ac3-6f1f-0e7355a950e7', 'revision': 3,
     'host': 'ctrl', 'deleted_at': 0,
     'metadata': {
         'Name': 'qg-75db668f-fd', 'Vlans': 2,
         'TID': '97ca78b9-920f-5bdc-5524-4b4e1ffab178', 'Type': 'ovsport',
         'UUID': 'c1c6956c-0013-4d49-82db-c61707af097f'}},
    {'created_at': 1528701912239, 'updated_at': 1528701912239,
     'id': '982d6aa5-316d-42a6-5cab-eda0639be8a1', 'revision': 3,
     'host': 'ctrl', 'deleted_at': 0,
     'metadata': {
         'Name': 'qvo73620eae-46', 'Vlans': 1,
         'TID': 'eeaeab4b-8b79-5b44-514f-92030397ea8c', 'Type': 'ovsport',
         'UUID': 'c67b9efb-2765-4acd-ba80-efff0700e6e2'}},
    # Rules
    {'revision': 1, 'created_at': 1528701912380, 'updated_at': 1528701912380,
     'host': u'ctrl', 'deleted_at': 0,
     'id': u'3377b1d8-cb50-4e80-6b76-693e452bca20',
     'metadata': {
         u'UUID': u'7da48a40-c169-5f23-6ee5-bca4666c1551', u'actions': u'drop',
         u'priority': 0, u'cookie': u'0x4c3bb5b17f919ff',
         u'filters': u'priority=0', u'table': 24, u'Type': u'ofrule'}},
    {'revision': 1, 'created_at': 1528701912375, 'updated_at': 1528701912375,
     'host': u'ctrl', 'deleted_at': 0,
     'id': u'e3c793a3-198a-4b27-69be-8c3a15d92321',
     'metadata': {
         u'UUID': u'f6549054-ad5f-54b4-7147-da8dc76e2a52',
         u'actions': u'drop', u'priority': 0, u'cookie': u'0x4c3bb5b17f919ff',
         u'filters': u'priority=0', u'table': 23, u'Type': u'ofrule'}},
    {'revision': 1, 'created_at': 1528701912370, 'updated_at': 1528701912370,
     'host': u'ctrl', 'deleted_at': 0,
     'id': u'e38b91ef-e475-4af3-5cb3-9fea8f1be292',
     'metadata': {
         u'UUID': u'17d171c4-0e3f-5b28-59d6-7ce0b8c2ee08',
         u'actions': u'goto_table:60',
         u'priority': 0, u'cookie': u'0x4c3bb5b17f919ff',
         u'filters': u'priority=0', u'table': 0, u'Type': u'ofrule'}}
]

EDGES = [
    {'created_at': 1528701912237, 'updated_at': 1528701912237,
     'id': 'bbe0c719-a945-584a-44d7-02ff9fa46f8d', 'revision': 0,
     'host': 'ctrl', 'parent': 'd984f64c-6113-4b6d-7500-a71cdb3d55f7',
     'child': 'bffc4a20-d884-4ce6-6d76-13dc1a025b48', 'deleted_at': 0,
     'metadata': {'RelationType': 'ownership'}},
    {'created_at': 1528701912237, 'updated_at': 1528701912237,
     'id': 'bbe0c719-a945-584a-44d7-02ff9fa46f8d', 'revision': 0,
     'host': 'ctrl', 'parent': 'd984f64c-6113-4b6d-7500-a71cdb3d55f7',
     'child': 'bffc4a20-d884-4ce6-6d76-13dc1a025b48', 'deleted_at': 0,
     'metadata': {'RelationType': 'ownership'}},
    # Layer 2
    {'child': '09ee287a-9035-4dab-6615-0dd3cf5094fb',
     'id': 'b3b6ae71-e366-528e-71b9-fc1ae0951656', 'host': 'ctrl',
     'deleted_at': 0, 'parent': 'fbf4dda1-3aaa-4bcd-6d49-2efb2881c36e',
     'metadata': {'RelationType': 'layer2'},
     'revision': 0, 'created_at': 1528701912240, 'updated_at': 1528701912240},
    {'child': 'f5aee614-f82c-41c8-5963-71938063c4ab',
     'id': '46776259-c0bd-5cf4-42fe-8f72243495db', 'host': 'ctrl',
     'deleted_at': 0, 'parent': '982d6aa5-316d-42a6-5cab-eda0639be8a1',
     'metadata': {'RelationType': 'layer2'},
     'revision': 0, 'created_at': 1528701912239, 'updated_at': 1528701912239}
]


class MockNode(object):
    "Mocks a skydive node"

    def __init__(self, json):
        self.__dict__ = json


class MockSkydiveCnx(object):
    "Mocks a REST Skydive connection"

    def lookup_nodes(self, query):
        sp_query = query.split('"')
        sel = sp_query[1]
        kind = sp_query[3]
        return [MockNode(x) for x in NODES if x['metadata'][sel] == kind]

    def lookup_edges(self, query):
        sp_query = query.split('"')
        sel = sp_query[1]
        kind = sp_query[3]
        return [MockNode(x) for x in EDGES if x['metadata'][sel] == kind]


class TestSourceSkydive(base.TestCase):
    """Test the skydive datasource"""

    def test_primitive_types_skydive(self):
        for table, (_, fields) in six.iteritems(source.TABLES):
            for field, (ftype, _) in six.iteritems(fields):
                self.assertIn(
                    ftype, primitives.TYPES,
                    message="type of {} in {} is {}".format(field, table,
                                                            ftype))

    def verify(self, name):
        conn = source.SkydiveCnx(MockSkydiveCnx())
        (access_rows, fields) = source.TABLES[name]
        # Py35 and Py27 types are not the same.
        # ref_type1 is BitVecRef and ref_type2 is BoolRef in py35
        # both are 'instance' in py27
        ref_type1 = type(z3.BitVecVal(2, z3.BitVecSort(3)))
        ref_type2 = type(z3.simplify(z3.And(True, True)))
        for row in access_rows(conn):
            for field in fields:
                (typ, access_field) = fields[field]
                result = primitives.TYPES[typ].to_z3(access_field(row))
                self.assertIn(type(result), [ref_type1, ref_type2])

    def test_host(self):
        self.verify('sk_host')

    def test_ofrule(self):
        self.verify('sk_rule')

    def test_vswitch(self):
        self.verify('sk_ovsswitch')

    def test_bridge(self):
        self.verify('sk_ovsbridge')

    def test_port(self):
        self.verify('sk_ovsport')

    def test_ovs_patch(self):
        self.verify('sk_patch')

    def test_ovs_internal(self):
        self.verify('sk_internal')

    def test_ovs_internal_ip(self):
        self.verify('sk_internal_ip')

    def test_owns(self):
        self.verify('sk_owns')

    def test_l2(self):
        self.verify('sk_l2')

    @mock.patch("skydive.rest.client.RESTClient")
    @mock.patch("oslo_config.cfg.CONF")
    def test_register(self, mock_conf, mock_client):
        mock_conf.skydive.enabled = False
        mock_conf.restore = None
        src = datasource.Datasource(primitives.TYPES)
        source.register(src)
        mock_client.assert_not_called()
        mock_conf.skydive.enabled = True
        mock_conf.restore = "file_path"
        source.register(src)
        mock_client.assert_not_called()
        mock_conf.restore = None
        source.register(src)
        mock_client.assert_called_once()
