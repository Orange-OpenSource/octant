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
import six
import z3

from octant import datalog_primitives as primitives
from octant import source_openstack as source
from octant.tests import base

FIREWALL = {
    u'status': u'ACTIVE',
    u'router_ids': [
        u'2d3f4181-da9d-44f2-97d6-dde0c5d3fb2c',
        u'3f027dca-6ae5-414d-866c-49d6cf5828d2',
        u'5db8dfb1-7957-4829-bf1a-06ddba083a64',
        u'b29aee21-4730-4d02-830c-ca8a23432801',
        u'c4e8edea-89d7-4913-a1c5-0904377a0033'],
    u'name': u'firewall', u'admin_state_up': True,
    u'tenant_id': u'98034511bd7c480b81e975ef599fd13d',
    u'firewall_policy_id': u'08f87059-2231-4a31-b254-fd81fde7ad8b',
    u'project_id': u'98034511bd7c480b81e975ef599fd13d',
    u'id': u'011b4539-e19a-4018-b793-f5f2031afa75', u'description': u''}

FIREWALL_POLICY = {
    u'name': u'policy',
    u'firewall_rules': [
        u'f66a142a-62e2-4e85-bd53-2c09dfb138ad',
        u'48c52d40-8519-443f-8d91-62bbbd9fec2e',
        u'326dd195-7d83-43e0-85e4-d7c0b28f60c2',
        u'2865d0c0-f514-45d0-bd32-20e21dc77be5'],
    u'tenant_id': u'6a3b92fa16d24669906dff11df06cc84', u'audited': False,
    u'shared': False, u'project_id': u'6a3b92fa16d24669906dff11df06cc84',
    u'id': u'00b1c868-9011-4af8-a99f-492bed5b524d', u'description': u''}

FIREWALL_RULE = {
    u'protocol': u'tcp', u'description': u'', u'ip_version': 4,
    u'tenant_id': u'5cf3e4475a374bae91c334c1a164f24c', u'enabled': True,
    u'source_ip_address': None, u'destination_ip_address': None,
    u'firewall_policy_id': u'0c97cd57-f9dd-4412-adec-c826bbee7c09',
    u'action': u'allow', u'shared': False, u'source_port': None,
    u'position': 2, u'destination_port': u'80',
    u'project_id': u'5cf3e4475a374bae91c334c1a164f24c',
    u'id': u'0014effa-4434-4cc7-b77e-2dca67f14848', u'name': u'HTTP'}

FIREWALL_RULE_V2 = {
    u'protocol': u'icmp', u'description': u'', u'source_port': None,
    u'source_ip_address': None, u'destination_ip_address': None,
    u'firewall_policy_id': None, u'destination_port': None,
    u'id': u'11dace88-52df-40b1-83eb-96b62a1b37b6', u'name': u'r_icmp',
    u'tenant_id': u'6ab2197c1d72421b8a578b4181cffb40', u'enabled': True,
    u'action': u'allow', u'ip_version': 4, u'shared': False,
    u'project_id': u'6ab2197c1d72421b8a578b4181cffb40'}

FIREWALL_POLICY_V2 = {
    u'description': u'Egress firewall policy',
    u'firewall_rules': [
        u'efd85cff-9f59-41ac-9e87-d1cb34e8df3e',
        u'dd99aa75-ab46-42f2-88f5-6ad954ab6787'],
    u'tenant_id': u'6ab2197c1d72421b8a578b4181cffb40',
    u'id': u'6dd2c9a3-0780-47e1-8d86-28a619fecb68', u'shared': False,
    u'project_id': u'6ab2197c1d72421b8a578b4181cffb40',
    u'audited': False, u'name': u'default egress'}

FIREWALL_V2 = {
    u'status': u'ACTIVE', u'description': u'',
    u'ingress_firewall_policy_id': u'dfc408cb-5af2-47e7-819d-6669cf3fd564',
    u'id': u'277e1103-d31d-4b5f-86e5-601598b7d6bc',
    u'name': u'fga', u'admin_state_up': True,
    u'tenant_id': u'6ab2197c1d72421b8a578b4181cffb40', u'shared': False,
    u'project_id': u'6ab2197c1d72421b8a578b4181cffb40',
    u'ports': [
        u'cba4c500-7c54-4c1c-af6a-be3a57ee3015'],
    u'egress_firewall_policy_id': u'dfc408cb-5af2-47e7-819d-6669cf3fd564'}


class MockNeutronCnx(object):
    def list_firewalls(self):
        return {'firewalls': [FIREWALL]}

    def list_firewall_policies(self):
        return {'firewall_policies': [FIREWALL_POLICY]}

    def list_firewall_rules(self):
        return {'firewall_rules': [FIREWALL_RULE]}

    def list_fwaas_firewall_groups(self):
        return {'firewall_groups': [FIREWALL_V2]}

    def list_fwaas_firewall_policies(self):
        return {'firewall_policies': [FIREWALL_POLICY_V2]}

    def list_fwaas_firewall_rules(self):
        return {'firewall_rules': [FIREWALL_RULE_V2]}


class TestSourceNeutron(base.TestCase):
    """Basic test class"""

    def test_primitive_types_neutron(self):
        for table, (_, fields) in six.iteritems(source.NEUTRON_TABLES):
            for field, (ftype, _) in six.iteritems(fields):
                self.assertIn(
                    ftype, primitives.TYPES,
                    message="type of {} in {} is {}".format(field, table,
                                                            ftype))

    def verify(self, name):
        conn = MockNeutronCnx()
        (access_rows, fields) = source.NEUTRON_TABLES[name]
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

    def test_firewalls_v1(self):
        self.verify("firewall_v1")

    def test_firewall_policies_v1(self):
        self.verify("firewall_policy_v1")

    def test_firewall_rules_v1(self):
        self.verify("firewall_rule_v1")

    def test_firewalls(self):
        self.verify("firewall")

    def test_firewall_policies(self):
        self.verify("firewall_policy")

    def test_firewall_rules(self):
        self.verify("firewall_rule")
