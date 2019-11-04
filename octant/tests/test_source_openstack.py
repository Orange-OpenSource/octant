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

from octant import primitives
from octant.source import openstack_source as source
from octant.source import source as datasource
from octant.tests import base


NETWORK = {
    'updated_at': u'2018-06-04T07:56:21Z',
    'dns_domain': None, 'provider_physical_network': u'public',
    'is_vlan_transparent': None, 'revision_number': 6,
    'ipv4_address_scope_id': None,
    'id': u'df5e1ef1-072e-4469-84e0-acc3bcb6de59',
    'availability_zone_hints': [], 'availability_zones': [u'nova'],
    'segments': None, 'location': None,
    'project_id': u'99f9abddf0b44720b97ee8c3d188c294',
    'ipv6_address_scope_id': None, 'status': u'ACTIVE', 'description': u'',
    'provider_network_type': u'flat', 'tags': [], 'is_router_external': True,
    'is_default': True, 'is_port_security_enabled': True,
    'subnet_ids': [u'e42a9354-59d7-405e-b8b8-9d02b80cf42b'], 'name': u'public',
    'qos_policy_id': None, 'created_at': u'2018-06-04T07:56:14Z', 'mtu': 1500,
    'provider_segmentation_id': None, 'is_admin_state_up': True,
    'is_shared': False}

PORT = {
    'binding_vif_details': {
        u'port_filter': True, u'datapath_type': u'system',
        u'ovs_hybrid_plug': True},
    'allowed_address_pairs': [],
    'extra_dhcp_opts': [], 'updated_at': u'2018-06-04T07:56:09Z',
    'dns_domain': None, 'device_owner': u'network:dhcp', 'revision_number': 6,
    'fixed_ips': [{
        u'subnet_id': u'6f27f6d7-e15a-48a0-8047-04ba9e9b661e',
        u'ip_address': u'10.0.0.2'}],
    'id': u'2874cfad-8dba-4f72-8f19-6bedfa2c9014', 'option_value': None,
    'binding_vnic_type': u'normal', 'option_name': None,
    'qos_policy_id': None, 'location': None,
    'mac_address': u'fa:16:3e:91:d0:d4',
    'project_id': u'472c305320fc4fa693c33bfda4eb334e', 'status': u'ACTIVE',
    'binding_profile': {}, 'binding_vif_type': u'ovs', 'description': u'',
    'tags': [], 'dns_assignment': None, 'trunk_details': None,
    'is_port_security_enabled': False, 'security_group_ids': [],
    'ip_address': None,
    'device_id': (u'dhcpaea584fe-b4b5-576a-b7fa-bbc70b1e4935-'
                  u'f2c16d38-0c78-4704-8e8d-50f34ad1293c'),
    'name': u'', 'network_id': u'f2c16d38-0c78-4704-8e8d-50f34ad1293c',
    'dns_name': None, 'created_at': u'2018-06-04T07:56:05Z', 'subnet_id': None,
    'data_plane_status': None, 'binding_host_id': u'ds1',
    'is_admin_state_up': True}

SUBNET = {
    'updated_at': u'2018-06-04T07:56:04Z', 'ipv6_ra_mode': None,
    'allocation_pools': [{u'start': u'10.0.0.2', u'end': u'10.0.0.62'}],
    'host_routes': [], 'revision_number': 0, 'ipv6_address_mode': None,
    'id': u'6f27f6d7-e15a-48a0-8047-04ba9e9b661e', 'dns_nameservers': [],
    'use_default_subnet_pool': None, 'gateway_ip': u'10.0.0.1',
    'location': None, 'project_id': u'472c305320fc4fa693c33bfda4eb334e',
    'description': u'', 'tags': [], 'is_dhcp_enabled': True,
    'service_types': [], 'cidr': u'10.0.0.0/26',
    'subnet_pool_id': u'a105931d-940e-40ed-b0c1-da72036a21f0',
    'name': u'private-subnet', 'segment_id': None,
    'network_id': u'f2c16d38-0c78-4704-8e8d-50f34ad1293c',
    'created_at': u'2018-06-04T07:56:04Z', 'ip_version': 4}

ROUTER = {
    'created_at': u'2018-04-10T16:08:04Z', 'availability_zones': ['nova'],
    'name': u'router1', 'availability_zone_hints': [], 'description': u'',
    'revision_number': 4, 'status': u'ACTIVE', 'tags': [],
    'project_id': u'efc93c8fdbf4405ba23837c146dfffac', 'location': None,
    'routes': [], 'is_admin_state_up': True,
    'updated_at': u'2018-04-10T16:08:20Z', 'flavor_id': None,
    'id': u'c5a7c205-e4e6-48b5-bc35-7c9247f23f37',
    'external_gateway_info': {
        'external_fixed_ips': [{
            'ip_address': u'172.24.4.4',
            'subnet_id': u'47633dbf-34e0-436b-9f3e-7570c31efdf6'}],
        'enable_snat': True,
        'network_id': u'357e4466-0cea-4666-8a3d-609ebafc6dae'},
    'is_ha': False, 'is_distributed': False}

SUBNET_POOL = {
    'created_at': u'2018-04-10T16:07:52Z', 'revision_number': 0,
    'name': u'shared-default-subnetpool-v4', 'maximum_prefix_length': 32,
    'is_shared': True, 'tags': [], 'default_prefix_length': 26,
    'prefixes': ['10.0.0.0/22'], 'description': u'', 'default_quota': None,
    'address_scope_id': None,
    'project_id': u'df9f12278aa24c288530b1c0fd5b98e7',
    'is_default': True, 'minimum_prefix_length': 8,
    'updated_at': u'2018-04-10T16:07:52Z',
    'id': u'47a890da-1bef-4849-9652-c809db1b07f8', 'location': None,
    'ip_version': 4}

SECURITY_GROUP = {
    'created_at': u'2018-04-10T16:07:52Z', 'revision_number': 4,
    'project_id': u'df9f12278aa24c288530b1c0fd5b98e7', 'name': u'default',
    'tags': [], 'updated_at': u'2018-04-10T16:07:52Z',
    'id': u'964f1abb-4347-4a34-9f58-bd8ec4409f92',
    'description': u'Default security group',
    'security_group_rules': [
        {'revision_number': 0, 'tags': [],
         'remote_group_id': u'964f1abb-4347-4a34-9f58-bd8ec4409f92',
         'tenant_id': u'df9f12278aa24c288530b1c0fd5b98e7',
         'remote_ip_prefix': None,
         'security_group_id': u'964f1abb-4347-4a34-9f58-bd8ec4409f92',
         'ethertype': u'IPv6', 'description': None, 'direction': u'ingress',
         'protocol': None, 'created_at': u'2018-04-10T16:07:52Z',
         'project_id': u'df9f12278aa24c288530b1c0fd5b98e7',
         'port_range_min': None, 'updated_at': u'2018-04-10T16:07:52Z',
         'id': u'd73f1c21-8c34-48e4-bc21-ff76b182c0d7',
         'port_range_max': None},
        {'revision_number': 0, 'tags': [], 'remote_group_id': None,
         'tenant_id': u'df9f12278aa24c288530b1c0fd5b98e7',
         'remote_ip_prefix': None,
         'security_group_id': u'964f1abb-4347-4a34-9f58-bd8ec4409f92',
         'ethertype': u'IPv4', 'description': None, 'direction': u'egress',
         'protocol': None, 'created_at': u'2018-04-10T16:07:52Z',
         'project_id': u'df9f12278aa24c288530b1c0fd5b98e7',
         'port_range_min': None, 'updated_at': u'2018-04-10T16:07:52Z',
         'id': u'9988bd56-d3fc-4aba-8ee7-25bb2792695a',
         'port_range_max': None},
        {'revision_number': 0, 'tags': [], 'remote_group_id': None,
         'tenant_id': u'df9f12278aa24c288530b1c0fd5b98e7',
         'remote_ip_prefix': None,
         'security_group_id': u'964f1abb-4347-4a34-9f58-bd8ec4409f92',
         'ethertype': u'IPv6', 'description': None, 'direction': u'egress',
         'protocol': None, 'created_at': u'2018-04-10T16:07:52Z',
         'project_id': u'df9f12278aa24c288530b1c0fd5b98e7',
         'port_range_min': None, 'updated_at': u'2018-04-10T16:07:52Z',
         'id': u'1aff303a-c5b8-4449-b40f-8e729dc2b714',
         'port_range_max': None},
        {'revision_number': 0, 'tags': [],
         'remote_group_id': u'964f1abb-4347-4a34-9f58-bd8ec4409f92',
         'tenant_id': u'df9f12278aa24c288530b1c0fd5b98e7',
         'remote_ip_prefix': None,
         'security_group_id': u'964f1abb-4347-4a34-9f58-bd8ec4409f92',
         'ethertype': u'IPv4', 'description': None, 'direction': u'ingress',
         'protocol': None, 'created_at': u'2018-04-10T16:07:52Z',
         'project_id': u'df9f12278aa24c288530b1c0fd5b98e7',
         'port_range_min': None, 'updated_at': u'2018-04-10T16:07:52Z',
         'id': u'f4734fc7-a094-4d37-8403-7573a2e8020b',
         'port_range_max': None}],
    'location': None}

SECURITY_GROUP_RULE = {
    'created_at': u'2018-04-10T16:08:19Z', 'revision_number': 0,
    'remote_group_id': None, 'name': None, 'remote_ip_prefix': None,
    'description': None,
    'security_group_id': u'de1ad55b-372e-430d-a87b-607f5ca8a873',
    'port_range_min': None, 'protocol': None, 'project_id': u'',
    'ether_type': u'IPv6', 'updated_at': u'2018-04-10T16:08:19Z',
    'id': u'107f2fc6-7206-4f7b-8cd8-5949a2e30ad8', 'location': None,
    'port_range_max': None, 'direction': u'egress'}

PROJECT = {
    'is_enabled': True, 'is_domain': False,
    'description': u'', 'id': u'2b50c40933b0436095a3a2e9c5f82cd6',
    'parent_id': u'default', 'location': None, 'domain_id': u'default',
    'name': u'service'}

SERVER = {
    'attached_volumes': [], 'vm_state': u'active',
    'addresses': {
        u'private': [
            {u'OS-EXT-IPS-MAC:mac_addr': u'fa:16:3e:29:72:04', u'version': 4,
             u'addr': u'10.0.0.12', u'OS-EXT-IPS:type': u'fixed'}]},
    'links': [
        {u'href': u'http://192.168.122.10/compute/v2.1/servers/'
                  u'6978be7e-8719-4980-b11f-7b77b26c2557',
         u'rel': u'self'},
        {u'href': u'http://192.168.122.10/compute/servers/'
                  u'6978be7e-8719-4980-b11f-7b77b26c2557',
         u'rel': u'bookmark'}],
    'availability_zone': u'nova', 'terminated_at': None,
    'image': {
        u'id': u'dea11fb2-0dc7-4e32-8790-c9939e80aab2',
        u'links': [{
            u'href': u'http://192.168.122.10/compute/images/'
                     u'dea11fb2-0dc7-4e32-8790-c9939e80aab2',
            u'rel': u'bookmark'}]},
    'user_data': None,
    'flavor': {
        u'id': u'42',
        u'links': [{u'href': u'http://192.168.122.10/compute/flavors/42',
                    u'rel': u'bookmark'}]},
    'networks': None, 'security_groups': [{u'name': u'default'}],
    'scheduler_hints': None, 'has_config_drive': u'',
    'user_id': u'c68baee4759f428dbc48d3f9e7d70aec', 'disk_config': u'AUTO',
    'id': u'6978be7e-8719-4980-b11f-7b77b26c2557', 'admin_password': None,
    'power_state': 3, 'progress': 0,
    'project_id': u'472c305320fc4fa693c33bfda4eb334e',
    'launched_at': u'2018-06-04T12:08:47.000000', 'personality': None,
    'status': u'ACTIVE', 'block_device_mapping': None, 'key_name': None,
    'hypervisor_hostname': u'ds1', 'updated_at': u'2018-06-04T12:08:47Z',
    'image_id': None,
    'host_id': u'cf0f29687850b675bdcfd4b6304d21e132eb089569ed755d05c74f41',
    'task_state': None, 'name': u'I1', 'access_ipv6': u'', 'access_ipv4': u'',
    'created_at': u'2018-06-04T12:08:32Z', 'location': None,
    'instance_name': u'instance-00000001', 'flavor_id': None, 'metadata': {}
}

FLAVOR = {
    'links': [
        {'rel': u'self',
         'href': u'http://192.168.122.10/compute/v2.1/flavors/1'},
        {'rel': u'bookmark',
         'href': u'http://192.168.122.10/compute/flavors/1'}
    ],
    'name': u'm1.tiny', 'vcpus': 1, 'ephemeral': 0, 'is_public': True,
    'rxtx_factor': 1.0, 'swap': u'', 'location': None, 'is_disabled': False,
    'ram': 512, 'disk': 1, 'id': u'1'}

IMAGE = {
    'created_at': u'2018-04-10T16:07:27Z', 'metadata': {},
    'links': [
        {'rel': u'self',
         'href': ('http://192.168.122.10/compute/v2.1/images/'
                  'e5cfee51-e6d5-4ae3-bfa1-f04c21a4918c')},
        {'rel': u'bookmark',
         'href': ('http://192.168.122.10/compute/images/'
                  'e5cfee51-e6d5-4ae3-bfa1-f04c21a4918c')},
        {'type': u'application/vnd.openstack.image', 'rel': u'alternate',
         'href': ('http://192.168.122.10/image/images/'
                  'e5cfee51-e6d5-4ae3-bfa1-f04c21a4918c')}],
    'name': u'cirros-0.3.5-x86_64-disk', 'min_ram': 0, 'min_disk': 0,
    'status': u'ACTIVE', 'location': None, 'progress': 100, 'size': 13267968,
    'updated_at': u'2018-04-10T16:07:27Z',
    'id': u'e5cfee51-e6d5-4ae3-bfa1-f04c21a4918c'}

USER = {
    'is_enabled': True, 'password_expires_at': None,
    'links': {
        u'self': (u'http://192.168.122.10/identity/v3/'
                  u'users/015c833678354396ae3f864581c7dab3')},
    'location': None, 'name': u'nova', 'email': None,
    'default_project_id': None, 'id': u'015c833678354396ae3f864581c7dab3',
    'password': None, 'domain_id': u'default', 'description': None}

GROUP = {
    'id': u'0fa7edf70be642a9ac0c654e758dc408', 'location': None,
    'description': u'non-admin group', 'name': u'nonadmins',
    'domain_id': u'default'}

REGION = {
    'parent_region_id': None, 'name': None,
    'links': {
        u'self': u'http://192.168.122.10/identity/v3/regions/RegionOne'},
    'location': None, 'id': u'RegionOne', 'description': u''
}

DOMAIN = {
    'is_enabled': True, 'description': u'The default domain',
    'links': {u'self': u'http://192.168.122.10/identity/v3/domains/default'},
    'location': None, 'id': u'default', 'name': u'Default'
}

ROLE = {
    'location': None, 'name': u'service',
    'links': {
        u'self': (u'http://192.168.122.10/identity/v3/roles/'
                  u'00d9a0e5005649fda0b5c1b19882027f')},
    'id': u'00d9a0e5005649fda0b5c1b19882027f'
}

SERVICE = {
    'is_enabled': True, 'description': u'Placement Service',
    'links': {
        u'self': u'http://192.168.122.10/identity/v3/services'
                 u'/117e70b8090e440d9d54a0f25fb7099b'},
    'location': None, 'type': u'placement',
    'id': u'117e70b8090e440d9d54a0f25fb7099b', 'name': u'placement'
}

ENDPOINT = {
    'is_enabled': True, 'region_id': u'RegionOne',
    'links': {
        u'self': u'http://192.168.122.10/identity/v3/endpoints/'
                 u'3d367a0889fc4d91a2efef834e28b8c4'},
    'url': u'http://192.168.122.10/identity', 'location': None,
    'interface': u'public',
    'service_id': u'202929e3496540858792dc6d64b0cf19',
    'id': u'3d367a0889fc4d91a2efef834e28b8c4', 'name': None
}

ROLE_ASSIGNMENT = {
    'group': None, 'name': None,
    'links': {
        u'assignment': u'http://192.168.122.10/identity/v3/projects/'
                       u'2b50c40933b0436095a3a2e9c5f82cd6/users/'
                       u'015c833678354396ae3f864581c7dab3/roles/'
                       u'00d9a0e5005649fda0b5c1b19882027f'},
    'role': {u'id': u'00d9a0e5005649fda0b5c1b19882027f'},
    'user': {u'id': u'015c833678354396ae3f864581c7dab3'},
    'scope': {u'project': {u'id': u'2b50c40933b0436095a3a2e9c5f82cd6'}},
    'id': None, 'location': None
}


class AttrDict(dict):
    def __init__(self, *args, **kwargs):
        super(AttrDict, self).__init__(*args, **kwargs)
        self.__dict__ = self


class MockNetwork(object):
    def networks(self):
        return (AttrDict(x) for x in [NETWORK])

    def ports(self):
        return (AttrDict(x) for x in [PORT])

    def routers(self):
        return (AttrDict(x) for x in [ROUTER])

    def subnets(self):
        return (AttrDict(x) for x in [SUBNET])

    def subnet_pools(self):
        return (AttrDict(x) for x in [SUBNET_POOL])

    def address_scopes(self):
        return (AttrDict(x) for x in [])

    def security_groups(self):
        return (AttrDict(x) for x in [SECURITY_GROUP])

    def security_group_rules(self):
        return (AttrDict(x) for x in [SECURITY_GROUP_RULE])


class MockCompute(object):

    def servers(self, all_tenants=False):
        return (AttrDict(x) for x in [SERVER])

    def flavors(self):
        return (AttrDict(x) for x in [FLAVOR])

    def images(self):
        return (AttrDict(x) for x in [IMAGE])


class MockIdentity(object):

    def projects(self):
        return (AttrDict(x) for x in [PROJECT])

    def users(self):
        return (AttrDict(x) for x in [USER])

    def groups(self):
        return (AttrDict(x) for x in [GROUP])

    def regions(self):
        return (AttrDict(x) for x in [REGION])

    def domains(self):
        return (AttrDict(x) for x in [DOMAIN])

    def roles(self):
        return (AttrDict(x) for x in [ROLE])

    def services(self):
        return (AttrDict(x) for x in [SERVICE])

    def endpoints(self):
        return (AttrDict(x) for x in [ENDPOINT])

    def role_assignments(self):
        return (AttrDict(x) for x in [ROLE_ASSIGNMENT])


class MockSession(object):

    def __init__(self):
        self.identity = MockIdentity()
        self.compute = MockCompute()
        self.network = MockNetwork()


class TestSourceOpenstack(base.TestCase):
    """Basic test class"""

    def test_primitive_types_openstack(self):
        for table, (_, fields) in six.iteritems(source.OPENSTACK_TABLES):
            for field, (ftype, _) in six.iteritems(fields):
                self.assertIn(
                    ftype, primitives.TYPES,
                    message="type of {} in {} is {}".format(field, table,
                                                            ftype))

    def verify(self, name):
        conn = MockSession()
        (access_rows, fields) = source.OPENSTACK_TABLES[name]
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

    def test_networks(self):
        self.verify("network")

    def test_ports(self):
        self.verify("port")

    def test_port_ips(self):
        self.verify("port_ip")

    def test_port_sg(self):
        self.verify("port_sg")

    def test_routers(self):
        self.verify("router")

    def test_routers_routes(self):
        self.verify("router_route")

    def test_subnets(self):
        self.verify("subnet")

    def test_subnet_route(self):
        self.verify("subnet_route")

    def test_subnet_pools(self):
        self.verify("subnet_pool")

    def test_subnet_pool_prefix(self):
        self.verify("subnet_pool_prefixes")

    def test_security_groups(self):
        self.verify("sg")

    def test_security_group_rules(self):
        self.verify("rule")

    @mock.patch("oslo_config.cfg.CONF")
    def test_servers(self, mock_conf):
        mock_conf.all_projects = True
        self.verify("server")

    def test_flavor(self):
        self.verify("flavor")

    def test_image(self):
        self.verify("image")

    def test_project(self):
        self.verify("project")

    def test_region(self):
        self.verify("region")

    def test_domain(self):
        self.verify("domain")

    def test_role(self):
        self.verify("role")

    def test_user(self):
        self.verify("user")

    def test_service(self):
        self.verify("service")

    def test_endpoint(self):
        self.verify("endpoint")

    def test_group(self):
        self.verify("group")

    def test_role_assignment(self):
        self.verify("role_assignment")

    @mock.patch("urllib3.disable_warnings")
    @mock.patch("getpass.getpass")
    @mock.patch("keystoneauth1.identity.Password")
    @mock.patch("keystoneauth1.session.Session")
    @mock.patch("neutronclient.v2_0.client.Client")
    @mock.patch("openstack.connection.Connection")
    @mock.patch("oslo_config.cfg.CONF")
    def test_register(self, mock_conf, mock_client_os, mock_client_neutron,
                      mock_session, mock_identity, mock_getpass, mock_disable):
        mock_list = [
            mock_client_os, mock_client_neutron, mock_session, mock_identity,
            mock_getpass, mock_disable]
        mock_conf.openstack.enabled = False
        mock_conf.openstack.password = ""
        mock_conf.openstack.verify = False
        mock_conf.restore = None
        src = datasource.Datasource(primitives.TYPES)
        source.register(src)
        for mck in mock_list:
            mck.assert_not_called()
        mock_conf.openstack.enabled = True
        mock_conf.restore = "file_path"
        source.register(src)
        for mck in mock_list:
            mck.assert_not_called()
        mock_conf.restore = None
        source.register(src)
        for mck in mock_list:
            mck.assert_called_once()

    def test_port_min(self):
        self.assertEqual(0, source.port_min(None))
        self.assertEqual(2, source.port_min(2))
        self.assertEqual(3, source.port_min('3'))
        self.assertEqual(4, source.port_min('4:7'))

    def test_port_max(self):
        self.assertEqual(65535, source.port_max(None))
        self.assertEqual(2, source.port_max(2))
        self.assertEqual(3, source.port_max('3'))
        self.assertEqual(4, source.port_max('1:4'))

    def test_normalize_status(self):
        self.assertEqual('active', source.normalize_status('ACTIVE'))
        self.assertEqual('down', source.normalize_status('Down'))
        self.assertEqual('other', source.normalize_status('foobar'))

    def test_fw_action(self):
        self.assertEqual('allow', source.fw_action('ALLOW'))
        self.assertEqual('deny', source.fw_action('deny'))
        self.assertEqual('other', source.fw_action('foobar'))
