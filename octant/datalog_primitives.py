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


def get_networks(conn):
    return conn.network.networks()


def get_ports(conn):
    return conn.network.ports()


def get_port_ips(conn):
    return (
        (p.id, fixed_ip)
        for p in conn.network.ports()
        for fixed_ip in p.fixed_ips)


def get_port_sgs(conn):
    return (
        (p.id, sg_id)
        for p in conn.network.ports()
        for sg_id in p.security_group_ids
    )


def get_subnets(conn):
    return conn.network.subnets()


def get_subnet_pools(conn):
    return conn.network.subnet_pools()


def get_address_scopes(conn):
    return conn.network.address_scopes()


def get_subnet_pool_prefixes(conn):
    return (
        (snp.id, prefix)
        for snp in conn.network.subnet_pools()
        for prefix in snp.prefixes)


def get_routers(conn):
    return conn.network.routers()


def get_sg(conn):
    return conn.network.security_groups()


def get_security_group_rules(conn):
    return conn.network.security_group_rules()


def get_servers(conn):
    return conn.compute.servers()


def get_flavors(conn):
    return conn.compute.flavors()


def get_images(conn):
    return conn.image.images()


def get_roles(conn):
    return conn.identity.roles()


def get_projects(conn):
    return conn.identity.projects()


def get_domains(conn):
    return conn.identity.domains()


def get_users(conn):
    return conn.identity.users()


def get_regions(conn):
    return conn.identity.regions()


def get_services(conn):
    return conn.identity.services()


def get_groups(conn):
    return conn.identity.groups()


def get_endpoints(conn):
    return conn.identity.endpoints()


def get_role_assignments(conn):
    return conn.identity.role_assignments()


def hide_none(c):
    "" if c is None else c


def _project_scope(p):
    return hide_none(
        p.scope['project']['id']
        if p.scope is not None and p.scope['project'] is not None
        else None)


# Describes how to bind values extracted from the to Python table.
TABLES = {
    "network": (get_networks, {
        "id": ("id", lambda n: n.id),
        "project_id": ("id", lambda n: n.project_id),
        "name": ("string", lambda n: n.name)
    }),
    "router": (get_routers, {
        "id": ("id", lambda r: r.id),
        "project_id": ("id", lambda r: r.project_id),
        "status": ("string", lambda r: r.status),
        "name": ("string", lambda r: r.name)
    }),
    "port": (get_ports, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "host": ("string", lambda p: p.binding_host_id),
        "network_id": ("id", lambda p: p.network_id),
        "project_id": ("id", lambda p: p.project_id),
        "device_id": ("id", lambda p: p.device_id),
        "status": ("string", lambda p: p.status)
    }),
    "subnet_pool": (get_subnet_pools, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "ip_version": ("int", lambda s: s.ip_version),
        "project_id": ("id", lambda p: p.project_id),
        "address_scope_id": ("id", lambda p: hide_none(p.address_scope_id)),
    }),
    "subnet_pool_prefixes": (get_subnet_pool_prefixes, {
        "id": ("id", lambda p: p[0]),
        "prefix": ("string", lambda p: p[1])
    }),
    "address_scope": (get_address_scopes, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
    }),
    "port_ip": (get_port_ips, {
        "port_id": ("id", lambda pi: pi[0]),
        "subnet_id": ("id", lambda pi: pi[1]['subnet_id']),
        "ip": ("string", lambda pi: pi[1]['ip_address']),
    }),
    "port_sg": (get_port_sgs, {
        "port_id": ("id", lambda psg: psg[0]),
        "sg_id": ("id", lambda psg: psg[1]),
    }),
    "subnet": (get_subnets, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "network_id": ("id", lambda p: p.network_id),
        "project_id": ("id", lambda p: p.project_id),
        "ip_version": ("int", lambda s: s.ip_version)
    }),
    "sg": (get_sg, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "project_id": ("id", lambda p: p.project_id),
    }),
    "rule": ((get_security_group_rules, {
        "id": ("id", lambda p: p.id),
        "direction": ("string", lambda p: p.direction),
        "ip_version": ("int", (
            lambda p: 4 if p.ether_type == 'IPv4' else 6
        )),
        "port_range_max": ("int", (
            lambda p: 65536 if p.port_range_max is None else p.port_range_max
        )),
        "port_range_min": ("int", (
            lambda p: 0 if p.port_range_min is None else p.port_range_min
        )),
        "protocol": ("string", (lambda p: hide_none(p.protocol))),
        "project_id": ("id", lambda p: p.project_id),
        "remote_group_id": ("id", lambda p: hide_none(p.remote_group_id)),
        "remote_ip_prefix": ("string", (
            lambda p: hide_none(p.remote_ip_prefix)
        )),
        "security_group_id": ("id", lambda p: p.security_group_id)
    })),
    "server": (get_servers, {
        "id": ("id", lambda s: s.id),
        "project_id": ("id", lambda s: s.project_id),
        "name": ("string", lambda s: s.name),
        "host": ("string", lambda s: s.hypervisor_hostname),
        "image_id": ("id", lambda s: s.image['id']),
        "flavor_id": ("id", lambda s: s.flavor['id'])
    }),
    "flavor": (get_flavors, {
        "id": ("id", lambda f: f.id),
        "name": ("string", lambda f: f.name),
        "vcpus": ("int", lambda f: f.vcpus),
        "ram": ("int", lambda f: f.ram),
        "disk": ("int", lambda f: f.disk),
        "public": ("bool", lambda f: f.is_public)
    }),
    "image": (get_images, {
        "id": ("id", lambda f: f.id),
        "name": ("string", lambda f: f.name),
    }),
    "project": (get_projects, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "domain_id": ("id", lambda p: p.domain_id),
        "parent_id": ("id", (lambda p: hide_none(p.parent_id)))
    }),
    "region": (get_regions, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "parent_id": ("id", (lambda p: hide_none(p.parent_region_id))),
    }),
    "domain": (get_domains, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name)
    }),
    "role": (get_roles, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name)
    }),
    "user": (get_users, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "domain_id": ("id", lambda p: p.domain_id)
    }),
    "service": (get_services, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "type": ("string", lambda p: p.type)
    }),
    "endpoint": (get_endpoints, {
        "id": ("id", lambda p: p.id),
        "url": ("string", lambda p: p.url),
        "interface": ("string", lambda p: p.interface),
        "service_id": ("id", lambda p: p.sevice_id),
        "region_id": ("id", lambda p: p.region_id)
    }),
    "group": (get_groups, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "domain_id": ("id", lambda p: p.domain_id)
    }),
    "role_assignment": (get_role_assignments, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "group_id": ("id", (
            lambda p: hide_none(p.group['id'] if p.group is not None else None)
        )),
        "role_id": ("id", lambda p: p.role['id']),
        "project_id": ("id", _project_scope),
        "user_id": ("id", (
            lambda p: hide_none(p.user['id'] if p.user is not None else None)
        ))
    })
}


def is_primitive_atom(atom):
    "Check if a atom refers to a primitive table."
    return atom.table in TABLES
