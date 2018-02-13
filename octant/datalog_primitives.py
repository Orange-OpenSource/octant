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


def get_subnets(conn):
    return conn.network.subnets()


def get_routers(conn):
    return conn.network.routers()


def get_acl(conn):
    return conn.network.security_groups()


def get_servers(conn):
    return conn.compute.servers()


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
    "subnet": (get_subnets, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "network_id": ("id", lambda p: p.network_id),
        "project_id": ("id", lambda p: p.project_id),
        "ip_version": ("int", lambda s: s.ip_version)
    }),
    "acl": (get_acl, {
        "id": ("id", lambda p: p.id),
        "name": ("string", lambda p: p.name),
        "project_id": ("id", lambda p: p.project_id),
    }),
    "server": (get_servers, {
        "id": ("id", lambda s: s.id),
        "project_id": ("id", lambda s: s.project_id),
        "name": ("string", lambda s: s.name),
        "host": ("string", lambda s: s.hypervisor_hostname)
    })
}


def is_primitive_atom(atom):
    "Check if a atom refers to a primitive table."
    return atom.table in TABLES
