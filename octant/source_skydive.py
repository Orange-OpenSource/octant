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

"""Skydive Data Source"""

from oslo_config import cfg
from skydive.rest import client as skydive_client


def filter_node(type_value):
    def filter(cnx):
        return cnx.lookup_nodes('G.V().Has("Type", "{}")'.format(type_value))
    return filter


def filter_rel(type_value):
    def filter(cnx):
        return cnx.lookup_edges(
            'G.E().Has("RelationType", "{}")'.format(type_value))
    return filter


def metadata(field):
    return lambda x: x.metadata[field]


def id(x):
    return x.id


def parent(x):
    return x.parent


def child(x):
    return x.child


TABLE = {
    "sk_host": (
        filter_node("host"),
        {
            "id": ("id", id),
            "name": ("string", metadata("Name")),
            "platform": ("string", metadata("Platform"))
        }
    ),
    "sk_ovsbridge": (
        filter_node("ovsbridge"),
        {
            "id": ("id", id),
            "name": ("string", metadata("Name")),
        }
    ),
    "sk_ovsport": (
        filter_node("ovsport"),
        {
            "id": ("id", id),
            "name": ("string", metadata("Name")),
        }
    ),
    "sk_owns": (
        filter_rel("ownership"),
        {
            "owner": ("id", parent),
            "item": ("id", child)
        }
    ),
    "sk_layer2": (
        filter_rel("layer2"),
        {
            "src": ("id", parent),
            "dst": ("id", child)
        }
    )
}


def register(datasource):
    conf = cfg.CONF.skydive
    if not conf.enabled:
        return
    if datasource.use_cache():
        cnx = None
    else:
        cnx = skydive_client.RESTClient(
            conf.endpoint, scheme=conf.scheme,
            username=conf.user_name, password=conf.password)
    datasource.register(cnx, TABLE)
