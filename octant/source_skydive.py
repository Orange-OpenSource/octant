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


def _filter_node(type_value):
    def _action(cnx):
        return cnx.lookup_nodes('G.V().Has("Type", "{}")'.format(type_value))
    return _action


def _filter_rel(type_value):
    def _action(cnx):
        return cnx.lookup_edges(
            'G.E().Has("RelationType", "{}")'.format(type_value))
    return _action


def _metadata(field):
    return lambda node: node.metadata[field]


def _id(node):
    return node.id


def _parent(edge):
    return edge.parent


def _child(edge):
    return edge.child


def elements_of_rule(elt, cnx):
    return [
        (rule.id, e, i)
        for rule in _filter_node('ofrule')(cnx)
        for i, e in enumerate(rule.metadata[elt].split(',') + ['end'])
    ]


#: Describes how to bind values extracted from the python skydive client.
TABLES = {
    "sk_host": (
        _filter_node("host"),
        {
            "id": ("id", _id),
            "name": ("string", _metadata("Name")),
            "platform": ("string", _metadata("Platform"))
        }
    ),
    "sk_ovsswitch": (
        _filter_node("ovsswitch"),
        {
            "id": ("id", _id),
            "name": ("string", _metadata("Name")),
        }
    ),
    "sk_ovsbridge": (
        _filter_node("ovsbridge"),
        {
            "id": ("id", _id),
            "name": ("string", _metadata("Name")),
        }
    ),
    "sk_ovsport": (
        _filter_node("ovsport"),
        {
            "id": ("id", _id),
            "name": ("string", _metadata("Name")),
        }
    ),
    "sk_rule": (
        _filter_node("ofrule"),
        {
            "id": ("id", _id),
            "priority": ("int", _metadata("priority")),
            "table": ("int", _metadata("table")),
            "filters": ("string", _metadata("filters")),
            "actions": ("string", _metadata("actions")),
        }
    ),
    "sk_filter": (
        lambda cnx: elements_of_rule("filters", cnx),
        {
            "id": ("id", lambda t: t[0]),
            "element": ("string", lambda t: t[1]),
            "position": ("int", lambda t: t[2])
        }
    ),
    "sk_action": (
        lambda cnx: elements_of_rule("actions", cnx),
        {
            "id": ("id", lambda t: t[0]),
            "element": ("string", lambda t: t[1]),
            "position": ("int", lambda t: t[2])
        }
    ),
    "sk_owns": (
        _filter_rel("ownership"),
        {
            "owner": ("id", _parent),
            "item": ("id", _child)
        }
    ),
    "sk_l2": (
        _filter_rel("layer2"),
        {
            "a": ("id", _parent),
            "b": ("id", _child)
        }
    )
}


def register(datasource):
    """Registers Skydive tables in the datasource

    :param datasource: a datasource object to enrich
    """
    conf = cfg.CONF.skydive
    if not conf.enabled:
        return
    if datasource.use_cache():
        cnx = None
    else:
        cnx = skydive_client.RESTClient(
            conf.endpoint, scheme=conf.scheme,
            username=conf.user_name, password=conf.password)
    datasource.register(cnx, TABLES)
