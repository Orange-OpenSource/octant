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
from six.moves import reduce

from oslo_config import cfg
from skydive.rest import client as skydive_client

from octant.common import primitives


class SkydiveCnx(object):
    """Representation of skydive connection with auxiliary data"""
    __slots__ = "socket", "initialized", "filters", "actions"

    def __init__(self, socket):
        self.socket = socket
        self.initialized = False
        self.filters = {}
        self.actions = {}

    def fill(self):
        if (self.initialized):
            return
        rules = self.socket.lookup_nodes('G.V().Has("Type", "ofrule")')
        for rule in rules:
            rid = rule.id
            print(rule.metadata)
            filters = rule.metadata.get('Filters', [])
            if filters is None:
                filters = []
            filters_len = len(filters)
            for fid, filter in enumerate(filters):
                nid = fid + 1 if fid < filters_len - 1 else 65535
                key = filter["Key"]
                val = filter.get("Value", None)
                mask = filter.get("Mask", None)
                cell = self.filters.setdefault(key, [])
                cell.append((rid, fid, nid, val, mask))
            actions = rule.metadata.get('Actions', [])
            if actions is None:
                actions = []
            actions_len = len(actions)
            for aid, action in enumerate(actions):
                nid = aid + 1 if aid < actions_len - 1 else 65535
                key = action.get("Function", "")
                args = action.get("Arguments", None)
                cell = self.actions.setdefault(key, [])
                cell.append((rid, aid, nid, args))
        self.initialized = True


def _filter_filter(filter_key):
    def _action(cnx):
        cnx.fill()
        return cnx.filters.get(filter_key, [])
    return _action


def _filter_action(action_key, filter=None):
    if filter is None:
        def _action(cnx):
            cnx.fill()
            return cnx.actions.get(action_key, [])
    else:
        def _action(cnx):
            cnx.fill()
            return [
                elt for elt in cnx.actions.get(action_key, [])
                if filter(elt)]
    return _action


def _record(added_fields):
    record = {
        "rid": ("id", lambda r: r[0]),
        "id": ("int", lambda r: r[1]),
        "next": ("int", lambda r: r[2]),
    }
    record.update(added_fields)
    return record


def _filter_node(type_value):
    def _action(cnx):
        return cnx.socket.lookup_nodes(
            'G.V().Has("Type", "{}")'.format(type_value))
    return _action


def _filter_node_list(type_value, fields):
    def _action(cnx):
        nodes = cnx.socket.lookup_nodes(
            'G.V().Has("Type", "{}")'.format(type_value))
        return [
            (node.id, elt)
            for node in nodes
            for elt in reduce(lambda v, k: v.get(k, []), fields, node.metadata)
        ]
    return _action


def _filter_rel(type_value):
    def _action(cnx):
        return cnx.socket.lookup_edges(
            'G.E().Has("RelationType", "{}")'.format(type_value))
    return _action


def _metadata(field):
    if isinstance(field, list):
        return lambda node: reduce(lambda v, k: v.get(k), field, node.metadata)
    return lambda node: node.metadata[field]


def _id(node):
    return node.id


def _parent(edge):
    return edge.parent


def _child(edge):
    return edge.child


def elements_of_rule(elt, cnx):
    """Split elements of actions or filters of an Openflow rule

    :param elt: should be either 'actions' or 'filters'
    :param cnx: an open connection to Skydive
    :return: a list of string, each is an atomic action or filter.
    """
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
        _filter_node("openvswitch"),
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
    "sk_patch": (
        _filter_node("patch"),
        {
            "id": ("id", _id),
            "name": ("string", _metadata("Name")),
            "index": ("int", _metadata("OfPort")),
            "peer": ("string", _metadata(["Ovs", "Options", "peer"])),
            "mac": ("string", _metadata("MAC")),
        }
    ),
    "sk_internal": (
        _filter_node("internal"),
        {
            "id": ("id", _id),
            "name": ("string", _metadata("Name")),
            "index": ("int", _metadata("OfPort")),
            "mac": ("string", _metadata("MAC")),
        }
    ),
    "sk_internal_ip": (
        _filter_node_list("internal", ["IPV4"]),
        {
            "id": ("id", lambda p: p[0]),
            "ip": ("ip_address", lambda p: primitives.ip_of_cidr(p[1])),
            "mask": ("ip_address", lambda p: primitives.mask_of_network(p[1])),
            "prefix": (
                "ip_address",
                lambda p: primitives.prefix_of_network(p[1])),
        }
    ),
    "sk_rule": (
        _filter_node("ofrule"),
        {
            "id": ("id", _id),
            "priority": ("int", _metadata("priority")),
            "table": ("int", _metadata("table"))
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
    ),
    "of_filter_port": (
        _filter_filter("in_port"),
        _record(
            {"port": ("int", lambda r: -1 if r[3] is None else int(r[3]))})
    ),
    "of_filter_source_mac": (
        _filter_filter("dl_src"),
        _record({"mac": ("string", lambda r: r[3])})
    ),
    "of_filter_source_ip": (
        _filter_filter("nw_src"),
        _record({
            "ip": ("ip_address", lambda r: r[3]),
            "mask": (
                "ip_address",
                lambda r: u"255.255.255.255" if r[4] is None else r[4]),
        })
    ),
    "of_filter_source_port": (
        _filter_filter("dl_src"),
        _record({
            "port": ("int", lambda r: int(r[3])),
            "mask": ("int", lambda r: 65535 if r[4] is None else int(r[4])),
        })
    ),
    "of_filter_dest_mac": (
        _filter_filter("dl_dst"),
        _record({"mac": ("string", lambda r: r[3])})
    ),
    "of_filter_dest_ip": (
        _filter_filter("nw_dst"),
        _record({
            "ip": ("ip_address", lambda r: r[3]),
            "mask": (
                "ip_address",
                lambda r: u"255.255.255.255" if r[4] is None else r[4]),
        })
    ),
    "of_filter_dest_port": (
        _filter_filter("dl_dst"),
        _record({
            "port": ("int", lambda r: int(r[3])),
            "mask": ("int", lambda r: 65535 if r[4] is None else int(r[4])),
        })
    ),
    "of_action_output": (
        _filter_action("output"),
        _record({
            "port": ("int", lambda r: int(r[3][0]["Function"]))
        })
    ),
    "of_action_normal": (
        _filter_action("NORMAL"),
        _record({})
    ),
    "of_action_set_source_mac": (
        _filter_action(
            "set_field",
            filter=lambda r: r[3][2]["Function"] == "eth_src"),
        _record({
            "mac": ("string", lambda r: r[3][0]["Function"])
        })
    ),
    "of_action_set_source_ip": (
        _filter_action(
            "set_field",
            filter=lambda r: r[3][2]["Function"] == "ip_src"),
        _record({
            "ip": ("ip_address", lambda r: r[3][0]["Function"])
        })
    ),
    "of_action_set_dest_mac": (
        _filter_action(
            "set_field",
            filter=lambda r: r[3][2]["Function"] == "eth_dst"),
        _record({
            "mac": ("string", lambda r: r[3][0]["Function"])
        })
    ),
    "of_action_set_dest_ip": (
        _filter_action(
            "set_field",
            filter=lambda r: r[3][2]["Function"] == "ip_dst"),
        _record({
            "ip": ("ip_address", lambda r: r[3][0]["Function"])
        })
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
        cnx = SkydiveCnx(skydive_client.RESTClient(
            conf.endpoint, scheme=conf.scheme,
            username=conf.user_name, password=conf.password))
    datasource.register(cnx, TABLES)
