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

'''Skydive Data Source'''

from __future__ import print_function

import re

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
    '''Split elements of actions or filters of an Openflow rule

    :param elt: should be either 'actions' or 'filters'
    :param cnx: an open connection to Skydive
    :return: a list of rule identifier, position and string. Each string
       is an atomic action or filter.
    '''
    return [
        (rule.id, i, e)
        for rule in _filter_node('ofrule')(cnx)
        for i, e in enumerate(rule.metadata[elt].split(',') + ['end'])
    ]


NUM = ('([0-9]+|0x[0-9a-f]+)')
ADDR = (
    '((?:[0-9a-f]{2}[:-]){5}[0-9a-f]{2}|(?:[0-9]+[.]){3}[0-9]+)')

RE_MATCH_NUM_FIELD = re.compile('^([a-z_]*)=' + NUM + '(?:/' + NUM + ')?$')

RE_MATCH_ADDR_FIELD = re.compile('^([a-z_]*)=' + ADDR + '(?:/' + ADDR + ')?$')

PROTO_SHORTHANDS = {
    'ip': (0x800, None),
    'ipv6': (0x86dd, None),
    'icmp': (0x0800, 1),
    'icmp6': (0x86dd, 58),
    'tcp': (0x0800, 6),
    'tcp6': (0x86dd, 6),
    'udp': (0x0800, 17),
    'udp6': (0x86dd, 17),
    'sctp': (0x0800, 132),
    'sctp6': (0x86dd, 132),
    'arp': (0x0806, None),
    'rarp': (0x8035, None),
    'mpls': (0x8847, None),
    'mplsm': (0x8848, None),
}

FILTER_FIELDS = [
    'eth_type', 'ip_proto', 'in_port', 'end', 'dl_vlan', 'tunnel_id',
    'tun_src', 'tun_dst', 'tun_ipv6_src', 'tun_ipv6_dst', 'tun_flags',
    'dl_src', 'dl_dst', 'nw_src', 'nw_dst', 'tp_src', 'tp_dst',
    'vlan_tci', 'unknown'
]


def preprocess_filters(cnx):
    """Parse openflow filters

    This function prepares a structure used by individual datalog filter table
    to extract the relevant filters from all the openflow rules.

    All the rules filter lists terminate with an 'end' element.

    :param cnx: a connection to a skydive analyzer
    :return: a structure where each field contains a description of all the
       atomic filters using the operation described by the field name.
       Each element in the lists is a tuple where the first two elements are
       the rule id and the position of the element in the filters of the rule.
    """
    prepared_filters = [
        (rule.id, rule.metadata['filters'].split(',') + ['end'])
        for rule in _filter_node('ofrule')(cnx)
    ]
    result = {}
    for field in FILTER_FIELDS:
        result[field] = []

    for (rule_id, elt_list) in prepared_filters:
        pos = 0
        for elt in elt_list:
            # Better ensure immunity to capitalization
            elt = elt.lower()
            if elt.startswith('priority='):
                continue
            if elt == 'end':
                result['end'].append((rule_id, pos))
                pos = pos + 1
                continue
            if elt in PROTO_SHORTHANDS:
                (eth_type, ip_proto) = PROTO_SHORTHANDS[elt]
                result['eth_type'].append((rule_id, pos, eth_type))
                if ip_proto is not None:
                    result['ip_proto'].append((rule_id, pos + 1, ip_proto))
                    pos = pos + 2
                else:
                    pos = pos + 1
                continue
            matched = RE_MATCH_NUM_FIELD.match(elt)
            if matched:
                field = matched.group(1)
                val = matched.group(2)
                mask = matched.group(3)
                if field in result:
                    result[field].append((
                        rule_id, pos, int(val, 0),
                        None if mask is None else int(mask, 0)))
                    pos = pos + 1
                    continue
                else:
                    print('forgotten key ' + elt)
            matched = RE_MATCH_ADDR_FIELD.match(elt)
            if matched:
                field = matched.group(1)
                val = matched.group(2)
                mask = matched.group(3)
                if field in result:
                    result[field].append((
                        rule_id, pos, val,
                        None if mask is None else mask))
                    pos = pos + 1
                    continue
                else:
                    print('forgotten key' + elt)
            result['unknown'].append((rule_id, pos, elt))
            pos = pos + 1

    return result


PORT_SHORTHANDS = {
    'any': -1, 'local': -2, 'controller': -3, 'all': -4,
    'flood': -5, 'normal': -6, 'table': -7, 'in_port': -8
}

RE_OUT_ACTION = re.compile(
    '^(?:(?:output:)?([0-9][0-9]*)|output[(].*port=([0-9]+).*)$')

RE_COLON_ACTION = re.compile(
    '^(mod_vlan_vid|mod_vlan_pcp|push_vlan|push_mpls|pop_mpls|mod_dl_src|'
    'mod_dl_dst|mod_nw_src|mod_nw_dst|mod_tp_src|mod_tp_dst|'
    'mod_nw_tos|mod_nw_ecn|mod_nw_ttl|goto_table)'
    ':([0-9][x0-9:.]*)')

RE_RESUBMIT = re.compile('^resubmit(?::([0-9]+)|[(]([0-9]*);([0-9]*)[)])')

SIMPLE_ACTIONS = ['end', 'drop', 'strip_vlan', 'pop_vlan']

ACTION_FIELDS = [
    'end', 'output', 'drop', 'resubmit', 'push_vlan', 'mod_vlan_vid',
    'strip_vlan', 'mod_nw_src', 'mod_nw_dst', 'mod_dl_src', 'mod_dl_dst',
    'mod_tp_src', 'mod_tp_dst', 'strip_vlan', 'pop_vlan', 'goto_table',
    'push_mpls', 'pop_mpls', 'mod_nw_tos', 'mod_nw_ecn', 'mod_nw_ttl',
    'resubmit',
    'unknown']


def preprocess_actions(cnx):
    """Parse openflow actions

    This function prepares a structure used by individual datalog action table
    to extract the relevant actions from all the openflow rules.

    All the rules action lists terminate with an 'end' element.

    :param cnx: a connection to a skydive analyzer
    :return: a structure where each field contains a description of all the
       atomic actions using the operation described by the field name.
       Each element in the lists is a tuple where the first two elements are
       the rule id and the position of the element in the actions of the rule.
    """
    prepared_filters = [
        (rule.id, rule.metadata['actions'].split(',') + ['end'])
        for rule in _filter_node('ofrule')(cnx)
    ]
    result = {}
    for field in ACTION_FIELDS:
        result[field] = []

    for (rule_id, elt_list) in prepared_filters:
        pos = 0
        for elt in elt_list:
            elt = elt.lower()
            if elt in SIMPLE_ACTIONS:
                result[elt].append((rule_id, pos))
                pos = pos + 1
                continue
            if elt in PORT_SHORTHANDS:
                out_port = PORT_SHORTHANDS[elt]
                result['output'].append((rule_id, pos, out_port))
                pos = pos + 1
                continue
            matched = RE_OUT_ACTION.match(elt)
            if matched:
                out_port = matched.group(1)
                if out_port is None:
                    out_port = matched.group(2)
                result['output'].append((rule_id, pos, int(out_port, 0)))
                pos = pos + 1
                continue
            matched = RE_RESUBMIT.match(elt)
            if matched:
                port = matched.group(1)
                table = None
                if port is None:
                    port = matched.group(2)
                    table = matched.group(3)
                    if port == '':
                        port = None
                    if table == '':
                        table = None
                result['resubmit'].append((
                    rule_id, pos,
                    int(port) if port is not None else None,
                    int(table) if table is not None else None))
                pos = pos + 1
                continue
            matched = RE_COLON_ACTION.match(elt)
            if matched:
                field = matched.group(1)
                arg = matched.group(2)
                # Argument is kept as a string. Must be converted by the
                # second level.
                result[field].append((rule_id, pos, arg))
                pos = pos + 1
                continue
            result['unknown'].append((rule_id, pos, elt))
            pos = pos + 1

    return result


def sk_action(access, specs):
    """A utility function to build field accessors

    :param access: the name of the list to use
    :param specs: list of additionnal field names and types
    :return: a tuple suitable for tables.
    """
    fields = {
        'id': ('id', lambda t: t[0]),
        'pos': ('int', lambda t: t[1])
    }
    for (i, (field, typ)) in enumerate(specs):
        if typ == 'int':
            fields[field] = (
                typ,
                (lambda c: lambda t: int(t[c + 2], 0))  # pylint: disable=E0602
                (i))
        else:
            fields[field] = (
                typ,
                (lambda c: lambda t: t[c + 2])(i))    # pylint: disable=E0602
    return (
        ('ska_action', lambda x: x[access]),
        fields
    )


def sk_filter(access, specs):
    """A utility function to build field accessors"""
    fields = {
        'id': ('id', lambda t: t[0]),
        'pos': ('int', lambda t: t[1])
    }
    for (i, (field, typ)) in enumerate(specs):
        fields[field] = (
            typ, (lambda c: lambda t: t[c + 2])(i))  # pylint: disable=E0602
    return (
        ('skf_filter', lambda x: x[access]),
        fields
    )


#: Describes how to bind values extracted from the python skydive client.
TABLES = {
    'sk_host': (
        _filter_node('host'),
        {
            'id': ('id', _id),
            'name': ('string', _metadata('Name')),
            'platform': ('string', _metadata('Platform'))
        }
    ),
    'sk_ovsswitch': (
        _filter_node('openvswitch'),
        {
            'id': ('id', _id),
            'name': ('string', _metadata('Name')),
        }
    ),
    'sk_ovsbridge': (
        _filter_node('ovsbridge'),
        {
            'id': ('id', _id),
            'name': ('string', _metadata('Name')),
        }
    ),
    'sk_ovsport': (
        _filter_node('ovsport'),
        {
            'id': ('id', _id),
            'name': ('string', _metadata('Name')),
        }
    ),
    'sk_rule': (
        _filter_node('ofrule'),
        {
            'id': ('id', _id),
            'priority': ('int', _metadata('priority')),
            'table': ('int', _metadata('table'))
        }
    ),

    'skf_filter': (preprocess_filters, {}),
    'skf_end': sk_filter('end', []),
    'skf_in_port': sk_filter('in_port', [('port', 'int')]),
    'skf_dl_vlan': sk_filter('dl_vlan', [('vlan', 'int')]),
    'skf_dl_src': sk_filter('dl_src', [('src', 'string'), ('mask', 'string')]),
    'skf_dl_dst': sk_filter('dl_dst', [('dst', 'string'), ('mask', 'string')]),
    'skf_nw_src':
        sk_filter('dl_vlan', [('src', 'ip_address'), ('mask', 'ip_address')]),
    'skf_nw_dst':
        sk_filter('dl_vlan', [('dst', 'ip_address'), ('mask', 'ip_address')]),
    'skf_tp_src': sk_filter('tp_src', [('src', 'int'), ('mask', 'int')]),
    'skf_tp_dst': sk_filter('tp_dst', [('dst', 'int'), ('mask', 'int')]),
    'skf_eth_type': sk_filter('eth_type', [('type', 'int')]),
    'skf_ip_proto': sk_filter('ip_proto', [('type', 'int')]),
    'skf_tunnel_id': sk_filter('ip_tunnel_id', [('tunnel', 'int')]),
    'skf_tun_src': sk_filter('tun_src', [('src', 'ip_address')]),
    'skf_tun_dst': sk_filter('tun_dst', [('dst', 'ip_address')]),
    'skf_tun_ipv6_src': sk_filter('tun_ipv6_src', [('src', 'string')]),
    'skf_tun_ipv6_dst': sk_filter('tun_ipv6_dst', [('dst', 'string')]),
    'skf_vlan_tci': sk_filter('vlan_tci', [('tci', 'int'), ('mask', 'int')]),
    'skf_tun_flags':
        sk_filter('tun_flags', [('flags', 'int'), ('mask', 'int')]),
    'skf_unknown': sk_filter('unknown', [('filter', 'string')]),

    'ska_action': (preprocess_actions, {}),
    'ska_output': sk_action('output_port', [('port', 'int')]),
    'ska_push_vlan': sk_action('push_vlan', [('vlan', 'int')]),
    'ska_mod_vlan_vid': sk_action('mod_vlan_vid', [('vlan', 'int')]),
    'ska_mod_vlan_pcp': sk_action('mod_vlan_pcp', [('pcp', 'int')]),
    'ska_push_mpls': sk_action('push_mpls', [('eth_type', 'int')]),
    'ska_pop_mpls': sk_action('pop_mpls', [('eth_type', 'int')]),
    'ska_mod_nw_src': sk_action('mod_nw_src', [('src', 'ip_address')]),
    'ska_mod_nw_dst': sk_action('mod_nw_dst', [('dst', 'ip_address')]),
    'ska_mod_nw_tos': sk_action('mod_nw_dst', [('tos', 'int')]),
    'ska_mod_nw_ecn': sk_action('mod_nw_dst', [('ecn', 'int')]),
    'ska_mod_nw_ttl': sk_action('mod_nw_dst', [('ttl', 'int')]),
    'ska_mod_dl_src': sk_action('mod_dl_src', [('src', 'string')]),
    'ska_mod_dl_dst': sk_action('mod_dl_dst', [('dst', 'string')]),
    'ska_mod_tp_src': sk_action('mod_tp_src', [('src', 'int')]),
    'ska_mod_tp_dst': sk_action('mod_tp_dst', [('dst', 'int')]),
    'ska_goto_table': sk_action('goto_table', [('table', 'int')]),
    'ska_resubmit': sk_action('resubmit', [('port', 'int'), ('table', 'int')]),
    'ska_unknown': sk_action('unknown', [('instr', 'string')]),

    'sk_filter': (
        lambda cnx: elements_of_rule('filters', cnx),
        {
            'rule_id': ('id', lambda t: t[0]),
            'element': ('string', lambda t: t[2]),
            'position': ('int', lambda t: t[1])
        }
    ),
    'sk_action': (
        lambda cnx: elements_of_rule('actions', cnx),
        {
            'rule_id': ('id', lambda t: t[0]),
            'element': ('string', lambda t: t[2]),
            'position': ('int', lambda t: t[1])
        }
    ),
    'sk_owns': (
        _filter_rel('ownership'),
        {
            'owner': ('id', _parent),
            'item': ('id', _child)
        }
    ),
    'sk_l2': (
        _filter_rel('layer2'),
        {
            'a': ('id', _parent),
            'b': ('id', _child)
        }
    )
}

for key in SIMPLE_ACTIONS:
    TABLES['ska_' + key] = (
        ('ska_filter',
         (lambda k: lambda x: x[k])(key)),  # pylint: disable=E0602
        {
            'id': ('id', lambda t: t[0]),
            'pos': ('int', lambda t: t[1])
        }
    )


def register(datasource):
    '''Registers Skydive tables in the datasource

    :param datasource: a datasource object to enrich
    '''
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
