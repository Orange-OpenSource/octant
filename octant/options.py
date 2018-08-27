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

""" Check-reach configuration options management """
from oslo_config import cfg

from octant import version

OPENSTACK_OPTIONS = [
    cfg.BoolOpt('enabled', default=True, help='Enable Openstack predicates'),
    cfg.StrOpt('www_authenticate_uri', default='http://127.0.0.1/identity',
               help='Keystone URI for authentication (as admin).'),
    cfg.StrOpt('project_name', default=None, help='Project name'),
    cfg.StrOpt('user_name', default='', help='User name'),
    cfg.StrOpt('user_domain_name', default='default', help='Domain name'),
    cfg.StrOpt('project_domain_name', default=None, help='Domain name'),
    cfg.StrOpt('region_name', default='RegionOne', help='Project name'),
    cfg.StrOpt('password', default='', help='Password of user for connection'),
    cfg.BoolOpt('verify', default=True, help='Verification of certificates'),
    cfg.BoolOpt('all_projects', default=True,
                help='Gives back results for all tenants')
]

SKYDIVE_OPTIONS = [
    cfg.BoolOpt('enabled', default=False, help='Enable Skydive predicates'),
    cfg.StrOpt('endpoint', default='127.0.0.1:8082',
               help='Exposed skydive endpoint.'),
    cfg.StrOpt('user_name', default='', help='User name'),
    cfg.StrOpt('password', default='', help='Password of user for connection'),
    cfg.StrOpt('scheme', default='http',
               help='Connection scheme (http or https)'),
    cfg.BoolOpt('verify', default=True, help='Verification of certificates'),
]

CLI_OPTIONS = [
    cfg.MultiStrOpt('theory', help="Name of theory file to load"),
    cfg.MultiStrOpt(
        'query', help="Query(ies) to ask on the theory. Can be repeated."),
    cfg.StrOpt('save', default=None, help='Create a backup file'),
    cfg.StrOpt(
        'restore', default=None,
        help='Use a backup file instead of a connection'),
    cfg.BoolOpt('pretty', default=False, help="Pretty prints results."),
    cfg.BoolOpt('csv', default=False, help="Output as csv file."),
    cfg.BoolOpt(
        'time', default=False, help="Print timing of the different phases."),
    cfg.BoolOpt('debug', default=False, help="Set loglevel to debug"),
    cfg.BoolOpt('doc', default=False, help="Uses Difference of Cubes")
]

cfg.CONF.register_opts(OPENSTACK_OPTIONS, group='openstack')
cfg.CONF.register_opts(SKYDIVE_OPTIONS, group='skydive')
cfg.CONF.register_opts(CLI_OPTIONS)
cfg.CONF.register_cli_opts(CLI_OPTIONS)


def init(args, **kwargs):
    """Initialize configuration"""
    cfg.CONF(args=args, project='octant',
             version='%%(prog)s %s' % version.VERSION_INFO.release_string(),
             **kwargs)


def list_opts():
    """List config file options for documentation generation"""
    return [
        ('DEFAULT', CLI_OPTIONS),
        ('openstack', OPENSTACK_OPTIONS),
        ('skydive', SKYDIVE_OPTIONS)]
