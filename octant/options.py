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

OPTIONS = [
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

CLI_OPTIONS = [
    cfg.MultiStrOpt(
        'theory',
        help=("Name of theory file to load")),
    cfg.MultiStrOpt(
        'query',
        help=("Query(ies) to ask on the theory. Can be repeated.")),
    cfg.BoolOpt(
        'pretty',
        help=("Pretty prints results.")),
    cfg.BoolOpt(
        'time',
        help=("Print timing of the different phases."))
]

cfg.CONF.register_opts(OPTIONS)
cfg.CONF.register_cli_opts(CLI_OPTIONS)


def init(args, **kwargs):
    """Initialize configuration"""
    cfg.CONF(args=args, project='octant',
             version='%%(prog)s %s' % version.VERSION_INFO.release_string(),
             **kwargs)


def list_opts():
    """List config file options for documentation generation"""
    return [('DEFAULT', OPTIONS)]
