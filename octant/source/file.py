#    Copyright 2019 Orange
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

"""File Data Source"""
from oslo_config import cfg

from octant import base


def loadDescription(tables, source, fd):
    for line in fd:
        elements = line.split(",")
        if len(elements) < 1:
            continue
        tablename = elements[0].strip()
        if tablename == '':
            continue
        contents = {}
        for descr in elements[1:]:
            subs = descr.strip().split(":")
            if len(subs) != 2:
                raise base.Z3SourceError(
                    "Bad type description in {}: {}".format(source, descr))
            [field, typ] = subs
            contents[field] = (typ, lambda x: [])
        tables[tablename] = ((lambda x: x), contents)


def register(datasource):
    """Registers tables described by user files in the datasource

    :param datasource: a datasource object to enrich
    """
    filesource = cfg.CONF.filesource
    tables = {}
    for source in filesource:
        with open(source, 'r') as fd:
            loadDescription(tables, source, fd)
    datasource.register(None, tables)
