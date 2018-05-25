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

"""Generic interface for datasources used by theory"""

from __future__ import print_function

from collections import namedtuple
import csv

from oslo_config import cfg

from octant import datalog_compiler as compiler
from octant import datalog_typechecker as typechecker

TableAccessor = namedtuple('TableAccessor', ['session', 'access', 'fields'])


class Datasource(object):
    """Represents the source of facts used by the Datalog interpreter

    :param types: Basic types used by the source.
    """

    def __init__(self, types):
        self.backup = None
        self.datasources = {}
        self.csv_writer = None
        self.csvfile = None
        self.types = types

    def __enter__(self):
        """Configure the datasources"""
        if cfg.CONF.restore is not None:
            with open(cfg.CONF.restore, 'r') as csvfile:
                csvreader = csv.reader(csvfile)
                backup = {}
                current = ''
                table = []
                for row in csvreader:
                    tablename = row[0]
                    if tablename != current:
                        table = []
                        current = tablename
                        backup[tablename] = (row[1:], table)
                    else:
                        table.append(row[1:])
            self.backup = backup
        if cfg.CONF.save is not None:
            self.csvfile = open(cfg.CONF.save, mode='w')
            self.csv_writer = csv.writer(self.csvfile)

    def __exit__(self, typ, value, traceback):
        if self.csvfile is not None:
            self.csvfile.close()

    def register(self, session, accessors):
        """Registers a new source.

        A source is described by a way to
        create a sessions and accessors to populate each table.
        The complete type using Haskell-like existential type (generics
        with limited scope) would be::

          (session: Callable[[], S],
           accessor: Dict[
             str,
             Forall[R,
               Tuple[
                 Callable[[S], R],
                 Dict[str, Tuple[str, Callable[[R], int | str]]]]]]
          ) -> None

        :param session: a callback ``() -> S`` where ``S`` is the type
           of a session.
        :param accessors: a map where keys are table (predicate)
           names and values are pairs of a row accessor of type ``(S) -> R``
           where ``R`` is the type of the internal datasource row
           representation and a map that associates to each field name
           of the row a pair of the name of an octant type ``t`` and a field
           accessor of type ``(R) -> T`` where ``T`` is the source
           representation of ``t``.

        """

        for tablename in accessors:
            (access, fields) = accessors[tablename]
            self.datasources[tablename] = (
                TableAccessor(session=session, access=access, fields=fields))

    def is_primitive(self, atom):
        """Check if the atom uses a table registered in the datasource

        :param atom: the atom
        :return: a boolean

        """
        return atom.table in self.datasources

    def get_table_types(self, table, fields):
        """Return the types of the fields for a given table

        :param table: the table name
        :param fields: a list of field names
        :return: a list of the type names of the fiels
        """
        if table in self.datasources:
            prim = self.datasources[table].fields
        else:
            raise typechecker.Z3TypeError("Unknown primitive {}".format(table))
        try:
            args = [prim[field][0] for field in fields]
        except KeyError as exc:
            raise typechecker.Z3TypeError(
                "Unknown field {} in table {}".format(exc.args[0], table))
        return args

    def use_cache(self):
        """check if it uses the cache"""
        return cfg.CONF.restore is not None

    def retrieve_table(self, table_name, fields, mk_relation):
        """Get the facts on the cloud or in the csv cache.

        :param table_name: the name of the table to retrieve
        :param fields: the list of field names of the table used
        :param mk_relation: a callback called on each row an taking a row
          value as a list of Z3 objects associated to each field and
          creating a fact in the Z3 context for the row.
        """
        use_cache = self.backup is not None
        if table_name in self.datasources:
            accessor = self.datasources[table_name]
            if use_cache:
                (index, objs) = self.backup.get(table_name, [])
            else:
                index = None
                objs = accessor.access(accessor.session)
        else:
            raise typechecker.Z3TypeError(
                'Unknown primitive relation {}'.format(table_name))

        def get_field(field):
            """Get a field compilation functions for cloud access"""
            type_name, access = accessor.fields[field]
            type_field = self.types[type_name]
            return (type_field.to_z3, access, type_field.marshall)

        def get_field_from_cache(field):
            """Get a field compilation functions for csv access"""
            type_name, _ = accessor.fields[field]
            type_field = self.types[type_name]
            try:
                pos = index.index(field)
            except ValueError:
                raise compiler.Z3NotWellFormed(
                    "Field {} was not saved for table {}".format(
                        field,
                        table_name))
            return (
                type_field.to_z3,
                lambda row: type_field.unmarshall(row[pos]),
                type_field.marshall)

        if use_cache:
            access_fields = [get_field_from_cache(field) for field in fields]
        else:
            access_fields = [get_field(field) for field in fields]
        if self.csv_writer is not None:
            self.csv_writer.writerow([table_name] + fields)
        for obj in objs:
            try:
                extracted = [
                    (typ, acc(obj), marshall)
                    for (typ, acc, marshall) in access_fields]
                if self.csv_writer is not None:
                    self.csv_writer.writerow(
                        [table_name] +
                        [marshall(raw) for (_, raw, marshall) in extracted])
                mk_relation([typ(raw) for (typ, raw, _) in extracted])
            except Exception as exc:
                print(
                    "Error while retrieving table {} on {}".format(
                        table_name, obj))
                raise exc
