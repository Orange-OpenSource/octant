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

"""Transform an AST describing a theory in a Z3 context"""

from __future__ import print_function

import abc
import getpass
import sys
import textwrap
import time

import six
from six import moves
import z3

from openstack import connection
from openstack import profile
from oslo_config import cfg

from octant import datalog_ast as ast
from octant import datalog_compiler as compiler
from octant import datalog_parser as parser
from octant import datalog_primitives as primitives
from octant import options


def z3_to_array(expr):
    def extract(item):
        kind = item.decl().kind()
        if kind == z3.Z3_OP_AND:
            return [x.children()[1] for x in item.children()]
        elif kind == z3.Z3_OP_EQ:
            return [item.children()[1]]
        else:
            raise compiler.Z3NotWellFormed(
                "Bad result  {}: {}".format(expr, kind))
    kind = expr.decl().kind()
    if kind == z3.Z3_OP_OR:
        return [extract(item) for item in expr.children()]
    elif kind == z3.Z3_OP_AND:
        return [[item.children()[1] for item in expr.children()]]
    elif kind == z3.Z3_OP_EQ:
        return [[expr.children()[1]]]
    elif kind == z3.Z3_OP_FALSE:
        return False
    elif kind == z3.Z3_OP_TRUE:
        return True
    else:
        raise compiler.Z3NotWellFormed("Bad result {}: {}".format(expr, kind))


@six.add_metaclass(abc.ABCMeta)
class Z3Type(object):
    """Translate Openstack values to Z3"""

    def __init__(self, name, type_instance):
        self.name = name
        self.type_instance = type_instance

    @abc.abstractmethod
    def z3(self, val):
        """Transforms a value from OpenStack in a Z3 value"""
        raise NotImplementedError

    @abc.abstractmethod
    def os(self, val):
        """Transforms a value from Z3 back to python"""
        raise NotImplementedError

    def type(self):
        """Gives back the Z3 type"""
        return self.type_instance


class BoolType(Z3Type):

    def __init__(self):
        super(BoolType, self).__init__('bool', z3.BoolSort())

    def z3(self, val):
        return z3.BoolVal(val)

    def os(self, val):
        return val.sort_kind().name() == 'true'


class StringType(Z3Type):

    def __init__(self, name, size=16):
        super(StringType, self).__init__(name, z3.BitVecSort(size))
        self.map = {}
        self.back = {}

    def z3(self, str):
        """Translates a string to a number and ultimately a bit vector"""
        if str in self.map:
            return self.map[str]
        else:
            code = len(self.map)
            val = z3.BitVecVal(code, self.type_instance)
            self.map[str] = val
            self.back[code] = str
            return val

    def os(self, val):
        return self.back[val.as_long()]


class NumType(Z3Type):

    def __init__(self, name, size=32):
        super(NumType, self).__init__(name, z3.BitVecSort(size))
        self.map = {}
        self.back = {}

    def z3(self, val):
        return z3.BitVecVal(val, self.type_instance)

    def os(self, val):
        return val.as_long()


class Z3Theory(object):
    """A theory of Z3 rules."""

    def __init__(self, rules):
        self.rules = rules
        self.compile_instance = compiler.Z3Compiler(rules)
        primitive_tables, typed_tables = self.compile_instance.compile()
        self.primitive_tables = primitive_tables
        self.typed_tables = typed_tables
        self.relations = {}
        self.vars = {}

        context = z3.Fixedpoint()
        context.set(engine='datalog')
        self.context = context

        self.types = {
            'string': StringType('string'),
            'id': StringType('id'),
            'int': NumType('int'),
            'int4': NumType('int', size=4),
            'bool': BoolType()
        }

    def build_theory(self):
        self.build_relations()
        self.retrieve_data()
        self.build_rules()

    def build_relations(self):
        for name, typedTable in six.iteritems(self.typed_tables):
            paramTypes = [
                self.types[typename].type()
                for typename in typedTable.params]
            paramTypes.append(z3.BoolSort())
            relation = z3.Function(name, *paramTypes)
            self.context.register_relation(relation)
            self.relations[name] = relation

    def retrieve_table(self, conn, table_name, fields):
        accessor, fields_descr = primitives.TABLES[table_name]
        relation = self.relations[table_name]

        def get_field(field):
            type_name, access = fields_descr[field]
            type = self.types[type_name]
            return lambda x: type.z3(access(x))

        access_fields = [get_field(field) for field in fields]
        for obj in accessor(conn):
            self.context.fact(relation(*[acc(obj) for acc in access_fields]))

    def retrieve_data(self):
        """Retrieve the network configuration data over the REST api"""
        prof = profile.Profile()
        prof.set_region(profile.Profile.ALL, cfg.CONF.region_name)
        password = cfg.CONF.password
        if password == "":
            password = getpass.getpass()
        auth_args = {
            'auth_url': cfg.CONF.www_authenticate_uri,
            'project_name': cfg.CONF.project_name,
            'username': cfg.CONF.user_name,
            'password': password,
            'user_domain_name': cfg.CONF.user_domain_name,
            'project_domain_name': cfg.CONF.project_domain_name,
            'profile': prof}
        conn = connection.Connection(**auth_args)

        for table_name, fields in six.iteritems(self.primitive_tables):
            self.retrieve_table(conn, table_name, fields)

        # As pylint is a little lost with openstack
        # pylint: disable=no-member
        ports = [(p.id, p.network_id, p.device_id)
                 for p in conn.network.ports()]
        networks = [(n.id, n.name) for n in conn.network.networks()]
        routers = [(r.id, r.name) for r in conn.network.routers()]
        return {
            'networks': networks,
            'ports': ports,
            'routers': routers
        }

    def compile_expr(self, vars, expr):
        if isinstance(expr, ast.NumConstant):
            return self.types['int'].z3(expr.val)
        elif isinstance(expr, ast.StringConstant):
            return self.types['string'].z3(expr.val)
        elif isinstance(expr, ast.Variable):
            if expr.id in vars:
                return vars[expr.id]
            else:
                type = self.types[expr.type].type()
                var = z3.Const(expr.id, type)
                self.context.declare_var(var)
                vars[expr.id] = var
                return var
        else:
            raise compiler.Z3NotWellFormed(
                "cannot proceed with {}".format(expr))

    def compile_atom(self, vars, atom):
        args = [self.compile_expr(vars, expr) for expr in atom.args]
        relation = self.relations[atom.table.name]
        compiled_atom = relation(*args)
        return z3.Not(compiled_atom) if atom.negated else compiled_atom

    def build_rules(self):
        for rule in self.rules:
            head = self.compile_atom(self.vars, rule.head)
            body = [self.compile_atom(self.vars, atom) for atom in rule.body]
            self.context.rule(head, body)

    def query(self, str):
        atom = parser.parse_atom(str)
        if atom.table not in self.typed_tables:
            raise compiler.Z3NotWellFormed(
                "Unknown relation {}".format(atom.table))
        atom.table = self.typed_tables[atom.table]
        if (len(atom.table.params) != len(atom.args)):
            raise compiler.Z3NotWellFormed(
                "Arity of predicate inconsistency")
        for i in moves.xrange(len(atom.table.params)):
            atom.args[i].type = atom.table.params[i]
        query = self.compile_atom({}, atom)
        self.context.query(query)
        types = [self.types[param] for param in atom.table.params]
        answer = z3_to_array(self.context.get_answer())
        if type(answer) is bool:
            return answer
        return [
            type_x.os(x) for row in answer
            for type_x, x in moves.zip(types, row)]


def print_result(query, answers, time):
    """Pretty-print the result of a query"""
    print("*" * 80)
    print(query)
    if time is not None:
        print("Query time: {}".format(time))
    print("-" * 80)
    wrapped = textwrap.wrap(
        str(answers), initial_indent='    ', subsequent_indent='    ')
    for line in wrapped:
        print(line)


def main():
    """Octant entry point"""
    args = sys.argv[1:]
    options.init(args)
    time_required = cfg.CONF.time
    rules = []
    start = time.clock()
    for rule_file in cfg.CONF.theory:
        rules += parser.parse_file(rule_file)
    if time_required:
        print("Parsing time: {}".format(time.clock() - start))
    start = time.clock()
    theory = Z3Theory(rules)
    theory.build_theory()
    if time_required:
        print("Data retrieval: {}".format(time.clock() - start))
    for query in cfg.CONF.query:
        start = time.clock()
        answers = theory.query(query)
        print_result(
            query, answers,
            time.clock() - start if time_required else None)
    print("*" * 80)
