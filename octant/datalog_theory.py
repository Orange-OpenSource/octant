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

import logging
import six
from six import moves
import sys
import textwrap
import time
import z3

from oslo_config import cfg

from octant import datalog_ast as ast
from octant import datalog_compiler as compiler
from octant import datalog_parser as parser
from octant import datalog_primitives as primitives
from octant import datalog_source as source
from octant import datalog_typechecker as typechecker
from octant import datalog_unfolding as unfolding
from octant import options
from octant import source_openstack
from octant import source_skydive
from octant import z3_comparison as z3c
from octant import z3_result as z3r


class Z3Theory(object):
    """A theory of Z3 rules."""

    def __init__(self, rules):
        self.rules = rules
        self.datasource = source.Datasource(primitives.TYPES)
        source_openstack.register(self.datasource)
        source_skydive.register(self.datasource)

        self.compiler = (
            compiler.Z3Compiler(rules, primitives.CONSTANTS, self.datasource))

        def constant_compiler(expr):
            return self.datasource.types[expr.type].to_z3(expr.val)

        self.compiler.compile(constant_compiler)
        self.relations = {}

        context = z3.Fixedpoint()
        z3_config = {"engine": "datalog"}
        if cfg.CONF.doc:
            z3_config["datalog.default_relation"] = "doc"
        context.set(**z3_config)
        self.context = context

    def build_theory(self):
        """Builds the Z3 theory"""
        self.build_relations()
        # TODO(piac6784) Retrieve table values as requested
        # by self.compiler.unfold_plan. Build a datastructure with
        # table columns needed (or all columns to begin.)
        self.retrieve_data()
        logging.getLogger().debug("AST of rules:\n%s", self.rules)
        self.build_rules()

    def build_relations(self):
        """Builds the compiled relations"""
        for name, arg_types in six.iteritems(self.compiler.typed_tables):
            try:
                param_types = [
                    self.datasource.types[typename].type()
                    for typename in arg_types]
            except KeyError as exc:
                raise typechecker.Z3TypeError(
                    "Unknown type {} found for {}: {}".format(
                        exc.args[0],
                        name,
                        arg_types
                    ))
            param_types.append(z3.BoolSort())
            relation = z3.Function(name, *param_types)
            self.context.register_relation(relation)
            self.relations[name] = relation

    def retrieve_data(self):
        """Retrieve the network configuration data over the REST api"""

        # implementation warning: do not define in loop.
        # Use an explicit closure.
        def mk_relation(relation):
            "Builds the Z3 relation"
            return lambda args: self.context.fact(relation(args))
        unfold_plan = self.compiler.unfold_plan
        with self.datasource:
            for table_name, fields in six.iteritems(
                    self.compiler.extensible_tables):
                extract = (
                    unfold_plan.tables.get(table_name)
                    if unfold_plan is not None else None)
                relation = self.relations[table_name]
                if extract:
                    table_content = self.datasource.retrieve_table(
                        table_name, fields, mk_relation(relation), extract)
                    unfold_plan.contents[table_name] = table_content
                else:
                    self.datasource.retrieve_table(
                        table_name, fields, mk_relation(relation))

    def compile_expr(self, variables, expr, env):
        """Compile an expression to Z3"""
        if isinstance(expr, (ast.NumConstant, ast.StringConstant,
                             ast.BoolConstant, ast.IpConstant)):
            return self.datasource.types[expr.type].to_z3(expr.val)
        elif isinstance(expr, ast.Variable):
            full_id = expr.full_id()
            if full_id in env:
                return env[full_id]
            if full_id in variables:
                return variables[full_id]
            expr_type = self.datasource.types[expr.type].type()
            var = z3.Const(expr.id, expr_type)
            variables[full_id] = var
            return var
        elif isinstance(expr, ast.Operation):
            operator = primitives.OPERATIONS[expr.operation].z3
            return operator(
                *(self.compile_expr(variables, arg, env) for arg in expr.args))
        else:
            raise compiler.Z3NotWellFormed(
                "cannot proceed with {}".format(expr))

    def compile_atom(self, variables, atom, env):
        """Compiles an atom to Z3"""
        args = [self.compile_expr(variables, expr, env) for expr in atom.args]
        if primitives.is_primitive(atom):
            compiled_atom = primitives.COMPARISON[atom.table](args)
        else:
            relation = self.relations[atom.table]
            compiled_atom = relation(*args)
        return z3.Not(compiled_atom) if atom.negated else compiled_atom

    def build_rule(self, rule, env):
        vars = {}
        head = self.compile_atom(vars, rule.head, env)
        body = [self.compile_atom(vars, atom, env) for atom in rule.body]
        term1 = head if body == [] else z3.Implies(z3.And(*body), head)
        term2 = (
            term1 if vars == {}
            else z3.ForAll(list(vars.values()), term1))
        self.context.rule(term2)

    def build_rules(self):
        """Compiles rules to Z3"""
        if cfg.CONF.doc:
            plan = self.compiler.unfold_plan
            env = unfolding.environ_from_plan(plan)
        else:
            env = {}
        for rule in self.rules:
            env_rule = env.get(rule.id, None)
            if env_rule is not None:
                for rec in env_rule:
                    self.build_rule(rule, rec)
            else:
                self.build_rule(rule, {})
        z3c.register(self.context)
        logging.getLogger().debug("Compiled rules:\n%s", self.context)

    def query(self, str_query):
        """Query a relation on the compiled theory"""
        atom = parser.parse_atom(str_query)
        self.compiler.substitutes_constants_in_array(atom.args)
        if atom.table not in self.compiler.typed_tables:
            raise compiler.Z3NotWellFormed(
                "Unknown relation {}".format(atom.table))
        atom.types = self.compiler.typed_tables[atom.table]
        if len(atom.types) != len(atom.args):
            raise compiler.Z3NotWellFormed(
                "Arity of predicate inconsistency in {}".format(atom))
        for i in moves.xrange(len(atom.types)):
            atom.args[i].type = atom.types[i]
        vars = {}
        query = self.compile_atom(vars, atom, {})
        query = query if vars == {} else z3.Exists(list(vars.values()), query)
        self.context.query(query)
        types = [
            self.datasource.types[arg.type]
            for arg in atom.args
            if isinstance(arg, ast.Variable)]
        variables = [
            arg.id for arg in atom.args if isinstance(arg, ast.Variable)
        ]
        raw_answer = self.context.get_answer()
        logging.getLogger().debug("Raw answer:\n%s", raw_answer)
        answer = z3r.z3_to_array(raw_answer, types)
        if isinstance(answer, bool):
            return variables, answer
        return variables, answer


def print_result(query, variables, answers, time_used, show_pretty):
    """Pretty-print the result of a query"""
    print("*" * 80)
    print(query)
    if time_used is not None:
        print("Query time: {}".format(time_used))
    print("-" * 80)
    if show_pretty:
        if isinstance(answers, list):
            z3r.print_pretty(variables, answers)
        else:
            print('   ' + str(answers))
    else:
        wrapped = textwrap.wrap(
            str(answers), initial_indent='    ', subsequent_indent='    ')
        for line in wrapped:
            print(line)


def main():
    """Octant entry point"""
    logging.basicConfig(stream=sys.stderr, level=logging.WARNING)
    args = sys.argv[1:]
    options.init(args)
    time_required = cfg.CONF.time
    csv_out = cfg.CONF.csv
    pretty = cfg.CONF.pretty
    debug = cfg.CONF.debug
    if debug:
        logging.getLogger().setLevel(logging.DEBUG)
    if csv_out and (time_required or pretty):
        print("Cannot use option --csv with --time or --pretty.")
        sys.exit(1)
    rules = []
    start = time.clock()
    try:
        for rule_file in cfg.CONF.theory:
            rules += parser.parse_file(rule_file)
    except parser.Z3ParseError as exc:
        print(exc.args[1])
        sys.exit(1)
    if time_required:
        print("Parsing time: {}".format(time.clock() - start))
    start = time.clock()
    try:
        theory = Z3Theory(rules)
        theory.build_theory()
        if time_required:
            print("Data retrieval: {}".format(time.clock() - start))
        for query in cfg.CONF.query:
            start = time.clock()
            variables, answers = theory.query(query)
            if csv_out:
                z3r.print_csv(variables, answers)
            else:
                print_result(
                    query, variables, answers,
                    time.clock() - start if time_required else None,
                    cfg.CONF.pretty)
        if not csv_out:
            print("*" * 80)
    except compiler.Z3NotWellFormed as exc:
        print("Badly formed program: {}".format(exc.args[1]))
        sys.exit(1)
    except typechecker.Z3TypeError as exc:
        print("Type error: {}".format(exc.args[1]))
        sys.exit(1)
    except parser.Z3ParseError:
        print("Parser error in query.")
        sys.exit(1)


if __name__ == '__main__':
    main()
