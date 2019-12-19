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

from collections import OrderedDict
import logging
import six
from six import moves
import z3

from oslo_config import cfg

from octant.common import ast
from octant.common import base
from octant.common import primitives
from octant.datalog import compiler
from octant.datalog import operations
from octant.datalog import unfolding
from octant.datalog import z3_comparison as z3c
from octant.datalog import z3_result as z3r
from octant.source import file
from octant.source import openstack_source
from octant.source import skydive_source
from octant.source import source


class Z3Theory(object):
    """A theory of Z3 rules."""

    def __init__(self, rules):
        self.rules = rules
        self.datasource = source.Datasource(primitives.TYPES)
        openstack_source.register(self.datasource)
        skydive_source.register(self.datasource)
        file.register(self.datasource)

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
        if self.compiler.project is not None:
            self.compiler.project.set_relations(self.relations)
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
                raise base.Z3TypeError(
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
        with self.datasource:
            for table_name, fields in six.iteritems(
                    self.compiler.extensible_tables):
                relation = self.relations[table_name]
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
            operator = operations.OPERATIONS[expr.operation].z3
            return operator(
                *(self.compile_expr(variables, arg, env) for arg in expr.args))
        else:
            raise base.Z3NotWellFormed(
                "cannot proceed with {}".format(expr))

    def compile_atom(self, variables, atom, env):
        """Compiles an atom to Z3"""
        args = [self.compile_expr(variables, expr, env) for expr in atom.args]
        if operations.is_primitive(atom):
            compiled_atom = z3.simplify(
                operations.COMPARISON[atom.table](args))
        else:
            if (self.compiler.project is not None and
                    self.compiler.project.is_specialized(atom.table)):
                compiled_atom = self.compiler.project.translate(
                    self.context, atom, args)
            else:
                relation = self.relations[atom.table]
                compiled_atom = relation(*args)
        return z3.Not(compiled_atom) if atom.negated else compiled_atom

    def build_rule(self, rule, env):
        vars = {}
        head = self.compile_atom(vars, rule.head, env)
        body = [
            self.compile_atom(vars, atom, env)
            for atom in rule.body
            if atom is not None]
        if any(z3.is_false(at) for at in body):
            return
        body = [at for at in body if not z3.is_true(at)]
        body_conj = body[0] if len(body) == 1 else z3.And(*body)
        term1 = head if body == [] else z3.Implies(body_conj, head)
        term2 = (
            term1 if vars == {}
            else z3.ForAll(list(vars.values()), term1))
        self.context.rule(term2)

    def build_rules(self):
        """Compiles rules to Z3"""
        if self.compiler.unfold_plan is not None:
            plan = self.compiler.unfold_plan
            env = unfolding.plan_to_program(
                plan, self.context, self.datasource,
                self.relations, self.rules)
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
        if self.compiler.project is not None:
            self.compiler.project.reconciliate(self.context)
        if cfg.CONF.smt2 is not None:
            with open(cfg.CONF.smt2, 'w') as fd:
                self.dump_primitive_tables(fd)
                primitives.dump_translations(fd)
                fd.write(str(self.context))

    def dump_primitive_tables(self, fd):
        fd.write("; *** primitive table declarations ***\n\n")
        for table_name, fields in six.iteritems(
                self.compiler.extensible_tables):
            fd.write("; {}({})\n".format(table_name, ",".join(fields)))

    def query(self, atom):
        """Query a relation on the compiled theory"""
        self.compiler.substitutes_constants_in_array(atom.args)
        if atom.table not in self.compiler.typed_tables:
            raise base.Z3NotWellFormed(
                "Unknown relation {}".format(atom.table))
        atom.types = self.compiler.typed_tables[atom.table]
        if len(atom.types) != len(atom.args):
            raise base.Z3NotWellFormed(
                "Arity of predicate inconsistency in {}".format(atom))
        for i in moves.xrange(len(atom.types)):
            atom.args[i].type = atom.types[i]
        ast_vars = list(OrderedDict.fromkeys([
            arg for arg in atom.args if isinstance(arg, ast.Variable)
        ]))
        vars = {}
        self.compiler.project = None
        query = self.compile_atom(vars, atom, {})
        if vars != {}:
            compiled_vars = [vars[ast_var.full_id()] for ast_var in ast_vars]
            query = z3.Exists(compiled_vars, query)
        self.context.query(query)
        types = [self.datasource.types[ast_var.type] for ast_var in ast_vars]
        variables = [ast_var.id for ast_var in ast_vars]
        raw_answer = self.context.get_answer()
        logging.getLogger().debug("Raw answer:\n%s", raw_answer)
        answer = z3r.z3_to_array(raw_answer, types)
        return variables, answer
