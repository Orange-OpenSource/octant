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
import copy
from six import moves

from oslo_config import cfg

from octant import datalog_ast as ast
from octant import datalog_primitives as primitives
from octant import datalog_typechecker as typechecker
from octant import datalog_unfolding as unfolding


class Z3NotWellFormed(Exception):
    """Raised for a theory that do not respect well-formedness rules"""

    def __init__(self, *args, **kwargs):
        super(Z3NotWellFormed, self).__init__(self, *args, **kwargs)


class Z3Compiler(object):
    """Prepare octant Datalog for compilation to Z3 (extensible tables)."""

    def __init__(self, rules, constants, datasource):
        self.rules = rules
        self.extensible_tables = {}
        self.var_count = 0
        self.datasource = datasource
        self.constants = constants
        self.typed_tables = {}
        self.unfold_plan = None

    def compile(self, z3compiler):
        """Compile preprocess high level Datalog.

        It removes constants, make variables unique and
        extract columns used in extensible tables. It also
        controls the type-checker.
        """
        self.substitute_constants()
        self.find_base_relations()
        if cfg.CONF.doc:
            unfolder = unfolding.Unfolding(
                self.rules, self.extensible_tables, z3compiler)
            self.unfold_plan = unfolder.proceed()
        self.typed_tables = typechecker.type_theory(
            self.rules, self.extensible_tables, self.datasource)

    def substitutes_constants_in_array(self, args):
        """Substitute constants in arguments arrays"""
        for i in moves.range(len(args)):
            oarg = args[i]
            if isinstance(oarg, ast.Constant):
                arg = self.constants.get(args[i].name, None)
                if arg is None:
                    raise Z3NotWellFormed(
                        "Unknown constant: {}".format(args[i].name))
                args[i] = copy.deepcopy(arg)

            elif isinstance(args[i], ast.Operation):
                nb_vars = primitives.OPERATIONS[args[i].operation].ty_vars
                args[i].var_types = [None] * nb_vars
                self.substitutes_constants_in_array(args[i].args)

    def substitute_constants(self):
        """Substitute constants phase"""
        for rule in self.rules:
            self.substitutes_constants_in_array(rule.head.args)
            for atom in rule.body:
                self.substitutes_constants_in_array(atom.args)

    def find_base_relations(self):
        """Extracts base relations of the theory"""
        aux_counter = 0
        new_rules = []
        for rule in self.rules:
            if self.datasource.is_extensible(rule.head):
                raise Z3NotWellFormed("No base predicate allowed in head: " +
                                      rule.head.table)
            for i, atom in enumerate(rule.body):
                if not self.datasource.is_extensible(atom):
                    continue
                fields = self.extensible_tables.setdefault(atom.table, [])
                if atom.labels is None:
                    raise Z3NotWellFormed(
                        "No labels for extensible atom {}".format(atom))
                for label in atom.labels:
                    if label not in fields:
                        fields.append(label)
                if atom.negated:
                    new_table = "_negated_%d" % aux_counter
                    aux_counter += 1
                    new_atom = ast.Atom(
                        new_table, atom.args, negated=True)
                    var_row = [
                        ast.Variable("V%d" % i)
                        for i in range(len(atom.args))]
                    atom_head = ast.Atom(new_table, var_row)
                    atom_body = ast.Atom(
                        atom.table, var_row, labels=atom.labels)
                    new_rule = ast.Rule(atom_head, [atom_body])
                    new_rules.append(new_rule)
                    rule.body[i] = new_atom
        self.rules.extend(new_rules)
        for fields in self.extensible_tables.values():
            fields.sort()
        for rule in self.rules:
            for atom in rule.body:
                if self.datasource.is_extensible(atom):
                    self.flatten(atom, self.extensible_tables[atom.table])

    def flatten(self, atom, fields):
        """Replace named arguments with positional args.

        Knowing the columns in use for extensible tables, column names are
        replaced by positions as regular tables.
        """
        dict_arg = {}

        def new_var():
            """Create a new var with unique name"""
            self.var_count += 1
            return ast.Variable("::{}".format(self.var_count))

        for (label, arg) in zip(atom.labels, atom.args):
            if label in dict_arg:
                raise Z3NotWellFormed(
                    "Duplicate label '{}' in atom {}".format(label, atom))
            dict_arg[label] = arg

        atom.args = [
            dict_arg[label] if label in dict_arg else new_var()
            for label in fields
        ]
        # Hide labels for pretty printing.
        atom.labels = None
