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

from octant import datalog_ast as ast
from octant import datalog_primitives as primitives
from octant import datalog_typechecker as typechecker


class Z3NotWellFormed(Exception):
    """Raised for a theory that do not respect well-formedness rules"""

    def __init__(self, *args, **kwargs):
        super(Z3NotWellFormed, self).__init__(self, *args, **kwargs)


class Z3Compiler(object):
    """Prepare octant Datalog for compilation to Z3 (primitive tables)."""

    def __init__(self, rules, constants):
        self.rules = rules
        self.primitive_tables = {}
        self.var_count = 0
        self.constants = constants

    def compile(self):
        """Compile preprocess high level Datalog.

        It removes constants, make variables unique and
        extract columns used in primitive tables. It also
        controls the type-checker.
        """
        self.substitute_constants()
        self.rename_variables()
        self.find_base_relations()
        typed_tables = typechecker.type_theory(
            self.rules, self.primitive_tables)
        return self.primitive_tables, typed_tables

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
                args[i].label = oarg.label

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

    def rename_variables(self):
        """Rename variables phase"""
        # WARNING: without nonlocal (python3) known must only be modified by
        # side effect. Assignment would create a new scope in inner functions !
        known = set()

        def rename_var(old, count=0):
            """Rename a variable"""
            newname = "{}:{}".format(old, count)
            if newname in known:
                return rename_var(old, count + 1)
            known.add(newname)
            return newname

        def rename_rule(rule):
            """Rename in a rule"""
            head_vars = rule.head_variables()
            body_vars = rule.body_variables()
            all_vars = body_vars.union(head_vars)
            seen = all_vars.intersection(known)
            known.update(all_vars)
            if seen:
                renaming = {v: rename_var(v) for v in seen}
                rule.rename_variables(renaming)

        for rule in self.rules:
            rename_rule(rule)

    def find_base_relations(self):
        """Extracts base relations of the theory"""
        for rule in self.rules:
            if primitives.is_primitive_atom(rule.head):
                raise Z3NotWellFormed("No base predicate allowed in head.")
            for atom in rule.body:
                if not primitives.is_primitive_atom(atom):
                    continue
                fields = self.primitive_tables.setdefault(atom.table, [])
                for arg in atom.args:
                    if arg.label is None:
                        raise Z3NotWellFormed(
                            "No label for {} in {}".format(arg, atom))
                    if arg.label not in fields:
                        fields.append(arg.label)
        for fields in self.primitive_tables.values():
            fields.sort()
        for rule in self.rules:
            for atom in rule.body:
                if primitives.is_primitive_atom(atom):
                    self.flatten(atom, self.primitive_tables[atom.table])

    def flatten(self, atom, fields):
        """Replace named arguments with positional args.

        Knowing the columns in use for primitive tables, column names are
        replaced by positions as regular tables.
        """
        dict_arg = {}

        def new_var():
            """Create a new var with unique name"""
            self.var_count += 1
            return ast.Variable("::{}".format(self.var_count))

        for arg in atom.args:
            if arg.label in dict_arg:
                raise Z3NotWellFormed("Duplicate label in atom")
            dict_arg[arg.label] = arg
            arg.label = None

        atom.args = [
            dict_arg[label] if label in dict_arg else new_var()
            for label in fields
        ]
