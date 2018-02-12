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

from octant import datalog_ast as ast
from octant import datalog_primitives as primitives
from octant import datalog_typechecker as typechecker


class Z3NotWellFormed(Exception):
    """Raised for a theory that do not respect well-formedness rules"""

    def __init__(self, *args, **kwargs):
        super(Z3NotWellFormed, self).__init__(self, *args, **kwargs)


class Z3Compiler(object):

    def __init__(self, rules):
        self.rules = rules
        self.primitive_tables = {}
        self.var_count = 0

    def compile(self):
        self.rename_variables()
        self.find_base_relations()
        typed_tables = typechecker.type(self.rules, self.primitive_tables)
        return self.primitive_tables, typed_tables

    def rename_variables(self):
        # WARNING: without nonlocal (python3) known must only be modified by
        # side effect. Assignment would create a new scope in inner functions !
        known = set()

        def rename_var(old, count=0):
            newname = "{}:{}".format(old, count)
            if newname in known:
                return rename_var(old, count + 1)
            else:
                known.add(newname)
                return newname

        def rename_rule(r):
            head_vars = r.head_variables()
            body_vars = r.body_variables()
            # if not head_vars.issubset(body_vars):
            #    raise Z3NotWellFormed(
            #        "Head variables must be included in body vars")
            vars = body_vars.union(head_vars)
            seen = vars.intersection(known)
            known.update(vars)
            if len(seen) > 0:
                renaming = {v: rename_var(v) for v in seen}
                r.rename_variables(renaming)

        for rule in self.rules:
            rename_rule(rule)

    def find_base_relations(self):
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
        dict = {}

        def new_var():
            self.var_count += 1
            return ast.Variable("::{}".format(self.var_count))

        for arg in atom.args:
            if arg.label in dict:
                raise Z3NotWellFormed("Duplicate label in atom")
            dict[arg.label] = arg
            arg.label = None

        atom.args = [
            dict[label] if label in dict else new_var()
            for label in fields
        ]
