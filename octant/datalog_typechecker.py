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

"""Type-checker for Datalog"""

from octant import datalog_ast as ast
from octant import datalog_primitives as primitives


class Z3TypeError(Exception):
    """Raised for a theory that is not well typed"""

    def __init__(self, *args, **kwargs):
        super(Z3TypeError, self).__init__(self, *args, **kwargs)


def type(rules, primitive_tables):

    def prepare_typing():
        dict_vars = {}
        dict_tables = {}
        # Initialize the types of primitive tables in use.
        for (table, fields) in primitive_tables.items():
            args = [primitives.TABLES[table][1][field][0] for field in fields]
            dict_tables[table] = ast.TypedTable(table, args)

        def subst_var(arg):
            """Makes var instances unique"""
            if arg.id in dict_vars:
                var_inst = dict_vars[arg.id]
                if arg.type is not None:
                    if var_inst.type is None:
                        var_inst.type = arg.type
                    else:
                        if var_inst.type != arg.type:
                            raise Z3TypeError(
                                "Incompatible constraint on {}: {} != {}"
                                .format(arg.id, var_inst.type, arg.type))
                return var_inst
            else:
                dict_vars[arg.id] = arg
                return arg

        def prepare_atom(atom):
            """Makes atom typable

            Sustitute table name with a unique table description and
            make var instances unique in arguments.
            """
            if atom.table in dict_tables:
                atom.table = dict_tables[atom.table]
                if len(atom.table.params) != len(atom.args):
                    raise Z3TypeError("Arity problem for symbol")
            else:
                params = [None for _ in atom.args]
                typed_table = ast.TypedTable(atom.table, params)
                dict_tables[atom.table] = typed_table
                atom.table = typed_table
            atom.args = [
                subst_var(arg) if isinstance(arg, ast.Variable) else arg
                for arg in atom.args]

        for rule in rules:
            prepare_atom(rule.head)
            for atom in rule.body:
                prepare_atom(atom)
        return dict_tables

    def type_atom(atom):
        params = atom.table.params
        work_done = False
        for i in range(len(params)):
            param_type = params[i]
            arg = atom.args[i]
            if param_type is None:
                if arg.type is not None:
                    params[i] = arg.type
                    work_done = True
            else:
                if arg.type is None:
                    arg.type = param_type
                    work_done = True
                else:
                    if arg.type != param_type:
                        raise Z3TypeError(
                            "Type error {}:{} not {} in {}".format(
                                arg,
                                arg.type,
                                param_type,
                                atom
                            ))
        return work_done
    dict_tables = prepare_typing()
    work_done = True
    while work_done:
        work_done = False
        for rule in rules:
            wd = type_atom(rule.head)
            work_done = work_done or wd
            for atom in rule.body:
                wd = type_atom(atom)
                work_done = work_done or wd
    return dict_tables
