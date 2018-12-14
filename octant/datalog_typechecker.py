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
from six import moves

from octant import datalog_ast as ast
from octant import datalog_primitives as primitives


class Z3TypeError(Exception):
    """Raised for a theory that is not well typed"""

    def __init__(self, *args, **kwargs):
        super(Z3TypeError, self).__init__(self, *args, **kwargs)


def type_theory(rules, extensible_tables, datasource):
    """Types a given set of rules"""

    def prepare_typing():
        """Initialize typing with info from extensible tables"""
        dict_vars = {}
        dict_tables = {}
        # Initialize the types of extensible tables in use.
        for (table, fields) in extensible_tables.items():
            args_types = datasource.get_table_types(table, fields)
            dict_tables[table] = args_types

        def subst_var(arg):
            """Makes var instances unique"""
            if isinstance(arg, ast.Variable):
                if arg.full_id() in dict_vars:
                    var_inst = dict_vars[arg.full_id()]
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
                    dict_vars[arg.full_id()] = arg
                    return arg
            elif isinstance(arg, ast.Operation):
                arg.args = [subst_var(a) for a in arg.args]
                return arg
            else:
                return arg

        def prepare_atom(atom):
            """Makes atom typable

            Sustitute table name with a unique table description and
            make var instances unique in arguments.

            Comparison are a particular case, due to polymorphism.
            """
            if atom.table in primitives.COMPARISON:
                atom.types = [None, None]
            elif atom.table in dict_tables:
                atom.types = dict_tables[atom.table]
                if len(atom.types) != len(atom.args):
                    raise Z3TypeError(
                        "Arity problem for symbol {} in {}".format(
                            atom.table, atom))
            else:
                params = [None for _ in atom.args]
                dict_tables[atom.table] = params
                atom.types = params
            atom.args = [
                subst_var(arg) for arg in atom.args]

        for rule in rules:
            prepare_atom(rule.head)
            for atom in rule.body:
                prepare_atom(atom)
        return dict_tables

    def type_expr(expr):
        """Types an expression"""
        if not isinstance(expr, ast.Operation):
            return False

        def get_type(scheme):
            """Get the type of an operation argument."""
            if isinstance(scheme, int):
                return expr.var_types[scheme]
            return scheme

        work_done = False
        schema = primitives.OPERATIONS[expr.operation]
        if expr.var_types is None:
            expr.var_types = [None] * schema.ty_vars
        typ_scheme_res = get_type(schema.result)
        if expr.type is None:
            if typ_scheme_res is not None:
                expr.type = typ_scheme_res
                work_done = True
        else:
            if typ_scheme_res is None:
                expr.var_types[schema.result] = expr.type
                work_done = True
            else:
                if typ_scheme_res != expr.type:
                    raise Z3TypeError(
                        "Type error expresion {} has type {} not {}".format(
                            expr,
                            typ_scheme_res,
                            expr.type))
        for i in moves.range(len(expr.args)):
            arg = expr.args[i]
            if type_expr(arg):
                work_done = True
            typ_schema_arg = get_type(schema.args[i])
            if arg.type is None:
                if typ_schema_arg is not None:
                    arg.type = typ_schema_arg
                    work_done = True
            else:
                if typ_schema_arg is None:
                    expr.var_types[schema.args[i]] = arg.type
                    work_done = True
                else:
                    if typ_schema_arg != arg.type:
                        raise Z3TypeError(
                            "Type error: arg {} has type {} not {}".format(
                                arg,
                                typ_schema_arg,
                                arg.type))
        return work_done

    def type_atom(atom):
        """Types an atom"""
        params = atom.types
        work_done = False
        for i in moves.range(len(params)):
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
        if atom.table in primitives.COMPARISON:
            param0 = atom.types[0]
            param1 = atom.types[1]
            if param0 is None:
                if param1 is not None:
                    atom.types[0] = atom.types[1]
                    atom.args[0].type = atom.types[1]
                    work_done = True
            else:
                if param1 is None:
                    atom.types[1] = atom.types[0]
                    atom.args[1].type = atom.types[0]
                    work_done = True
                else:
                    if param0 != param1:
                        raise Z3TypeError(
                            "Type error on equality {} not {} != {}".format(
                                atom,
                                param0,
                                param1
                            ))
        for arg in atom.args:
            if type_expr(arg):
                work_done = True
        return work_done
    dict_tables = prepare_typing()
    work_done = True
    while work_done:
        work_done = False
        for rule in rules:
            new_work = type_atom(rule.head)
            work_done = work_done or new_work
            for atom in rule.body:
                new_work = type_atom(atom)
                work_done = work_done or new_work
    return dict_tables
