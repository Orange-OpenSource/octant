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

"""AST for Datalog"""


class AST(object):
    pass


class Rule(AST):
    """Represents a rule"""

    def __init__(self, head, body):
        self.head = head
        self.body = body

    def body_variables(self):
        return set(v for x in self.body for v in x.variables())

    def head_variables(self):
        return self.head.variables()

    def head_table(self):
        return self.head.table

    def body_tables(self):
        return set(atom.table for atom in self.body)

    def rename_variables(self, renaming):
        self.head.rename_variables(renaming)
        for atom in self.body:
            atom.rename_variables(renaming)

    def __repr__(self):
        return "{} :- {}".format(self.head, self.body)


class Atom(AST):
    """Represents an atom either in the head or body"""

    def __init__(self, table, args, negated=False):
        self.table = table
        self.args = args
        self.negated = negated

    def variables(self):
        return set(v for x in self.args for v in x.variables())

    def rename_variables(self, renaming):
        for arg in self.args:
            arg.rename_variables(renaming)

    def __repr__(self):
        return "{}{}({})".format(
            "~" if self.negated else "",
            self.table,
            str(self.args)[1:-1])


class Expr(AST):
    "An expression with an optional label"

    def __init__(self, label=None, type=None):
        self.label = label
        self.type = type

    def variables(self):
        return []

    def str_label(self, s):
        return s if self.label is None else "{}: {}".format(self.label, s)

    def rename_variables(self, renaming):
        pass


class Variable(Expr):
    "A variable (scope rule)"

    def __init__(self, id, label=None, type=None):
        super(Variable, self).__init__(label=label)
        self.id = id

    def variables(self):
        return [self.id]

    def __repr__(self):
        repr = (
            self.id if self.type is None
            else "{}:{}".format(self.id, self.type))
        return self.str_label(repr)

    def rename_variables(self, renaming):
        if self.id in renaming:
            self.id = renaming[self.id]


class Operation(Expr):
    "An n-ary operation"

    def __init__(self, op, args, type=None):
        super(Operation, self).__init__(type=type)
        self.op = op
        self.args = args
        self.var_types = []  # type variable for polymorphic operators.

    def variables(self):
        return set(v for x in self.args for v in x.variables())

    def rename_variables(self, renaming):
        for arg in self.args:
            arg.rename_variables(renaming)

    def __repr__(self):
        return "{}({})".format(self.op, self.args)


class NumConstant(Expr):
    "A numeric constant"

    def __init__(self, val, label=None, type=None):
        super(NumConstant, self).__init__(
            label=label,
            type='int' if type is None else type)
        self.val = val

    def __repr__(self):
        return self.str_label(str(self.val))


class StringConstant(Expr):
    "A string constant"

    def __init__(self, val, label=None, type=None):
        super(StringConstant, self).__init__(label=label, type=type)
        self.val = val

    def __repr__(self):
        return self.str_label('"{}"'.format(self.val))


class BoolConstant(Expr):
    "A boolean constant"

    def __init__(self, val, label=None):
        super(BoolConstant, self).__init__(label=label, type='bool')
        self.val = val

    def __repr__(self):
        return self.str_label(str(self.val))


class IpConstant(Expr):
    "An ip address constant"

    def __init__(self, val, label=None):
        super(IpConstant, self).__init__(label=label, type='ip_address')
        self.val = val

    def __repr__(self):
        return self.str_label(self.val)


class TypedTable(object):
    """A table with a name and types of its columns"""
    def __init__(self, name, params=[]):
        self.name = name
        self.params = params

    def __str__(self):
        return "[{}({})]".format(
            self.name,
            ",".join(str(x) for x in self.params))


class Constant(object):
    """A constant to be substituted"""
    def __init__(self, name, label=None):
        self.name = name
        self.label = label

    def __str__(self):
        return self.name
