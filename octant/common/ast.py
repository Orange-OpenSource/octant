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
    """Base ast (abstract syntax tree) type for octant Datalog"""

    # pylint: disable=too-few-public-methods

    def __ne__(self, other):
        return not self.__eq__(other)

    def __eq__(self, other):
        raise NotImplementedError


class Rule(AST):
    """Represents a rule"""

    rule_counter = 0

    def __init__(self, head, body):
        self.id = Rule.rule_counter
        Rule.rule_counter += 1
        self.head = head
        self.body = body
        head.pin_variables(self.id)
        for atom in body:
            atom.pin_variables(self.id)

    def body_variables(self):
        """Body variables of a rule as a set."""
        return set(v for x in self.body for v in x.variables())

    def head_variables(self):
        """Head variables of a rule"""
        return set(self.head.variables())

    def head_table(self):
        """Table introduced by the rule"""
        return self.head.table

    def body_tables(self):
        """All tables used by the rule"""
        return set(atom.table for atom in self.body)

    def __repr__(self):
        return "{}: {} :- {}".format(self.id, self.head, self.body)

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return other.head == self.head and other.body == self.body
        return False


class Atom(AST):
    """Represents an atom either in the head or body

    * table: a string, the name of the predicate
    * args: ast.Expr list, the arguments of the atom
    * negated: boolean, whether the predicate is negated or not
    * labels: string list, arguments are initially labelled for primitive
        tables
    * types: string list, the types of the arguments (used by typechecker only)
    """

    def __init__(self, table, args, negated=False, labels=None):
        self.table = table
        self.args = args
        self.negated = negated
        self.labels = labels
        self.types = None

    def variables(self):
        """Variables of the atom"""
        return set(v for x in self.args for v in x.variables())

    def pin_variables(self, rule_id):
        """Make variables distinct by adding the rule_id"""
        for arg in self.args:
            arg.pin_variables(rule_id)

    def __repr__(self):
        return "{}{}({})".format(
            "~" if self.negated else "",
            self.table,
            (', '.join('{} = {}'.format(lab, val)
                       for (lab, val) in zip(self.labels, self.args))
             if self.labels is not None
             else ', '.join(str(val) for val in self.args)))

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return (other.table == self.table and other.args == self.args and
                    other.negated == self.negated and
                    other.labels == self.labels)
        return False


class Expr(AST):
    "An abstract expression with an optional"

    def __init__(self, dtype=None):
        self.type = dtype

    def variables(self):
        """Free variables (default is none)

        :returns: the set of variables full identifiers (string x int)
        """
        # pylint: disable=no-self-use
        return set()

    def __eq__(self, other):
        raise NotImplementedError

    def pin_variables(self, rule_id):
        """Variable pining

        Pinning a variable associates it to a single rule. Default operation
        on expr is nothing.
        """
        pass


class Variable(Expr):
    """A variable (scope rule)

    :param ident: the name of the variable
    :param dtype: an optional type constraint
    """

    def __init__(self, ident, dtype=None):
        super(Variable, self).__init__(dtype=dtype)
        # pylint: disable=invalid-name
        self.id = ident
        self.rule_id = None

    def variables(self):
        return set([self.full_id()])

    def __repr__(self):
        expr_repr = (
            self.id if self.type is None
            else "{}:{}".format(self.id, self.type))
        return expr_repr

    def __hash__(self):
        return hash((self.id, self.rule_id))

    def pin_variables(self, rule_id):
        self.rule_id = rule_id

    def full_id(self):
        "Unique name of the variable valid in program scope."
        return (self.id, self.rule_id)

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return other.full_id() == self.full_id()
        return False


class Operation(Expr):
    """An n-ary operation

    :param oper: the name of the operation
    :param args: the AST of the arguments of the operation
    :param type: an optional type constaint.
    """

    def __init__(self, oper, args, dtype=None):
        super(Operation, self).__init__(dtype=dtype)
        self.operation = oper
        self.args = args
        self.var_types = None  # type variable for polymorphic operators.

    def variables(self):
        return set(v for x in self.args for v in x.variables())

    def pin_variables(self, rule_id):
        for arg in self.args:
            arg.pin_variables(rule_id)

    def __repr__(self):
        return "{}({})".format(self.operation, self.args)

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return (other.operation == self.operation and
                    other.args == self.args)
        return False


class NumConstant(Expr):
    "A numeric constant"

    def __init__(self, val, dtype='int'):
        super(NumConstant, self).__init__(dtype=dtype)
        self.val = val

    def __repr__(self):
        return str(self.val)

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return other.val == self.val and other.type == self.type
        return False


class StringConstant(Expr):
    """A string constant

    :param val: the value of the string
    :param typ: The type used
    """

    def __init__(self, val, dtype='string'):
        super(StringConstant, self).__init__(dtype=dtype)
        self.val = val

    def __repr__(self):
        return '"{}"'.format(self.val)

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return other.val == self.val and other.type == self.type
        return False


class BoolConstant(Expr):
    """A boolean constant

    :param val: the boolean value (as a bool)
    """

    def __init__(self, val):
        super(BoolConstant, self).__init__(dtype='bool')
        self.val = val

    def __repr__(self):
        return str(self.val)

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return other.val == self.val
        return False


class IpConstant(Expr):
    """An ip address constant

    :param val: ip address represented as a string
    """

    # pylint: disable=too-few-public-methods

    def __init__(self, val):
        super(IpConstant, self).__init__(dtype='ip_address')
        self.val = val

    def __repr__(self):
        return self.val

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return other.val == self.val
        return False


class Constant(AST):
    """A constant to be substituted"""

    # pylint: disable=too-few-public-methods

    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name

    def pin_variables(self, rule_id):
        pass

    def variables(self):
        """Free variables (default is none)"""
        # pylint: disable=no-self-use
        return set()

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return other.name == self.name
        return False
