#    Copyright 2019 Orange
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


import six
import z3

from oslo_config import cfg

inferior_to = {}
superior_to = {}


def reset():
    """Reset the tables of comparison to constant predicates"""
    global inferior_to
    global superior_to
    inferior_to = {}
    superior_to = {}


def register_define(context, n, s, f, bit_is_set):
    """Register and define one comparison to constant

    :param context: z3 context to create predicate and rules
    :param n: the constant
    :param s: the size of domain
    :param f: the predicate implementing the comparison
    :param bit_is_set: when we check a bit, add a rule if set or not depending
        on the truth of this arg. This is the way we handle < and > in a single
        function.
    """
    context.register_relation(f)
    sort = f.domain(0)
    var = z3.Const('X', sort)
    glob_mask = (1 << s) - 1
    for p in range(s):
        bit = 1 << p
        if (n & bit != 0) == bit_is_set:
            mask = glob_mask ^ (bit - 1)
            prefix = (n & mask) ^ bit
            z3_prefix = z3.BitVecVal(prefix, sort)
            z3_mask = z3.BitVecVal(mask, sort)
            equation = z3_prefix == (var & z3_mask)
            context.rule(z3.ForAll([var], z3.Implies(equation, f(var))))


def register(context):
    """Register and define all the comparison to constant predicates"""
    for ((n, s), f) in six.iteritems(inferior_to):
        register_define(context, n, s, f, True)
    for ((n, s), f) in six.iteritems(superior_to):
        register_define(context, n, s, f, False)


def is_ground(v):
    "Check v is a bitvector constant"
    return isinstance(v, z3.BitVecNumRef)


def z3_mod(c, offset):
    return z3.BitVecVal(c.as_long() + offset, c.sort())


def z3_inf(v, c):
    n = c.as_long()
    s = c.size()
    f = inferior_to.get((n, s), None)
    if f is None:
        f = z3.Function("_inf_%d_%d" % (n, s), c.sort(), z3.BoolSort())
        inferior_to[(n, s)] = f
    return f(v)


def z3_sup(v, c):
    n = c.as_long()
    s = c.size()
    f = superior_to.get((n, s), None)
    if f is None:
        f = z3.Function("_sup_%d_%d" % (n, s), c.sort(), z3.BoolSort())
        superior_to[(n, s)] = f
    return f(v)


def z3_lt(arg1, arg2):
    if cfg.CONF.doc:
        if is_ground(arg1):
            return z3_sup(arg2, arg1)
        if is_ground(arg2):
            return z3_inf(arg1, arg2)
    return arg1 < arg2


def z3_gt(arg1, arg2):
    if cfg.CONF.doc:
        if is_ground(arg1):
            return z3_inf(arg2, arg1)
        if is_ground(arg2):
            return z3_sup(arg1, arg2)
    return arg1 > arg2


def z3_le(arg1, arg2):
    if cfg.CONF.doc:
        if is_ground(arg1):
            if arg1.as_long() == 0:
                return z3.BoolVal(True)
            return z3_sup(arg2, z3_mod(arg1, -1))
        if is_ground(arg2):
            return z3_inf(arg1, z3_mod(arg2, 1))
    return arg1 <= arg2


def z3_ge(arg1, arg2):
    if cfg.CONF.doc:
        if is_ground(arg1):
            return z3_inf(arg2, z3_mod(arg1, 1))
        if is_ground(arg2):
            if arg2.as_long() == 0:
                return z3.BoolVal(True)
            return z3_sup(arg1, z3_mod(arg2, -1))
    return arg1 >= arg2
