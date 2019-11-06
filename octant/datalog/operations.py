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

"""Primitive operations"""

import collections
from octant.datalog import z3_comparison as z3c

Operation = collections.namedtuple(
    'Operation',
    ['args', 'result', 'ty_vars', 'z3'])

OPERATIONS = {
    "&": Operation(args=[0, 0], result=0, ty_vars=1, z3=(lambda x, y: x & y)),
    "|": Operation(args=[0, 0], result=0, ty_vars=1, z3=(lambda x, y: x | y)),
    "~": Operation(args=[0], result=0, ty_vars=1, z3=(lambda x: ~x))
}

COMPARISON = {
    "=": (lambda args: args[0] == args[1]),
    ">": (lambda args: z3c.z3_gt(args[0], args[1])),
    ">=": (lambda args: z3c.z3_ge(args[0], args[1])),
    "<": (lambda args: z3c.z3_lt(args[0], args[1])),
    "<=": (lambda args: z3c.z3_le(args[0], args[1])),
}


def is_primitive(atom):
    """Checks if the atom is a primitive predicate"""
    return atom.table in COMPARISON
