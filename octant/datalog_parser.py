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

"""Parser for the Datalog dialect used."""

from __future__ import print_function

import six

from ply import lex
from ply import yacc

from octant import base
from octant import datalog_ast as ast


# Not changing ply conventions because of pylint
# pylint: disable=invalid-name

tokens = (
    'IDENT', 'VAR', 'NUMBER', 'STRING', 'IP', 'ENTAIL', 'OPAR', 'BANG',
    'CPAR', 'COLON', 'COMMA', 'EQUAL', 'DOT', 'TILDE', 'AMPERSAND', 'BAR',
    'LT', 'LE', 'GT', 'GE'
)

t_EQUAL = r'='
t_DOT = r'\.'
t_COLON = r':'
t_COMMA = r','
t_CPAR = r'\)'
t_OPAR = r'\('
t_ENTAIL = r':-'
t_TILDE = r'~'
t_AMPERSAND = r'&'
t_BANG = r'!'
t_BAR = r'\|'
t_IDENT = r'[a-z][a-zA-Z0-9_]*'
t_VAR = r'[A-Z][a-zA-Z0-9_]*'
t_LT = r'<'
t_GT = r'>'
t_LE = r'<='
t_GE = r'>='
t_ignore_COMMENT = r'\#.*'


# IP rule must have higher precedence than NUMBER. It must be specified
# before NUMBER and must be a function not a simple token.
def t_IP(t):
    r'\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}'
    t.value = six.text_type(t.value)
    return t


def t_NUMBER(t):
    r'-?\d+'
    try:
        t.value = int(t.value)
    except ValueError:
        print('Integer value too large %s at %d' % (t.value, t.lexer.lineno))
        t.value = 0
    return t


def t_STRING(t):
    r'("(\\"|\\\\|[^"\\])*")'
    t.value = t.value[1:-1].replace('\\\\', '\\').replace('\\"', '"')
    return t


t_ignore = ' \t'


def t_newline(t):
    r'\n+'
    t.lexer.lineno += t.value.count("\n")


def t_error(t):
    # pylint: disable=missing-docstring
    print("Illegal character '%s' at line %d" % (t.value[0], t.lexer.lineno))
    t.lexer.skip(1)


lexer = lex.lex()


precedence = (
    ('left', 'BAR'),
    ('left', 'AMPERSAND'),
    ('right', 'TILDE'),            # Unary not operator
)


def p_rule_list_one(t):
    'rule_list : rule'
    t[0] = [t[1]]


def p_rule_list_many(t):
    'rule_list : rule_list rule'
    t[1].append(t[2])
    t[0] = t[1]


def p_rule(t):
    'rule : predicate ENTAIL predicate_list DOT'
    t[0] = ast.Rule(head=t[1], body=t[3])


def p_rule_no_body(t):
    'rule : predicate DOT'
    t[0] = ast.Rule(head=t[1], body=[])


def p_predicate_list_one(t):
    'predicate_list : predicate'
    t[0] = [t[1]]


def p_predicate_list_many(t):
    'predicate_list : predicate_list COMMA predicate'
    t[1].append(t[3])
    t[0] = t[1]


def p_predicate(t):
    'predicate : positive'
    t[0] = t[1]


def p_neg_predicate(t):
    'predicate : BANG positive'
    t[2].negated = True
    t[0] = t[2]


def p_positive(t):
    'positive : IDENT OPAR expr_list CPAR'
    t[0] = ast.Atom(table=t[1], args=t[3])


def p_positive_named(t):
    'positive : IDENT OPAR expr_list_named CPAR'
    t[0] = ast.Atom(table=t[1], args=t[3][1], labels=t[3][0])


def p_positive_empty(t):
    'positive : IDENT OPAR CPAR'
    t[0] = ast.Atom(table=t[1], args=[])


def p_positive_eq(t):
    '''positive : expr EQUAL eexpr
                | expr LT eexpr
                | expr LE eexpr
                | expr GT eexpr
                | expr GE eexpr
    '''   # noqa: H405
    t[0] = ast.Atom(table=t[2], args=[t[1], t[3]])


def p_expr_list_one(t):
    'expr_list : expr'
    t[0] = [t[1]]


def p_expr_list_many(t):
    'expr_list : expr_list COMMA expr'
    t[1].append(t[3])
    t[0] = t[1]


def p_expr_named_one(t):
    'expr_list_named : IDENT EQUAL expr'
    t[0] = ([t[1]], [t[3]])


def p_expr_named_many(t):
    'expr_list_named : expr_list_named COMMA IDENT EQUAL expr'
    t[1][0].append(t[3])
    t[1][1].append(t[5])
    t[0] = t[1]


def p_expr_type(t):
    'expr : sexpr COLON IDENT'
    t[1].type = t[3]
    t[0] = t[1]


def p_expr_no_type(t):
    'expr : sexpr'
    t[0] = t[1]


def p_sexpr_number(t):
    'sexpr : NUMBER'
    t[0] = ast.NumConstant(t[1])


def p_sexpr_var(t):
    'sexpr : VAR'
    t[0] = ast.Variable(t[1])


def p_sexpr_string(t):
    'sexpr : STRING'
    t[0] = ast.StringConstant(t[1])


def p_sexpr_ip(t):
    'sexpr : IP'
    t[0] = ast.IpConstant(t[1])


def p_sexpr_ident(t):
    'sexpr : IDENT'
    t[0] = ast.Constant(t[1])


def p_eexpr_expr(t):
    'eexpr : expr'
    t[0] = t[1]


def p_eexpr_par(t):
    'eexpr : OPAR eexpr CPAR'
    t[0] = t[2]


def p_eexpr_par_type(t):
    'eexpr : OPAR eexpr CPAR COLON IDENT'
    t[2].type = t[5]
    t[0] = t[2]


def p_eexpr_and(t):
    'eexpr : eexpr AMPERSAND eexpr'
    t[0] = ast.Operation('&', [t[1], t[3]])


def p_eexpr_or(t):
    'eexpr : eexpr BAR eexpr'
    t[0] = ast.Operation('|', [t[1], t[3]])


def p_eexpr_not(t):
    'eexpr : TILDE eexpr'
    t[0] = ast.Operation('~', [t[2]])


def p_error(t):
    # pylint: disable=missing-docstring
    parser.count_error += 1
    if not t:
        print("Syntax error: EOF reached")
    else:
        print("Syntax error at token '%s' (line %d)" % (t.value, t.lineno))
        while True:
            tok = parser.token()
            if not tok or tok.type == 'DOT':
                break
        parser.restart()


parser = yacc.yacc(write_tables=False, debug=False)


def wrapped_parse(intext):
    """Parser entry point that resets the state of lexer and errors."""
    lexer.lineno = 1
    parser.count_error = 0
    result = parser.parse(intext)
    if parser.count_error > 0:
        raise base.Z3ParseError("{} errors".format(parser.count_error))
    return result


def parse_atom(query_str):
    """Parse a string considered as a query"""
    rules = wrapped_parse(query_str + ".")
    return rules[0].head


def parse_file(filename):
    """Parse a file"""
    with open(filename) as filestream:
        return wrapped_parse(filestream.read())
