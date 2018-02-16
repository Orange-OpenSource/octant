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

from ply import lex
from ply import yacc

from octant import datalog_ast as ast

tokens = (
    'IDENT', 'VAR', 'NUMBER', 'STRING', 'ENTAIL', 'OPAR',
    'CPAR', 'COLON', 'COMMA', 'EQUAL', 'DOT', 'TILDE'
)

t_EQUAL = r'='
t_DOT = r'\.'
t_COLON = r':'
t_COMMA = r','
t_CPAR = r'\)'
t_OPAR = r'\('
t_ENTAIL = r':-'
t_TILDE = r'~'
t_IDENT = r'[a-z][a-zA-Z0-9_]*'
t_VAR = r'[A-Z][a-zA-Z0-9_]*'


def t_NUMBER(t):
    r'\d+'
    try:
        t.value = int(t.value)
    except ValueError:
        print('Integer value too large %s at %d' % (t.value, t.lexer.lineno))
        t.value = 0
    return t


def t_STRING(t):
    r'("(\\"|\\\\|[^"\\])*")'
    t.value = t.value[1:-1]
    return t


t_ignore = ' \t'


def t_newline(t):
    r'\n+'
    t.lexer.lineno += t.value.count("\n")


def t_error(t):
    print("Illegal character '%s' at line %d" % t.value[0])
    t.lexer.skip(1)

lexer = lex.lex()


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
    'predicate : TILDE positive'
    t[2].negated = True
    t[0] = t[2]


def p_positive(t):
    'positive : IDENT OPAR expr_list CPAR'
    t[0] = ast.Atom(table=t[1], args=t[3])


def p_positive_eq(t):
    'positive : sexpr EQUAL sexpr'
    t[0] = ast.Atom(table='eq', args=[t[1], t[3]])


def p_expr_list_one(t):
    'expr_list : expr'
    t[0] = [t[1]]


def p_expr_list_many(t):
    'expr_list : expr_list COMMA expr'
    t[1].append(t[3])
    t[0] = t[1]


def p_expr_named(t):
    'expr : IDENT EQUAL texpr'
    t[3].label = t[1]
    t[0] = t[3]


def p_expr_simple(t):
    'expr : texpr'
    t[0] = t[1]


def p_expr_type(t):
    'texpr : sexpr COLON IDENT'
    t[1].type = t[3]
    t[0] = t[1]


def p_expr_no_type(t):
    'texpr : sexpr'
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


def p_sexpr_ident(t):
    'sexpr : IDENT'
    t[0] = ast.Constant(t[1])


def p_error(t):
    if not t:
        print("Syntax error: EOF reached")
    else:
        print("Syntax error at %s" % t)
        while True:
            tok = parser.token()
            if not tok or tok.type == 'DOT':
                break
        parser.restart()


parser = yacc.yacc(write_tables=False, debug=False)


def parse_atom(str):
    rules = parser.parse(str + ".")
    return rules[0].head


def parse_file(filename):
    with open(filename) as file:
        return parser.parse(file.read())
