
--------------------
The Datalog Language
--------------------

Datalog is a fragment of Prolog. Datalog operates on literals. A literal is an
atomic formula or its negation. An atomic formula is a term like ``p(T1,...Tn)``
where ``p`` is a predicate and ``Ti`` are either variables or constants
(booleans, numbers, strings or OpenStack ids in our setting).

Some predicates are defined by the context. In our case, these are facts about
the OpenStack instance. This is known as the extensive database in the
litterature. The goal of a Datalog program is to describe new predicates.

A Datalog program is a set of rules and each rule is a Horn clause:

.. code-block:: console

    p(T1...Tn) :- q1(T11...T1n), ... qn(Tk1 ... Tkn).

* ``p(T1...Tn)`` is called the head of the clause.
* ``q1(T11...T1n), ... qn(Tk1 ... Tkn)`` is called the body of the clause.
* The body may be empty. In that case the rule is written ``p(T1...Tn).`` and is
  called a fact (do not forget the dot at the end of clauses).

Such a Horn clause contributes to the definition of the predicate ``p`` by adding
new facts. A litteral is true if it either directly stated as a fact or if it is
an instantiation of the head of a rule such for a substitiont of the variables
that make true all the litterals appearing in the body.

More formally, let ``X1``...``Xm`` be the variables appearing in the rule. Let
``V1``...``Vm`` be constant expression (also known as ground expression).
We denote ``E[X1 <-V1 ... Xm <-Vm]`` either ``E`` if ``E`` is not a variable
or ``Vk`` if ``E`` is variable ``Xk``.

``p(T1[X1 <-V1 ... Xm <-Vm], ... Tn[X1 <-V1 ... Xm <-Vm])``
is true if for every predicate of the body
``qi(Ti1[X1 <-V1 ... Xm <-Vm], Tin[X1 <-V1 ... Xm <-Vm])``
is true.

The set of facts that can be deduced from a Datalog program is independent of
the order of the rules. In that sense Datalog is truly declarative.

It is important to understand that Z3 operates on finite terms and that it
represents predicates as tables. Limiting the size of predicates is crucial
for keeping good performances.
In particular too generic predicates can lead to tables too large to represent
and it may be safer to specialize them from the start.

For similar reasons Datalog Z3 is typed. Each parameter predicate must have a
unique type that will determin how it is represented internally. Polymorphic
predicates are not possible and if a variable appears free in the head of a
rule, it must be constrained by a type (In standard Datalog, variables
appearing in the head must appear in the body. The type constraint act as an
implicit body litteral that restricts the potential values of the variable).

It is also important to understand that Z3 does not operate on strings in those
cases but on opaque ids representing string in a unique manner. It is not
possible to use string operations.

Datalog Grammar
===============

The BNF grammar of the simple Datalog is the following.

Comments begin with a dash and extend to the end of the line.
A program is a sequence of rules. Each rule is Horn clause terminated by a dot.
The clause may have a body or not. The body is a list
of litterals separated by commas and terminated by a dot.

.. productionlist::
   rule_list: `rule`
            : `rule_list` `rule`
   rule : `litteral` "|-" `litteral_list` "."
        : `litteral` "."
   litteral_list : `litteral`
                 : `litteral_list` "," `litteral`

The litterals building the clause are defined by a predicate identifier and
a list of expressions between parenthesis and separated by commas. Predicate
identifiers MUST begin with a lower-case letter. A litteral may also be an
equality.

An optional exclamation mark at the begining of a litteral indicates a negated litteral.
The use of negation in Datalog is constrained to ensure that there is no
recursive loops between predicates using negation.
Octant will not check that the use of negation is stratified but Z3 will.

.. productionlist::
   litteral : "!"? positive
   positive : `IDENT` "(" `expr_list` ")"
            : sexpr "=" eexpr
            : sexpr ">" eexpr
            : sexpr ">=" eexpr
            : sexpr "<" eexpr
            : sexpr "<=" eexpr
   expr_list : `expr`
             : `expr_list` "," `expr`

When the predicate is a primitive OpenStack table, the expression MUST be
preceded by a label followed by an equal symbol.
The label identifies the field used in the table and the position of the
expression in the argument list is no more relevant.
If the predicate is defined by the user, expressions MUST NOT be preceded
by a label. The list of available fields for primitive Openstack tables is
given in section :ref:`exported-tables`.

.. productionlist::
   expr : `IDENT` "=" `texpr`
        : `texpr`

Optionnally expressions may be explicitly typed. The type constraint is
introduced by a colon and the type is a simple identifier. Expressions are
either constants or variables. Integers are classical 32 bit integers,
variable names MUST begin with an upper-case letter.
Strings must be enclosed between double-quotes and backslash is the escape
character.
Finally idents represent octant constants. Existing constants are described
in section :ref:`exported-types`.

.. productionlist::
   texpr : `sexpr` ":" `IDENT`
         : `sexpr`
   sexpr : `INTEGER` | `VAR` | `STRING` | `IDENT`
   eexpr : `eexpr` "|" `expr` | `eexpr` "&" `expr` | '~' `eexpr`
         : `sexpr`

Datalog Queries
===============
Queries are regular litterals. They can contain variables. The result of
a query is either True or False for a query without variables or a list of
lists. Each sublist correspond to an instantiation of all the variables that
appear in the query in the order of appearance  that makes the litteral valid.
