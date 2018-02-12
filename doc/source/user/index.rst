===========
Users guide
===========
`octant` is a tool that can check properties on live instances of a cloud. It
can be used to check conformance properties (double attachment, isolation,
etc.)

`octant` requires three kind of entries:

* A configuration file to connect to an OpenStack cloud as admin.
* One or several rule files that define the Datalog program and the data
  to retrieve
* One or several queries to ask.

Here is a typical octant invocation:

.. code-block:: console

    octant --config-file connection.conf --theory program.dtl --query 'question(X,Y)'

octant uses Z3 as back-end, a very fast SMT solver developped by Z3 that offers
a Datalog engine as an option.

------------------
Configuration file
------------------

.. show-options::
   :config-file: etc/octant-config-generator.conf

--------------------
Command-line options
--------------------

**--config-file** *path*
    Path to a configuration file describing how to connect to the OpenStack APIs
**--theory** *path*
    Path to a Datalog program. This option can be used multiple times
**--query** *datalog-expression*
     Text of a single query. This option can be used multiple times.
**--time**
      Triggers the printing of timing information.

--------------------
The Datalog Language
--------------------
Datalog is a fragment of Prolog. Datalog operates on literals. A literal is an
atomic formula or its negation. An atomic formula is a term like `p(T1,...Tn)`
where `p` is a predicate and `Ti` are either variables or constants
(booleans, numbers, strings or OpenStack ids in our setting).

Some predicates are defined by the context. In our case, these are facts about
the OpenStack instance. This is known as the extensive database in the
litterature. The goal of a Datalog program is to describe new predicates.

A Datalog program is a set of rules and each rule is a Horn clause:

.. code-block:: console

    p(T1...Tn) :- q1(T11...T1n), ... qn(Tk1 ... Tkn).

* `p(T1...Tn)` is called the head of the clause.
* `q1(T11...T1n), ... qn(Tk1 ... Tkn)` is called the body of the clause.
* The body may be empty. In that case the rule is written `p(T1...Tn).` and is
  called a fact (do not forget the dot at the end of clauses).

Such a Horn clause contributes to the definition of the predicate `p` by adding
the facts `p(T1...Tn)` for instantiations of the variables in `Ti` that
make every litteral qi(Ti1...Tin) true.

It is important to understand that Z3 operates on finite terms and that it
represents predicates as tables. Limiting the size of predicates is crucial
for keeping good performances.
In particular too generic predicates can lead to tables too large to represent
and it may be safer to specialize them from the start.

It is also important to understand that Z3 does not operate on strings in those
cases but on opaque ids representing string in a unique manner. It is not possible
to use string operations.

The BNF grammar of the simple Datalog is the following.

A program is a sequence of rules. Each rule is Horn clause terminated by a dot.
The clause may have a body or not.

.. productionlist::
   rule_list: `rule`
            : `rule_list` `rule`
   rule : `litteral` "|-" `litteral_list` "."
        : `litteral` "."
   litteral_list : `litteral`
                 : `litteral_list` "," `litteral`

The litterals building the clause are defined by a predicate and a list of
arguments between parenthesis and separated by commas. Idents MUST begin with 
a lower-case letter.

.. productionlist::
   litteral : `IDENT` "(" `expr_list` ")"
   expr_list : `expr`
             : `expr_list` "," `expr`
   expr : `IDENT` "=" `texpr`
   expr : `texpr`

Optionnally expressions may be explicitly typed. The type constraint is introduced
by a colon and the type is a simple identifier. Expressions are either constants
or variables. Integers are classical 32 bit integers, variable names MUST begin with an
upper-case letter.
Strings must be enclosed between double-quotes and backslash is the escape
character.

.. productionlist:: 
   texpr : `sexpr` ":" `IDENT`
   texpr : `sexpr`
   sexpr : `INTEGER` | `VAR` | `STRING`

-------------------------
Openstack Exported Tables
-------------------------

network
=======

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the network
name        string   network name
project_id  id       id of owner project
==========  =======  =======================

router
======

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the router
name        string   router name
project_id  id       id of owner project
status      string   status of router
==========  =======  =======================

port
====

==========  =======  ===============================
FieldName   Type     Description
==========  =======  ===============================
id          id       id of the router
name        string   router name
host        string   name of hosting compute node
project_id  id       id of owner project
network_id  id       name of network
device_id   id       name of device having the port
==========  =======  ===============================


subnet
======

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the router
name        string   router name
project_id  id       id of owner project
network_id  id       name of network
ip_version  int      4 or 6
==========  =======  =======================


acl
===

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the router
name        string   router name
project_id  id       id of owner project
==========  =======  =======================

server
======

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the router
name        string   router name
project_id  id       id of owner project
host        string   name of hosting compute
==========  =======  =======================


----------
An Example
----------

We want to check if a network is connected to a known pool of networks
representing for example internet access or a corporate internal network
through a sequence of routers. To simplify, we will not look at actual routes 
or ACL but only at the existence of a path.

Let us call `root1` the litteral defining the roots of the first group of
networks. `root1("N1").` means that network whose name is "N1" belongs to the
group. It must be provided extensively by the operator as a list of facts (This
can be in a separate file generated automatically).

The program computing the networks accessible from those roots is the following:

.. code-block:: console

  linked(X,Y) :-
      port(id=Z, network_id=X, device_id=T),
      router(id=T, name=U),
      port(id=V, network_id=Y, device_id=T).
  connect1(X) :- root1(Y), network(id=X, name=Y).
  connect1(X) :- linked(X, Y), connect1(Y).
  connectName1(Y) :- network(id=X, name=Y), connect1(X).

`linked` defines the fact that two networks are directly connected (through a
router). It exploits the OpenStack tables for ports and routers.

`connect1` is defined inductively:

* The first clause (base case) states that a root network is member of
  `connect1`
* The second clause (inductive case) states that a network linked to a member
  of `connect1` is also a member of `connect1`

`connectName1` is used to retrieve the names of networks instead of unreadable
uuids.

A query will typically be `connectName1(X)` and will give back all the networks
connected.
