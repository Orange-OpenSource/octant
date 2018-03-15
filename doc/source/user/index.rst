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
**--pretty**
    Pretty prints the result (using tables).

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

.. _exported-types:

--------------------------
Types and  Constants
--------------------------

**bool**
    boolean. Values are **true** and **false**
**string**
    string constants. By default 65536 strings can be handled.
**int**
    small integers
**id**
    OpenStack ids (implemented as UUID by OpenStack). Use **none** to
    represent the absence of id
**ip_version**
    Ip version. Can be either **ipv4** or **ipv6**.
**status**
    Status of a neutron object. Can be either **active**, **down**, **build**,
    **error** or **other** (for unofficial extensions).
**direction**
    Direction of a security group rule: either **ingress** or **egress**.
**fw_action**
    Action associated to a firewall rule. Either **allow**, **deny**
    or **reject**.

.. _exported-tables:

-------------------------
Openstack Exported Tables
-------------------------

Networking (Neutron)
====================

network
-------

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the network
name        string   network name
project_id  id       id of owner project
status      status   status of network
==========  =======  =======================

router
------

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the router
name        string   router name
project_id  id       id of owner project
status      status   status of router
==========  =======  =======================

router_route
------------

===========  ==========  ==========================
FieldName    Type        Description
===========  ==========  ==========================
router_id    id          id of the router
dest_prefix  ip_address  prefix of destination cidr
dest_mask    ip_address  mask of destination cidr
next_hop     ip_address  next hop address
===========  ==========  ==========================


port
----

==========  =======  ===============================
FieldName   Type     Description
==========  =======  ===============================
id          id       id of the port
name        string   port name
host        string   name of hosting compute node
project_id  id       id of owner project
network_id  id       name of network
device_id   id       name of device having the port
status      status   status of port
==========  =======  ===============================

port_ip
-------

==========  ==========  =======================
FieldName   Type        Description
==========  ==========  =======================
port_id     id          id of the port
subnet_id   id          subnet id hosting port
ip          ip_address  ip on the subnet
==========  ==========  =======================

port_sg
-------

==========  ==========  ========================
FieldName   Type        Description
==========  ==========  ========================
port_id     id          id of the port
sg_id       id          id of the security group
==========  ==========  ========================

subnet
------

============  ==========  =======================
FieldName     Type        Description
============  ==========  =======================
id            id          id of the subnet
name          string      subnet name
project_id    id          id of owner project
network_id    id          id of network
ip_version    int         4 or 6
cidr_prefix   ip_address  address part of cidr
cidr_mask     ip_address  netmask part of cidr
gateway_ip    ip_address  ip of subnet gateway
============  ==========  =======================

subnet_route
------------

===========  ==========  ========================================
FieldName    Type        Description
===========  ==========  ========================================
subnet_id    id          id of the subnet where the route applies
dest_prefix  ip_address  prefix of destination cidr
dest_mask    ip_address  mask of destination cidr
next_hop     ip_address  next hop address
===========  ==========  ========================================

subnet_pool
-----------

================  =======  ===========================
FieldName         Type     Description
================  =======  ===========================
id                id       id of the subnet pool
name              string   subnet pool name
project_id        id       id of owner project
address_scope_id  id       id of address scope or none
ip_version        int      4 or 6
================  =======  ===========================

subnet_pool_prefix
------------------

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the subnet pool
prefix      string   address prefix
==========  =======  =======================

address_scope
-------------

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the address scope
name        string   address scope name
==========  =======  =======================

sg
--

==========  =======  ========================
FieldName   Type     Description
==========  =======  ========================
id          id       id of the security group
name        string   security group name
project_id  id       id of owner project
==========  =======  ========================

rule
----

=================  ===========  ========================
FieldName          Type         Description
=================  ===========  ========================
id                 id           id of the rule
ip_version         int          4 or 6
direction          string       direction of the rule
port_range_max     int          maximum port number
port_range_min     int          minimum port number
protocol           string       protocol filtered (or -)
remote_group_id    id           remote group id
remote_ip_prefix   ip_address   remote ip network prefix
remote_ip_mask     ip_address   netmask part of remote ip
security_group_id  id           security group id
project_id         id           id of owner project
=================  ===========  ========================

firewall_rule
-------------

==================  ===========  =============================
FieldName           Type         Description
==================  ===========  =============================
id                  id           id of firewall
name                string       name of firewall
enabled             bool         if the rule is active
ip_version          ip_version   ip version
protocol            string       protocol filtered
position            int          priority of the rule
action              fw_action    action taken if rule matches
firewall_policy_id  id           policy containing the rule
dest_prefix         ip_address   prefix for destination
dest_mask           ip_address   mask for destination
dest_port_min       int          first port for destination
dest_port_max       int          last port for destination
source_prefix       ip_address   prefix for source
source_mask         ip_address   mask for source
source_port_min     int          first port for source
source_port_max     int          last port for source
==================  ===========  =============================

firewall_policy
---------------

=================  ===========  =============================
FieldName          Type         Description
=================  ===========  =============================
id                 id           firewall policy id
project_id         id           project containing the policy
name               string       name of policy
=================  ===========  =============================

firewall
--------

=================  ===========  ================================
FieldName          Type         Description
=================  ===========  ================================
id                 id           firewall id
name               string       name of firewall
project_id         id           project containing the firewall
policy_id          id           name of policy associated
status             status       status of firewall
=================  ===========  ================================

firewall_router
---------------

=================  ===========  ========================
FieldName          Type         Description
=================  ===========  ========================
firewall_id        id           firewall id
router_id          id           router id
=================  ===========  ========================

Compute (Nova)
==============

server
------

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the server
name        string   server name
project_id  id       id of owner project
host        string   name of hosting compute
image_id    id       id of image
flavor_id   id       id of flavor
==========  =======  =======================

flavor
------

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the flavor
name        string   flavor name
vcpus       int      number of virtual cpus
ram         int      ram size (Mb)
disk        int      disk size (Gb)
public      bool     is flavour public
==========  =======  =======================

image
-----

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the image
name        string   image name
==========  =======  =======================

Identity (Keystone)
===================

project
-------

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the project
name        string   router name
domain_id   id       id of domain
parent_id   id       id of enclosing project
==========  =======  =======================

region
------

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the region
name        string   region name
parent_id   id       id of enclosing region
==========  =======  =======================

domain
------

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the domain
name        string   domain name
==========  =======  =======================

role
----

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the role
name        string   role name
==========  =======  =======================

user
----

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the user
name        string   user name
domain_id   id       id of domain
==========  =======  =======================

group
-----

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the group
name        string   group name
domain_id   id       id of domain
==========  =======  =======================

service
-------

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the service
name        string   service name
type        string   kind of service
==========  =======  =======================

endpoint
--------

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the endpoint
url         string   url of endpoint
service_id  id       id of service
region_id   id       id of region
==========  =======  =======================

role_assignment
---------------

==========  =======  =======================
FieldName   Type     Description
==========  =======  =======================
id          id       id of the group
name        string   group name
group_id    id       id of group
role_id     id       id or role
project_id  id       id of project scope
user_id     id       id of user 
==========  =======  =======================

----------
An Example
----------

We want to check if a network is connected to a known pool of networks
representing for example internet access or a corporate internal network
through a sequence of routers. To simplify, we will not look at actual routes
or ACL but only at the existence of a path.

Let us call ``root1`` the litteral defining the roots of the first group of
networks. ``root1("N1").`` means that network whose name is "N1" belongs to the
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

``linked`` defines the fact that two networks are directly connected (through a
router). It exploits the OpenStack tables for ports and routers.

``connect1`` is defined inductively:

* The first clause (base case) states that a root network is member of
  ``connect1``
* The second clause (inductive case) states that a network linked to a member
  of ``connect1`` is also a member of ``connect1``

``connectName1`` is used to retrieve the names of networks instead of unreadable
uuids.

A query will typically be ``connectName1(X)`` and will give back all the networks
connected.

Now we can define two sets of roots (``root1`` and ``root2``) and two associated
``connect1`` and ``connect2`` predicates. ``root1`` could be for example our
production networks and ``root2`` our test networks.

We would like to check if there exists VMs attached to a
network linked to ``root1`` and a network linked to ``root2``. Here is the
predicate that checks such double attachments:

.. code-block:: console

    connectVM1(X) :- port(id=Z, network_id=Y, device_id=X), connect1(Y).
    connectVM2(X) :- port(id=Z, network_id=Y, device_id=X), connect2(Y).

    doubleAttach(Y):- connectVM1(X), connectVM2(X), server(id=X, name=Y).

``connectVM1`` and ``connectVM2`` define devices that are connected to respectively
``root1`` and ``root2``.
``doubleAttach`` gives back the name of the VMs members of both groups. We use
the ``server`` primitive predicate to find the name of the VM.

Here is a sample output:

.. code-block:: console

    $ octant --config-file sample.conf --theory sample.dtl \
         --query 'connectName1("N12121")' --query 'connectName1("N21212")' \
         --query 'doubleAttach(X)' --time
    Parsing time: 0.0034239999999999826
    Data retrieval: 1.262298
    ********************************************************************************
    connectName1("N12121")
    Query time: 0.012639000000000067
    --------------------------------------------------------------------------------
        True
    ********************************************************************************
    connectName1("N21212")
    Query time: 0.011633999999999922
    --------------------------------------------------------------------------------
        False
    ********************************************************************************
    doubleAttach(X)
    Query time: 0.012620999999999993
    --------------------------------------------------------------------------------
        ['C1', 'C3']
    ********************************************************************************
