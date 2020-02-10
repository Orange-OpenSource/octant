=================
Efficient Datalog
=================

Network Oriented Datalog
========================
The power of octant comes from its use of Z3 Network Oriented Datalog (NoD).
Network Oriented Datalog uses differences of cubes, a powerful representations
of bit vectors tailored for networking: in short, they can efficiently
represent the set of network headers that will execute a given routing
rule in a switch because networking hardware use very similar filtering
constructs with variations depending on the context.

Each time a datalog program must filter a set of variables using bitwise
boolean operations or comparisons with filters ordered according to a given
priority, NoD is probably the only way to have a program that scales
correctly with the size of the variable.

To use NoD, one must activate it in the configuration (``doc=true``)
or using the command line option ``--doc``.

Datalog Transformation
======================
But the use of NoD comes with its own constraints. An NoD program should
avoid operations like ``X=Y&Z`` or ``X<Y`` where ``X``, ``Y`` and ``Z`` are
variables. But this is not always possible if we want to parameterize our
programs by the topology of the network modelled.

The solution is to either manually pre-process the data... or to use octant
automatic transformations that allow the end user to keep its program generic.

Rule Specialization
-------------------
The compiler will try to inline the values of arguments coming from the
Extentional Database (EDB) in order to reduce the number of variables
in primitive predicates using comparison and bitwise operations.

The transformation combines a type system to find which EDB table contributes to
the potential values of a variable, a heuristic to choose the variables to
inline and a standard rule rewriting to perform the transformation itself.

Predicate Specialization
------------------------
When a set of arguments of a predicate are always constants in the head of
the rules defining the predicate, the generic predicate can be replaced by
specialized ones. The generic predicate will be defined as the union of the
specialized ones and will be used when not enough arguments are supplied
in the uses.

Specialized predicates have more compact representations and can improve
the performance of queries in significant ways. To provide oportunities of
predicate specialization, we use rule specialization, especially when
argument types are ``id``. ``id`` should be used to uniquely represent
objects of the real world in the EDB (server, switch, port, rules, etc.).
Openstack typically uses ``uuid`` for idents.



