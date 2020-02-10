--------------------
Command-line options
--------------------

Main options
------------

**--config-file** *path*
    Path to a configuration file describing how to connect to the OpenStack APIs
**--theory** *path*
    Path to a Datalog program. This option can be used multiple times
**--query** *datalog-expression*
    Text of a single query. This option can be used multiple times.
**--save** *file*
    Tell octant to save the values queried on the OpenStack cloud to a backup
    in *file*.
**--restore** *file*
    Tell octant to use the backup in *file* instead of querying an actual cloud.

Output control
--------------

**--pretty**
    Pretty prints the result (using tables).
**--csv**
    Result is given in CSV format.

Optimization
------------

**--doc**
    Uses Difference of Cubes (DoC) for predicate representation
**--nounfold**
    Disable the unfolding of rules when using DoC.
**--nospec**
    Disable the predicate specialization phase when using DoC.

Debugging
---------

**--time**
    Triggers the printing of timing information.
**--debug**
    Debug output
**--smt2** *file*
    Save the resulting Z3 program in a file in SMT2 format.
**--ipsize** *n*
    Internal use for benchmarking only (change the size of the ipaddress type)
