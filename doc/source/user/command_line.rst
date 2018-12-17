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
**--save** *file*
    Tell octant to save the values queried on the OpenStack cloud to a backup
    in *file*.
**--restore** *file*
    Tell octant to use the backup in *file* instead of querying an actual cloud.
