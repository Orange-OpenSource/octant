===========
Users guide
===========
`octant` is a tool that can check properties on live instances of a cloud. It
can be used to check conformance properties (double attachment, isolation,
etc.)

Properties are expressed in a declarative language: Datalog. `octant` uses Z3
as back-end, a very fast SMT solver developped by Z3 that offers
a Datalog engine as an option.

.. toctree::
   :maxdepth: 2

   invocation
   configuration
   command_line
   datalog
   types
   openstack
   skydive
   example
