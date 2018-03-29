===============================
octant
===============================

Octant is a front-end for the Z3 SMT solver that makes it usable on data
available on OpenStack rest API.

Check-reach is a tool that can be used by cloud admins to check various
policies on their deployments (double attachment, reachability, etc.)

* Free software: Apache 2.0 license
* Documentation: see the code and the ``/doc`` directory
* Bugs: use the *Issues* tab in GitHub

Features
--------

* Access to the main Neutron and Nova tables (networks, ports,
  security groups, routers, servers)
* Simple typed datalog that uses BDD backed Z3 fixed-point solver.
