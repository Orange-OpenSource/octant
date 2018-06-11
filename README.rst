===============================
octant
===============================

Octant is a front-end for the Z3 SMT solver that makes it usable on data
available on OpenStack rest API.

It can be used by cloud admins to check various
policies on their deployments (double attachment, reachability, etc.)

* Free software: Apache 2.0 license
* Documentation: see the code and the ``/doc`` directory
* Bugs: use the *Issues* tab in GitHub

Features
--------

* Simple typed datalog that uses Z3 fixed-point solver.
* Access to the main Neutron, Nova  and Keystonetables (networks, ports,
  security groups, routers, servers, projects, users)
* Optional access to Skydive (https://github.com/skydive-project/skydive)
  data representing the low-level configuration of the cloud infrastructure.
