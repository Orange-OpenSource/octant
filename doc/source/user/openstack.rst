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

Firewall as a service V1 (deprecated)
=====================================

firewall_rule_v1
----------------

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
policy_id           id           policy containing the rule
dest_prefix         ip_address   prefix for destination
dest_mask           ip_address   mask for destination
dest_port_min       int          first port for destination
dest_port_max       int          last port for destination
source_prefix       ip_address   prefix for source
source_mask         ip_address   mask for source
source_port_min     int          first port for source
source_port_max     int          last port for source
==================  ===========  =============================

firewall_policy_v1
------------------

=================  ===========  =============================
FieldName          Type         Description
=================  ===========  =============================
id                 id           firewall policy id
project_id         id           project containing the policy
name               string       name of policy
=================  ===========  =============================

firewall_v1
-----------

=================  ===========  ================================
FieldName          Type         Description
=================  ===========  ================================
id                 id           firewall id
name               string       name of firewall
project_id         id           project containing the firewall
policy_id          id           name of policy associated
status             status       status of firewall
enabled            bool         admin state of firewall
=================  ===========  ================================

firewall_router_v1
------------------

=================  ===========  ========================
FieldName          Type         Description
=================  ===========  ========================
firewall_id        id           firewall id
router_id          id           router id
=================  ===========  ========================

Firewall as a service V2 (current)
==================================

firewall_rule
-------------

==================  ===========  ========================================
FieldName           Type         Description
==================  ===========  ========================================
id                  id           id of firewall
name                string       name of firewall
enabled             bool         if the rule is active
shared              bool         whether it is shared with other projects
project_id          id           project defining the resource
ip_version          ip_version   ip version
protocol            string       protocol filtered
action              fw_action    action taken if rule matches
policy_id           id           policy containing the rule
dest_prefix         ip_address   prefix for destination
dest_mask           ip_address   mask for destination
dest_port_min       int          first port for destination
dest_port_max       int          last port for destination
source_prefix       ip_address   prefix for source
source_mask         ip_address   mask for source
source_port_min     int          first port for source
source_port_max     int          last port for source
==================  ===========  ========================================

firewall_policy
---------------

=================  ===========  =========================================
FieldName          Type         Description
=================  ===========  =========================================
id                 id           firewall policy id
project_id         id           project containing the policy
name               string       name of policy
shared             bool         whether it is shared with other projects
audited            bool         whether the rule is audited
=================  ===========  =========================================

firewall
--------

=================  ===========  ==============================================
FieldName          Type         Description
=================  ===========  ==============================================
id                 id           firewall id
name               string       name of firewall
project_id         id           project containing the firewall
ingress_policy_id  id           name of policy associated for incoming packets
egress_policy_id   id           name of policy associated for outgoing packets
status             status       status of firewall
enabled            bool         admin state of firewall
=================  ===========  ==============================================

firewall_port
-------------

=================  ===========  ========================
FieldName          Type         Description
=================  ===========  ========================
firewall_id        id           firewall id
port_id            id           port id
=================  ===========  ========================

firewall_rule_policy
--------------------

=================  ===========  =============================================
FieldName          Type         Description
=================  ===========  =============================================
rule_id            id           firewall rule id
policy_id          id           firewall policy id
position           int          position (priority) of the rule in the policy
=================  ===========  =============================================

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
