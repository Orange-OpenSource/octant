-------------------------
Skydive Exported Tables
-------------------------

We have chosen to prefix each Skydive table with ``sk_``

Nodes
=====

sk_host
-------
================  =======  =========================================
FieldName         Type     Description
================  =======  =========================================
id                id       An internal id for the node
name              string   The name of the host
platform          string   The OS flavour (typically ubuntu, debian)
================  =======  =========================================

sk_ovsswitch
------------
================  =======  =========================================
FieldName         Type     Description
================  =======  =========================================
id                id       An internal id for the node
name              string   The name of the openvswitch instance
================  =======  =========================================

sk_ovsbridge
------------
================  =======  =========================================
FieldName         Type     Description
================  =======  =========================================
id                id       An internal id for the node
name              string   The name of the bridge
================  =======  =========================================

sk_ovsport
----------
================  =======  =========================================
FieldName         Type     Description
================  =======  =========================================
id                id       An internal id for the node
name              string   The name of the host
================  =======  =========================================

sk_rule
-------
================  =======  =========================================
FieldName         Type     Description
================  =======  =========================================
id                id       Openflow rule identifier
priority          int      Priority of the rule
table             int      Table hosting the rule on the switch
================  =======  =========================================

sk_action
---------
================  =======  =========================================
FieldName         Type     Description
================  =======  =========================================
rule_id           id       Id of the rule containing the action
element           string   Action content
position          int      Position in the rule
================  =======  =========================================

sk_filter
---------
================  =======  =========================================
FieldName         Type     Description
================  =======  =========================================
rule_id           id       Id of the rule containing the action
element           string   Filter content
position          int      Position in the rule
================  =======  =========================================

Edges
=====

sk_owns
-------
================  =======  =========================================
FieldName         Type     Description
================  =======  =========================================
owner             id       Owner
item              id       Owned item
================  =======  =========================================

sk_l2
-----
================  =======  =========================================
FieldName         Type     Description
================  =======  =========================================
a                 id       One end (no order implied)
b                 id       Other end (no order implied)
================  =======  =========================================
