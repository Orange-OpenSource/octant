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
