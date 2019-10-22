#    Copyright 2019 Orange
#
#    Licensed under the Apache License, Version 2.0 (the "License"); you may
#    not use this file except in compliance with the License. You may obtain
#    a copy of the License at
#
#         http://www.apache.org/licenses/LICENSE-2.0
#
#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
#    WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
#    License for the specific language governing permissions and limitations
#    under the License.

""" Topology generator for Octant """
import ipaddress
import uuid


class Network(object):

    def __init__(self, name, prefix, routes=[], offset=-1):
        """Creates a network

        :param name: the name of the network
        :param prefix: the prefix as an integer offset by either offset
            or netsize
        :param routes: a list of external routes described as target network
            and local address of next hop.
        :param offset: offset of the network (default -1 means use global
            netsize)
        """

        self.id = uuid.uuid4()
        self.name = name
        self.routes = routes
        self.base = prefix
        self.prefix = None
        self.offset = offset


class Port(object):

    def __init__(self, network, address, sg=[]):
        """Create a port

        :param network: the name of the network to connect the port to
        :paam address: the local address of the port on the network as an int
        :param sg: an optional list of security groups names
        """

        self.id = uuid.uuid4()
        self.network = network
        self.address = address
        self.sg = sg


class Server(object):

    def __init__(self, name, ports):
        """Create a server

        :param name: the server name
        :param ports: a list of ports
        """

        self.id = uuid.uuid4()
        self.name = name
        self.ports = ports


class Router(object):

    def __init__(self, name, ports, routes=[]):
        """Create a router

        :param name: the router name
        :param ports: a list of ports
        :param routes: additional routes described as a triple target network,
            network and local address of next hop machine
        """

        self.id = uuid.uuid4()
        self.name = name
        self.ports = ports
        self.routes = routes


class SG(object):

    def __init__(self, name, rules):
        """Creates a security group

        :param name: name of security group
        :param rules: a list of security group rules.
        """

        self.id = uuid.uuid4()
        self.name = name
        self.rules = rules


class Rule(object):

    def __init__(
            self, dir='egress', min=0, max=65535,
            protocol='', net=None, sg=None):
        """Creates a rule in security group

        :param dir: direction of the rule
        :param min: min port value filtered by the rule
        :param max: max port value filtered by the rule
        :param protocl: protocol taken into account
        :param net: network name taken into acount
        :param sg: optional remote security group that
            filtered not should match
        """

        self.id = uuid.uuid4()
        self.min = min
        self.max = max
        self.dir = dir
        self.protocol = protocol
        self.net = net
        self.sg = sg


class Deployment(object):

    def __init__(self, descr, size=32, netsize=16):
        """Creates a deployment

        :param descr: a list of objects describing the deployment
        :param size:  the size of addresss
        :param netsize: the size of networks (length of host mask)
        """

        self.size = size
        self.netsize = netsize
        self.networks = {}
        self.servers = {}
        self.routers = {}
        self.sg = {}
        self.descr = descr

    def compile(self):
        """Compiles the deployment.

        Compiling a deployment will return a generator of textlines describing
        the resources in csv format.
        """

        self.networks = {}
        self.servers = {}
        self.routers = {}
        self.sg = {}
        for obj in self.descr:
            if isinstance(obj, Network):
                offset = obj.offset if obj.offset != -1 else self.netsize
                obj.prefix = ipaddress.ip_network(
                    (obj.base << offset, 32 - offset))
                self.networks[obj.name] = obj
            elif isinstance(obj, Server):
                self.servers[obj.name] = obj
            elif isinstance(obj, Router):
                self.routers[obj.name] = obj
            elif isinstance(obj, SG):
                self.sg[obj.name] = obj

        yield "subnet,gateway_ip,id"
        for obj in self.networks.values():
            gw = ipaddress.ip_address(
                int(obj.prefix.network_address) | 1).compressed
            yield "subnet,{},{}".format(gw, obj.id)

        def dump_port_addr(ports):
            for port in ports:
                net = self.networks[port.network]
                ip = ipaddress.ip_address(
                    int(net.prefix.network_address) | port.address).compressed
                yield "port_ip,{},{},{}".format(ip, port.id, net.id)

        yield "port_ip,ip,port_id,subnet_id"
        for obj in self.servers.values():
            yield from dump_port_addr(obj.ports)
        for obj in self.routers.values():
            yield from dump_port_addr(obj.ports)

        def dump_port_sg(ports):
            for port in ports:
                for sg in port.sg:
                    sg_id = self.sg[sg].id
                    yield "port_sg,{},{}".format(port.id, sg_id)

        yield "port_sg,port_id,sg_id"
        for obj in self.servers.values():
            yield from dump_port_sg(obj.ports)
        for obj in self.routers.values():
            yield from dump_port_sg(obj.ports)

        yield ("rule,direction,id,ip_version,port_range_max,"
               "port_range_min,protocol,remote_group_id,remote_ip_mask,"
               "remote_ip_prefix,security_group_id")
        for sg in self.sg.values():
            for rule in sg.rules:
                if rule.net is None:
                    prefix = '0.0.0.0'
                    mask = '0.0.0.0'
                else:
                    net = self.networks[rule.net]
                    prefix = net.prefix.network_address.compressed
                    mask = net.prefix.netmask.compressed

                remote_sg_id = (
                    self.sg[rule.sg].id if rule.sg is not None
                    else '-*-None-*-')
                yield "rule,{},{},ipv4,{},{},{},{},{},{},{}".format(
                    rule.dir,
                    rule.id,
                    rule.max,
                    rule.min,
                    rule.protocol,
                    remote_sg_id,
                    mask,
                    prefix,
                    sg.id
                )

        yield "server,id,name"
        for server in self.servers.values():
            yield "server,{},{}".format(server.id, server.name)

        yield "subnet_route,dest_mask,dest_prefix,next_hop,subnet_id"
        for network in self.networks.values():
            for (remote, addr) in network.routes:
                net = self.networks[remote]
                prefix = net.prefix.network_address.compressed
                mask = net.prefix.netmask.compressed
                next_hop = ipaddress.ip_address(
                    int(network.prefix.network_address) | addr).compressed
                yield "subnet_route,{},{},{},{}".format(
                    mask,
                    prefix,
                    next_hop,
                    network.id
                )

        yield "router_route,dest_mask,dest_prefix,next_hop,router_id"
        for router in self.routers.values():
            for (remote, nwk, addr) in router.routes:
                network = self.networks[nwk]
                net = self.networks[remote]
                prefix = net.prefix.network_address.compressed
                mask = net.prefix.netmask.compressed
                next_hop = ipaddress.ip_address(
                    int(network.prefix.network_address) | addr).compressed
                yield "router_route,{},{},{},{}".format(
                    mask,
                    prefix,
                    next_hop,
                    router.id
                )

        yield "router,id"
        for router in self.routers.values():
            yield "router,{}".format(router.id)

        def dump_port(ports, device_id):
            for port in ports:
                yield "port,{},{},{}".format(
                    device_id, port.id,
                    self.networks[port.network].id)

        yield "port,device_id,id,network_id"
        for obj in self.servers.values():
            yield from dump_port(obj.ports, obj.id)
        for obj in self.routers.values():
            yield from dump_port(obj.ports, obj.id)

    def dump(self, file=None):
        """Prints the deployment.

        :param file: optional output file name (stdout if none provided)
        """

        if file is None:
            for line in self.compile():
                print(line)
        else:
            with open(file, 'w') as fd:
                for line in self.compile():
                    print(line, file=fd)
