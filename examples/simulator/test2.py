import argparse

import topology_gen as topo


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        'size', type=int, help='Number of additional networks')
    parser.add_argument(
        '-o', '--output',
        type=str, default=None, dest='output', help='Output file')
    args = parser.parse_args()

    size = args.size

    aux_nets = [
        topo.Network('AN{}'.format(i), (256 + i) * 256, offset=8)
        for i in range(0, size)
    ]

    aux_routes_net = [('AN{}'.format(i), 10) for i in range(0, size)]

    aux_routes_router = [('AN{}'.format(i), 'N4', 10) for i in range(0, size)]

    aux_ports = [topo.Port('AN{}'.format(i), 1) for i in range(0, size)]

    descr = [
        topo.Network('N1', 1, routes=[('N3', 10)]),
        topo.Network('N2', 2),
        topo.Network('N3', 3),
        topo.Network('N4', 4, routes=[('N5', 10)] + aux_routes_net),
        topo.Network('N5', 5),
        topo.Router(
            'R1', [topo.Port('N1', 1), topo.Port('N2', 1), topo.Port('N4', 1)],
            routes=[('N5', 'N4', 10)] + aux_routes_router),
        topo.Router('R2', [topo.Port('N1', 10), topo.Port('N3', 1)]),
        topo.Router(
            'R3', [topo.Port('N4', 10), topo.Port('N5', 1)] + aux_ports),
        topo.Server('M1', [topo.Port('N1', 21, ["SG1"])]),
        topo.Server('M2', [topo.Port('N2', 22, ["SG1"])]),
        topo.Server('M3', [topo.Port('N4', 23, ["SG1"])]),
        topo.Server('M4', [topo.Port('N5', 24, ["SG1"])]),
        topo.Server('M5', [topo.Port('N3', 25, ["SG1"])]),
        topo.Server('M6', [topo.Port('N1', 26, ["SG1"])]),
        topo.SG(
            'SG1', [topo.Rule(sg='SG1'), topo.Rule(dir='ingress', sg='SG1')])
    ] + aux_nets

    topo.Deployment(descr, netsize=16).dump(args.output)


if __name__ == "__main__":
    main()
