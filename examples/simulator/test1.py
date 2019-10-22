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

import argparse

import topology_gen as topo

DESCR = [
    topo.Network('N1', 1, routes=[('N3', 10)]),
    topo.Network('N2', 2),
    topo.Network('N3', 3),
    topo.Network('N4', 4, routes=[('N5', 10)]),
    topo.Network('N5', 5),
    topo.Router(
        'R1', [topo.Port('N1', 1), topo.Port('N2', 1), topo.Port('N4', 1)],
        routes=[('N5', 'N4', 10)]),
    topo.Router('R2', [topo.Port('N1', 10), topo.Port('N3', 1)]),
    topo.Router('R3', [topo.Port('N4', 10), topo.Port('N5', 1)]),
    topo.Server('M1', [topo.Port('N1', 21, ["SG1"])]),
    topo.Server('M2', [topo.Port('N2', 22, ["SG1"])]),
    topo.Server('M3', [topo.Port('N4', 23, ["SG1"])]),
    topo.Server('M4', [topo.Port('N5', 24, ["SG1"])]),
    topo.Server('M5', [topo.Port('N3', 25, ["SG1"])]),
    topo.Server('M6', [topo.Port('N1', 26, ["SG1"])]),
    topo.SG('SG1', [topo.Rule(sg='SG1'), topo.Rule(dir='ingress', sg='SG1')])
]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '-o', '--output',
        type=str, default=None, dest='output', help='Output file')
    parser.add_argument(
        '--netsize', type=int, default=5, dest='netsize', help='Prefix size')
    args = parser.parse_args()
    topo.Deployment(DESCR, netsize=args.netsize).dump(args.output)


if __name__ == "__main__":
    main()
