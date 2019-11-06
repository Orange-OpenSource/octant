#    Copyright 2018 Orange
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

"""Octant entry point"""

import logging
import sys
import textwrap
import time


from oslo_config import cfg

from octant.common import base
from octant.common import primitives
from octant.datalog import theory as datalog_theory
from octant.front import options
from octant.front import parser
from octant.front import z3_result as z3r


def print_result(query, variables, answers, time_used, show_pretty):
    """Pretty-print the result of a query"""
    print("*" * 80)
    print(query)
    if time_used is not None:
        print("Query time: {}".format(time_used))
    print("-" * 80)
    if show_pretty:
        if isinstance(answers, list):
            z3r.print_pretty(variables, answers)
        else:
            print('   ' + str(answers))
    else:
        wrapped = textwrap.wrap(
            str(answers), initial_indent='    ', subsequent_indent='    ')
        for line in wrapped:
            print(line)


def main():
    """Octant entry point"""
    logging.basicConfig(stream=sys.stderr, level=logging.WARNING)
    args = sys.argv[1:]
    options.init(args)
    if cfg.CONF.ipsize != 32:
        primitives.TYPES['ip_address'] = (
            primitives.IpAddressType(size=cfg.CONF.ipsize))
    time_required = cfg.CONF.time
    csv_out = cfg.CONF.csv
    pretty = cfg.CONF.pretty
    debug = cfg.CONF.debug
    if debug:
        logging.getLogger().setLevel(logging.DEBUG)
    if csv_out and (time_required or pretty):
        print("Cannot use option --csv with --time or --pretty.")
        sys.exit(1)
    rules = []
    start = time.clock()
    try:
        for rule_file in cfg.CONF.theory:
            rules += parser.parse_file(rule_file)
    except base.Z3ParseError as exc:
        print(exc.args[1])
        sys.exit(1)
    if time_required:
        print("Parsing time: {}".format(time.clock() - start))
    start = time.clock()
    try:
        theory = datalog_theory.Z3Theory(rules)
        theory.build_theory()
        if time_required:
            print("Data retrieval: {}".format(time.clock() - start))
        for query in cfg.CONF.query:
            start = time.clock()
            variables, answers = theory.query(query)
            if csv_out:
                z3r.print_csv(variables, answers)
            else:
                print_result(
                    query, variables, answers,
                    time.clock() - start if time_required else None,
                    cfg.CONF.pretty)
        if not csv_out:
            print("*" * 80)
    except base.Z3NotWellFormed as exc:
        print("Badly formed program: {}".format(exc.args[1]))
        sys.exit(1)
    except base.Z3TypeError as exc:
        print("Type error: {}".format(exc.args[1]))
        sys.exit(1)
    except base.Z3SourceError as exc:
        print("Error in datasource: {}".format(exc.args[1]))
        sys.exit(1)
    except base.Z3ParseError:
        print("Parser error in query.")
        sys.exit(1)


if __name__ == '__main__':
    main()
