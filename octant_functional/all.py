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

"""Functional Test Launcher"""

import csv
import os
import sys
import tempfile
import unittest


def subdirs(path):
    """Paths to subdirectories of a path"""
    return [
        os.path.join(path, sp)
        for sp in os.listdir(path)
        if os.path.isdir(os.path.join(path, sp)) and sp != "__pycache__"]


def files(path):
    """Names of files in a directory"""
    return [
        filename
        for filename in os.listdir(path)
        if os.path.isfile(os.path.join(path, filename))]


class TestDatalogFile(unittest.TestCase):
    """Launch a single test case

    A test case is defined by a folder containing:
    * an optional configuration (conf.cfg)
    * an optional backup file (backup.csv)
    * a theory (test.dtl)
    * a query (query.dtl)
    * an expected output (expected.csv)
    """

    def __init__(self, dirpath):
        super(TestDatalogFile, self).__init__()
        self.dirpath = dirpath

    def shortDescription(self):
        return self.dirpath

    def id(self):
        return self.dirpath

    # pylint: disable=invalid-name
    def runTest(self):
        """Overriden runTest"""
        all_files = files(self.dirpath)
        self.assertTrue('test.dtl' in all_files, "Needs a theory.")
        self.assertTrue('query.dtl' in all_files, "Needs a query.")
        self.assertTrue(
            'expected.csv' in all_files, "Needs an expected result.")
        opt_config = (
            " --config-file {}".format(os.path.join(self.dirpath, 'conf.cfg'))
            if 'conf.cfg' in all_files
            else "")
        opt_backup = (
            " --restore {}".format(os.path.join(self.dirpath, 'backup.csv'))
            if 'backup.csv' in all_files
            else "")
        opt_filesource = (
            " --filesource {}".format(os.path.join(self.dirpath, 'source.csv'))
            if 'source.csv' in all_files
            else ""
        )
        theory = os.path.join(self.dirpath, 'test.dtl')
        (outfd, outfile) = tempfile.mkstemp(suffix='.csv')
        # os.path.join(self.dirpath, 'out.csv')
        with open(os.path.join(self.dirpath, 'query.dtl'), 'r') as query_file:
            query = query_file.read().strip(' \t\n')
        cmd = ("{} -m octant.main --csv{}{}{}"
               " --theory {} --query '{}' > {}").format(
                   sys.executable,
                   opt_config,
                   opt_filesource,
                   opt_backup,
                   theory,
                   query,
                   outfile)
        os.system(cmd)
        with open(os.path.join(self.dirpath, 'expected.csv'), 'r') as csvfile:
            csvreader = csv.reader(csvfile)
            expected_contents = [row for row in csvreader][1:]
            expected_contents.sort()
        with os.fdopen(outfd, 'r') as csvfile:
            # with open(outfile, 'r') as csvfile:
            csvreader = csv.reader(csvfile)
            out_contents = [row for row in csvreader][1:]
            out_contents.sort()
        self.assertListEqual(expected_contents, out_contents)
        os.remove(outfile)


class All(unittest.TestSuite):
    "Test suite launching all functional tests"

    def __init__(self):
        super(All, self).__init__()
        curdir = os.path.dirname(os.path.abspath(__file__))
        cases = subdirs(curdir)
        for case_dir in cases:
            self.addTest(TestDatalogFile(case_dir))
