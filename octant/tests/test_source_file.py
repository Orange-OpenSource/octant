# -*- coding: utf-8 -*-

# Licensed under the Apache License, Version 2.0 (the "License"); you may
# not use this file except in compliance with the License. You may obtain
# a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.

"""
test_source_file
----------------------------------

Tests File (backup) datasource
"""

import six

from octant import base as obase
from octant import source_file as source
from octant.tests import base


DESCR1 = """c1,f1:int16,f2:bool

c2,f3:id

"""

DESCR2 = "c1,f1,f2:bool\n"


class TestSourceFile(base.TestCase):
    """Basic test class"""

    def test_load_description(self):
        fd = six.StringIO(DESCR1)
        tables = {}
        source.loadDescription(tables, "file", fd)
        self.assertEqual(2, len(tables.keys()))
        self.assertEqual(421, tables['c1'][0](421))
        l1 = tables['c1'][1]
        self.assertEqual(2, len(l1.keys()))
        self.assertEqual([], l1['f1'][1](421))
        self.assertEqual('int16', l1['f1'][0])
        self.assertEqual('bool', l1['f2'][0])
        l2 = tables['c2'][1]
        self.assertEqual(1, len(l2.keys()))
        self.assertEqual('id', l2['f3'][0])

    def test_load_description_bad(self):
        fd = six.StringIO(DESCR2)
        tables = {}
        self.assertRaises(
            obase.Z3SourceError, source.loadDescription,
            tables, "file", fd)
