# -*- coding: utf-8 -*-

# Copyright 2010-2011 OpenStack Foundation
# Copyright (c) 2013 Hewlett-Packard Development Company, L.P.
#
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

""" Test utilities for the project"""
from contextlib import contextmanager
import six
import sys

from oslotest import base


@contextmanager
def capture_stdout():
    old = sys.stdout
    try:
        sys.stdout = six.StringIO()
        yield sys.stdout
    finally:
        sys.stdout = old


class TestCase(base.BaseTestCase):

    """Test case base class for all unit tests."""
