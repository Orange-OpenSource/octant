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

"""General purpose datastructures used by octant"""


class Z3ParseError(Exception):
    """Raised on syntax errors at end of parsing."""

    def __init__(self, *args, **kwargs):
        super(Z3ParseError, self).__init__(self, *args, **kwargs)


class Z3TypeError(Exception):
    """Raised for a theory that is not well typed"""

    def __init__(self, *args, **kwargs):
        super(Z3TypeError, self).__init__(self, *args, **kwargs)


class Z3SourceError(Exception):
    """Raised when a source or its description is wrong"""

    def __init__(self, *args, **kwargs):
        super(Z3SourceError, self).__init__(self, *args, **kwargs)


class Z3NotWellFormed(Exception):
    """Raised for a theory that do not respect well-formedness rules"""

    def __init__(self, *args, **kwargs):
        super(Z3NotWellFormed, self).__init__(self, *args, **kwargs)
