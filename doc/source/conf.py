# -*- coding: utf-8 -*-
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
# implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import os
import sys

from sphinx.ext.apidoc import main

sys.path.insert(0, os.path.abspath('../..'))
# -- General configuration ----------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom ones.
extensions = [
    'sphinx.ext.autodoc',
    'oslo_config.sphinxext',
    'oslo_config.sphinxconfiggen',
]

# autodoc generation is a bit aggressive and a nuisance when doing heavy
# text edit cycles.
# execute "export SPHINX_DEBUG=1" in your terminal to disable

# The suffix of source filenames.
source_suffix = '.rst'

# The master toctree document.
master_doc = 'index'

# General information about the project.
project = u'octant'
copyright = u'2018, Orange'

# If true, '()' will be appended to :func: etc. cross-reference text.
add_function_parentheses = True

# If true, the current module name will be prepended to all description
# unit titles (such as .. function::).
add_module_names = True

# The name of the Pygments (syntax highlighting) style to use.
pygments_style = 'sphinx'

# -- Options for HTML output --------------------------------------------------

# The theme to use for HTML and HTML Help pages.  Major themes that come with
# Sphinx are currently 'default' and 'sphinxdoc'.
# html_theme_path = ["."]
# html_theme = '_theme'
# html_static_path = ['static']
html_theme = 'default'

# Output file base name for HTML help builder.
htmlhelp_basename = '%sdoc' % project

# Grouping the document tree into LaTeX files. List of tuples
# (source start file, target name, title, author, documentclass
# [howto/manual]).
latex_documents = [
    ('index',
     '%s.tex' % project,
     u'%s Documentation' % project, 'Orange',
     'manual'),
]

# Example configuration for intersphinx: refer to the Python standard library.
# -- Options for oslo_config.sphinxconfiggen ---------------------------------

config_generator_config_file = [
    ('../../etc/octant-config-generator.conf',
     'static/octant')
]


def run_apidoc(_):
    main([
        "-f", "-o", "doc/source/reference", "octant/",
        "octant/tests/*.py", "octant/front/parser.py"])


def setup(app):
    app.connect('builder-inited', run_apidoc)
