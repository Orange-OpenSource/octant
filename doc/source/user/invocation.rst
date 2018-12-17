----------
Invocation
----------
`octant` requires three kind of entries:

* A configuration file to connect to one or several sources of information:
  * an OpenStack cloud as admin,
  * a skydive analyzer.
* One or several rule files that define the Datalog program and the data
  to retrieve
* One or several queries to ask.

Here is a typical octant invocation:

.. code-block:: console

    octant --config-file connection.conf --theory program.dtl --query 'question(X,Y)'

Octant can also save and use backup files instead of an actual cloud as datasource.
Please keep in mind that backup files only contain values for fields that were
actually used by the theory loaded when the file was created.
