=========================
Octant installation guide
=========================


The preferred installation is through the use of pip.

.. code-block:: console

    sudo pip install octant-1.0.0.tgz

octant can be installed from source with setup.

.. code-block:: console

    cd octant
    python setup.py build
    sudo python setup.py install

It must be configured with a config file describing how to connect to the
OpenStack APIs. Here is an example sample.conf file:

.. code-block:: console

    [openstack]
    www_authenticate_uri=http://192.168.122.10/identity
    user_name=admin
    password=secret
    user_domain_name=default
    region_name=RegionOne

It defines the access for an admin on a cloud where keystone is available on
machine at address 192.168.122.10. It is recomended to not specify the password
in a production environment. In that case the password will be asked
interactively.

If you use an https endpoint and the certificate cannot be verified, you can
add ``verify=False`` to the configuration file.

If you run the queries as a regular user on your projects or if you are the
admin user but you want to restrict the queries to a specific project, you must
set ``all_projects=False`` in the configuration file. This is the equivalent of
``openstack server list --all-projects``.

A similar section can be written to connect to a running skydive instance.
Skydive connection must be explicitly enabled.

.. code-block:: console

    [skydive]
    enabled=true
    endpoint=127.0.0.1:8082
    user_name=admin
    password=secret
