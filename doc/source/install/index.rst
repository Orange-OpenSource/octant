=========================
Octant installation guide
=========================


The preferred installation is through the use of pip.
octant can be installed from source with setup.

.. code-block:: console

    python setup.py build
    sudo python setup.py install

It must be configured with a config file describing how to connect to the
OpenStack APIs. Here is an example sample.conf file:

.. code-block:: console

    [DEFAULT]
    www_authenticate_uri=http://192.168.122.10/identity
    user_name=admin
    project_name=admin
    password=secret
    user_domain_name=default
    project_domain_name=default
    region_name=RegionOne


It defines the access for an admin on a cloud where keystone is available on
machine at address 192.168.122.10. It is recomended to not specify the password
in a production environment.

