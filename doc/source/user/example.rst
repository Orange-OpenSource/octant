----------
An Example
----------

We want to check if a network is connected to a known pool of networks
representing for example internet access or a corporate internal network
through a sequence of routers. To simplify, we will not look at actual routes
or ACL but only at the existence of a path.

Let us call ``root1`` the litteral defining the roots of the first group of
networks. ``root1("N1").`` means that network whose name is "N1" belongs to the
group. It must be provided extensively by the operator as a list of facts (This
can be in a separate file generated automatically).

The program computing the networks accessible from those roots is the following:

.. code-block:: console

  linked(X,Y) :-
      port(id=Z, network_id=X, device_id=T),
      router(id=T, name=U),
      port(id=V, network_id=Y, device_id=T).
  connect1(X) :- root1(Y), network(id=X, name=Y).
  connect1(X) :- linked(X, Y), connect1(Y).
  connectName1(Y) :- network(id=X, name=Y), connect1(X).

``linked`` defines the fact that two networks are directly connected (through a
router). It exploits the OpenStack tables for ports and routers.

``connect1`` is defined inductively:

* The first clause (base case) states that a root network is member of
  ``connect1``
* The second clause (inductive case) states that a network linked to a member
  of ``connect1`` is also a member of ``connect1``

``connectName1`` is used to retrieve the names of networks instead of unreadable
uuids.

A query will typically be ``connectName1(X)`` and will give back all the networks
connected.

Now we can define two sets of roots (``root1`` and ``root2``) and two associated
``connect1`` and ``connect2`` predicates. ``root1`` could be for example our
production networks and ``root2`` our test networks.

We would like to check if there exists VMs attached to a
network linked to ``root1`` and a network linked to ``root2``. Here is the
predicate that checks such double attachments:

.. code-block:: console

    connectVM1(X) :- port(id=Z, network_id=Y, device_id=X), connect1(Y).
    connectVM2(X) :- port(id=Z, network_id=Y, device_id=X), connect2(Y).

    doubleAttach(Y):- connectVM1(X), connectVM2(X), server(id=X, name=Y).

``connectVM1`` and ``connectVM2`` define devices that are connected to respectively
``root1`` and ``root2``.
``doubleAttach`` gives back the name of the VMs members of both groups. We use
the ``server`` primitive predicate to find the name of the VM.

Here is a sample output:

.. code-block:: console

    $ octant --config-file sample.conf --theory sample.dtl \
         --query 'connectName1("N12121")' --query 'connectName1("N21212")' \
         --query 'doubleAttach(X)' --time
    Parsing time: 0.0034239999999999826
    Data retrieval: 1.262298
    ********************************************************************************
    connectName1("N12121")
    Query time: 0.012639000000000067
    --------------------------------------------------------------------------------
        True
    ********************************************************************************
    connectName1("N21212")
    Query time: 0.011633999999999922
    --------------------------------------------------------------------------------
        False
    ********************************************************************************
    doubleAttach(X)
    Query time: 0.012620999999999993
    --------------------------------------------------------------------------------
        ['C1', 'C3']
    ********************************************************************************
