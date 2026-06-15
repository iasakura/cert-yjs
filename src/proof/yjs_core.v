(** Boundary to the reusable Yjs order theory.

    cert-yjs proves that the goose-translated [Integrate] refines the *pure*
    integration algorithm and inherits order preservation from it. That pure
    theory lives in iasakura/iris-yjs, packaged as the opam libraries
    rocq-yjs-core (namespace [yjs.crdt]) and rocq-yjs (namespace [yjs]).

    This module re-exports the pieces cert-yjs consumes so the rest of the
    development imports a single name:

      ClientId                            yjs.crdt.client_id
      YjsId, YjsPtr, YjsItem, accessors   yjs.item
      ItemSet, IsClosedItemSet            yjs.item_set
      YjsLt'/YjsLeq', ItemSetInvariant    yjs.order.{item_order,item_set_invariant}
      IntegrateInput, toItem, integrate*  yjs.algorithm.{basic,insert_basic}
      ArrSet, YjsArrInvariant             yjs.algorithm.invariant_yjsarray
      IsItemValid                         yjs.algorithm.invariant_basic
      YjsArrInvariant_integrateSafe       yjs.algorithm.insert_loop
      setfii_loop, setintegrate, Couple,  yjs.algorithm.insert_set
        setintegrate_eq_integrate, ...
*)
From yjs.crdt Require Export client_id.
From yjs Require Export item item_set util.
From yjs.order Require Export item_order item_set_invariant.
From yjs.algorithm Require Export basic insert_basic invariant_basic invariant_yjsarray insert_loop insert_set.
