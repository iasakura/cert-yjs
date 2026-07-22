(** Facade for the [store] proofs. One Go file ([yjs/store.go]), FOUR proof
    files split for build-time isolation:

    - [yjs_store_base]: ghost names and RAs, [own_item_map], the store
      predicates ([store_inv] / [own_store] / [is_Store] / [is_root] / ...),
      the RWMutex lock layer, [store_inv_init];
    - [yjs_store_integrate]: id lookup, the conflict scan, [Store.Integrate];
    - [yjs_store_node]: the run-cell infrastructure ([all_cells] and its
      lemmas), the covering gate ([GetNode_range]), [splitNode] / the split
      layer, [integrateDecoded], the wire-drain theory, and the
      [store_inv ⊣⊢ own_store] bridge;
    - [yjs_store_update]: the applyUpdate drain loop and the [own_store]-level
      certificate spec [wp_store__applyUpdate_certs].

    Downstream files Require THIS module only; the split is an internal
    build-time concern. *)
From New.proof Require Export yjs_store_base yjs_store_integrate yjs_store_node yjs_store_update.
