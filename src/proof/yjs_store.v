(** Facade for the [store] proofs. One Go file ([yjs/store.go]), three proof
    files split for build-time isolation:

    - [yjs_store_base]: ghost names and RAs, [own_item_map], the store
      predicates ([store_inv] / [own_store] / [is_Store] / [is_root] / ...),
      the RWMutex lock layer, [store_inv_init];
    - [yjs_store_integrate]: id lookup, the conflict scan, [Store.Integrate];
    - [yjs_store_update]: [GetNode] / [getOrCreateYType] / [repair], the
      [store_inv ⊣⊢ own_store] bridge, and the applyUpdate stack up to
      [wp_store__applyUpdate_certs].

    Downstream files Require THIS module only; the split is an internal
    build-time concern. *)
From New.proof Require Export yjs_store_base yjs_store_integrate yjs_store_update.
