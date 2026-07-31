(** Facade for the [store] proofs. One Go file ([yjs/store.go]), layered: the
    pure model ([model]: the wire drain and the coherence predicates), the value
    layer ([value]: the cell bookkeeping), the Iris layer ([heap]: ghost names,
    [store_inv] / [own_store] / [is_Store]), the internal WP specs
    ([wp_private]: the RWMutex lock wrappers) and one file per method proof
    ([Integrate], [GetNode], [splitNode], [repair], [applyUpdate]). Downstream
    files Require THIS module only; the split is an internal build-time
    concern. *)
From New.proof.store Require Export model value heap wp_private Integrate GetNode splitNode repair applyUpdate.
