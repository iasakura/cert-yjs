(** Facade for the [id] proofs: the value layer ([value]: [toYjsId] and its
    round-trip / injectivity), the Iris layer ([heap]: [is_origin_id]), the
    specs of the package's unexported helpers ([wp_private]) and one file per
    exported method ([Add], [Sub], [Equal]). The [id] type has no pure model of
    its own: the model side is rocq-yjs's [YjsId]. *)
From New.proof.id Require Export value heap wp_private Add Sub Equal.
