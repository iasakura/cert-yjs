(** Facade for the [item] proofs, in dependency order: the pure model ([model],
    [run_theory]), the value layer ([value]: [item_cell], the cell/model
    isomorphism, the deletion layer), the Iris layer ([heap]: [own_dll]), the
    specs of the package's unexported helpers ([wp_private]) and one file per
    exported method ([Indexable], [Len], [Deleted]). *)
From New.proof.item Require Export run_theory model value heap wp_private Indexable Len Deleted.
