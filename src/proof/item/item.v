(** Facade for the [item] proofs, in dependency order: the pure model ([model],
    [run_theory]), the value layer ([value]: the heap node's scalar readings),
    the Iris layer ([heap]: [own_item_node] / [own_dll_runs]), the specs of the
    package's unexported helpers ([wp_private]) and one file per exported
    method ([Indexable], [Len], [Deleted]). *)
From New.proof.item Require Export run_theory model value heap wp_private Indexable Len Deleted.
