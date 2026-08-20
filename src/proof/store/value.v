(** Facade for the [store] VALUE layer: the cell bookkeeping the invariant is
    stated over. Go values but no Iris. Four topic files, in dependency order:
    the cell pool ([value_cells]: [type_state] / [all_cells] / [client_run]
    and the pool invariants), the live-cell refinement and the tombstone set
    ([value_live]: [live_refine] / [delete_set_tombstoned] / [ids_tombstoned]),
    the split surgery and the per-step transport records ([value_split]:
    [split_cells] / [split_types_update_rel] / [repair_types_update_rel] /
    [delete_types_update_rel]), and id ranges with their wire carriers
    ([value_span]: [range_ids] / [span_ids] / [delete_span], plus the by-id
    search). [value_span] is independent of the other three.

    Read each file's own header for what it holds. Downstream files Require
    THIS module (through [store/store.v]) only; the split is an internal
    build-time concern. The Iris layer over all of it is [store/heap.v]. *)
From New.proof.store Require Export value_cells value_live value_split value_span.
