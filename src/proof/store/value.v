(** Facade for the [store] VALUE layer: what the store invariant is stated
    over. Go values but no Iris. Three topic files, in dependency order: the
    type pool and the per-client item index ([value_cells]: [pool_entries] /
    [kp_client_locs] / [locs_wf] and the registry coherence), the split
    surgery at run granularity ([value_split]: [split_locs] /
    [pool_split_step] and the [repair] contract), and id ranges with their
    wire carriers ([value_span]: [range_ids] / [span_ids] / [delete_span]).
    [value_span] is independent of the other two.

    Read each file's own header for what it holds. Downstream files Require
    THIS module (through [store/store.v]) only; the split is an internal
    build-time concern. The Iris layer over all of it is [store/heap.v]. *)
From New.proof.store Require Export value_cells value_split value_span.
