(** Facade for the [Text] handle proofs: the Iris handle ([heap]: [is_Text])
    and the method proofs ([InsertIn], [DeleteIn], [CodeUnitsIn] inside a
    transaction; [Insert], [Delete] as one-write transactions; the reads
    [Len], [CodeUnits]). The Text handle has no model of its own; the sequence
    it exposes is the [yType] model, so the document-list theory lives in
    [ytype/model]. Downstream files Require only this module. *)
From New.proof.text Require Export model heap InsertIn Insert DeleteIn Delete CodeUnitsIn Len CodeUnits Snapshot Observe.
