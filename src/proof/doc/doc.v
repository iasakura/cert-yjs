(** Facade for the [Doc] proofs: the pure doc-level model ([model], the
    multi-root document the store's state lives in), the Iris layer ([heap]:
    [is_Doc]) and the method proofs ([NewDoc], [GetText], [ApplySyncUpdate],
    and its byte-level entry point [ApplyEncodedUpdate]). Downstream files
    Require only this module. *)
From New.proof.doc Require Export model heap NewDoc GetText ApplySyncUpdate ApplyEncodedUpdate.
