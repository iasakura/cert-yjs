(** Facade for the [Doc] proofs: the pure doc-level model ([model], the
    multi-root document the store's state lives in), the Iris layer ([heap]:
    [is_Doc]) and the method proofs ([NewDoc], [GetOrCreateText], [Transact],
    [ApplySyncUpdate], its byte-level entry point [ApplyEncodedUpdate], and
    [TransactEncoded], the transaction whose update is handed back as bytes).
    Downstream files Require only this module. *)
From New.proof.doc Require Export model heap NewDoc GetOrCreateText Transact ApplySyncUpdate ApplyEncodedUpdate TransactEncoded.
