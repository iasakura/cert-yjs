(** Proof-level prelude for the ws FFI: pulls in the lifting lemmas together
    with the New proof prelude, and fixes the ws FFI instances so that downstream
    proof files do not have to.

    Staging note: this file belongs in the perennial fork at
    [new/proof/ws_prelude.v], whose logical path is [New.proof.ws_prelude] --
    the same as here. Modeled on perennial's [new/proof/grove_prelude.v]. *)
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.
From New.proof Require Export proof_prelude.
From New Require Export atomic_fupd.
From New Require Export ws_prelude.

#[global]
Existing Instances ws_semantics ws_interp.
#[global]
Existing Instances goose_wsGS.

(* Make sure Z_scope is open. *)
Local Lemma Z_scope_test : (0%Z) + (0%Z) = 0%Z.
Proof. done. Qed.
