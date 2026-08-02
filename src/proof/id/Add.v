(** [id.Add]: shifting an id's clock by [n], at the machine-word level. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.id Require Import value heap.

Section id_Add.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".



(* Add advances the clock; the client is untouched. *)
Lemma wp_Id__Add (id : yjs.id.t) (n : w64) :
  {{{ is_pkg_init yjs }}}
    id @! yjs.id @! "Add" #n
  {{{ RET #(yjs.id.mk id.(yjs.id.clientId') (word.add id.(yjs.id.clock') n)); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

End id_Add.
