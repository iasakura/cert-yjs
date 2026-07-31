(** [id.Equal]: field-wise id equality, which is exactly model id equality
    ([Id_eqb_toYjsId] in [id/value.v]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.id Require Import value heap.

Section id_Equal.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".



(* ----- WP specs for the id / set helper functions ------------------------ *)

Lemma wp_Id__Equal (a b : yjs.id.t) :
  {{{ is_pkg_init yjs }}}
    a @! yjs.id @! "Equal" #b
  {{{ RET #(bool_decide (toYjsId a = toYjsId b)); True }}}.
Proof.
  wp_start as "_". wp_auto. wp_if_destruct.
  - have -> : bool_decide (a.(yjs.id.clock') = b.(yjs.id.clock'))
             = bool_decide (toYjsId a = toYjsId b).
    { rewrite -Id_eqb_toYjsId. by rewrite (bool_decide_eq_true_2 _ e). }
    iApply "HΦ". done.
  - have Hf : bool_decide (toYjsId a = toYjsId b) = false.
    { apply bool_decide_eq_false_2 => H. apply n. by rewrite (toYjsId_inj _ _ H). }
    iEval (rewrite Hf) in "HΦ". iApply "HΦ". done.
Qed.

End id_Equal.
