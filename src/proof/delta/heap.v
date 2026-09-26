(** The text delta, Iris layer.

    Definitions
    - [own_delta sl dq delta]: the [[]DeltaOp] slice at [sl] denotes the
      delta [delta].

    Laws
    - [own_delta_nil]: the nil slice is the empty delta.

    The method proofs are [delta/ApplyDelta.v]; [deltaSnoc], the step every
    walk takes, is [delta/wp_private.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.delta Require Import model value.

Section delta_heap.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== definitions ======================================================== *)

Definition own_delta (sl : slice.t) (dq : dfrac) (delta : list DeltaOp) : iProp Σ :=
  ∃ (vs : list yjs.DeltaOp.t),
    "Hsl" ∷ sl ↦*{dq} vs ∗
    "Hcap" ∷ own_slice_cap yjs.DeltaOp.t sl dq ∗
    "%Hdenote" ∷ ⌜Forall2 delta_op_denotes vs delta⌝.

(* ===== lemmas ============================================================= *)

Lemma own_delta_nil : ⊢ own_delta slice.nil (DfracOwn 1) [].
Proof.
  iExists []. iSplitR; [iApply own_slice_nil | iSplitR; [iApply own_slice_cap_nil | done]].
Qed.

End delta_heap.
