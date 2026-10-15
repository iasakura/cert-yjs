(** The text delta, Iris layer.

    Definitions
    - [is_delta_op v op]: the [DeltaOp] struct value [v] denotes the entry
      [op]: its kind and count ([delta_op_kind]) and, for an insert, the
      read-only ownership of its content slice, which holds the inserted
      code units. Persistent: an insert's slice is never written once the
      entry exists (it may be a node's own content, yjs/observe.go), so every
      reader of a delta shares it.
    - [own_delta sl dq delta]: the [[]DeltaOp] slice at [sl] denotes the
      delta [delta].

    Laws
    - [is_delta_op_retain] / [is_delta_op_delete] / [is_delta_op_insert]:
      building an entry's denotation from the struct's fields.
    - [is_delta_ops_take]: the denotations survive truncating a delta.
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

Notation A := (list w16).

(* ===== definitions ======================================================== *)

Definition is_delta_op (v : yjs.DeltaOp.t) (op : DeltaOp) : iProp Σ :=
  ⌜delta_op_kind v op⌝ ∗
  match op with
  | Insert t => v.(yjs.DeltaOp.Content') ↦*□ t
  | Retain _ | Delete _ => True
  end.

#[global] Instance is_delta_op_persistent v op : Persistent (is_delta_op v op).
Proof. rewrite /is_delta_op. destruct op; apply _. Qed.

Definition own_delta (sl : slice.t) (dq : dfrac) (delta : list DeltaOp) : iProp Σ :=
  ∃ (vs : list yjs.DeltaOp.t),
    "Hsl" ∷ sl ↦*{dq} vs ∗
    "Hcap" ∷ own_slice_cap yjs.DeltaOp.t sl dq ∗
    "#Hdenote" ∷ ([∗ list] v;op ∈ vs;delta, is_delta_op v op).

(* ===== lemmas ============================================================= *)

(** Building an entry's denotation: a retain or a delete from its kind byte
    and count, an insert from its kind byte and the read-only share of its
    content. *)
Lemma is_delta_op_retain (v : yjs.DeltaOp.t) (n : nat) :
  v.(yjs.DeltaOp.Kind') = W8 0 -> v.(yjs.DeltaOp.Length') = W64 (Z.of_nat n) ->
  ⊢ is_delta_op v (Retain n).
Proof. move=> Hk Hn. rewrite /is_delta_op /=. iSplit; [by iPureIntro | done]. Qed.

Lemma is_delta_op_delete (v : yjs.DeltaOp.t) (n : nat) :
  v.(yjs.DeltaOp.Kind') = W8 2 -> v.(yjs.DeltaOp.Length') = W64 (Z.of_nat n) ->
  ⊢ is_delta_op v (Delete n).
Proof. move=> Hk Hn. rewrite /is_delta_op /=. iSplit; [by iPureIntro | done]. Qed.

Lemma is_delta_op_insert (v : yjs.DeltaOp.t) (t : A) :
  v.(yjs.DeltaOp.Kind') = W8 1 ->
  v.(yjs.DeltaOp.Content') ↦*□ t -∗ is_delta_op v (Insert t).
Proof. move=> Hk. iIntros "#Hc". rewrite /is_delta_op /=. iSplit; [by iPureIntro | iExact "Hc"]. Qed.

(** Truncating a delta keeps its entries' denotations: what dropping the
    trailing retain ([delta[:n-1]]) hands the shorter slice. *)
Lemma is_delta_ops_take (vs : list yjs.DeltaOp.t) (delta : list DeltaOp) (k : nat) :
  ([∗ list] v;op ∈ vs;delta, is_delta_op v op) -∗
  [∗ list] v;op ∈ take k vs;take k delta, is_delta_op v op.
Proof.
  iIntros "H". iDestruct (big_sepL2_length with "H") as %Hlen.
  have Hlens : length (take k vs) = length (take k delta) by rewrite !length_take Hlen.
  iDestruct (big_sepL2_app_inv (λ _ v op, is_delta_op v op) (take k vs) (drop k vs)
               (take k delta) (drop k delta) (or_introl Hlens) with "[H]") as "[Hk _]";
    last iExact "Hk".
  rewrite !take_drop. iExact "H".
Qed.

Lemma own_delta_nil : ⊢ own_delta slice.nil (DfracOwn 1) [].
Proof.
  iExists []. iSplitR; [iApply own_slice_nil | iSplitR; [iApply own_slice_cap_nil |]].
  by iApply big_sepL2_nil.
Qed.

End delta_heap.
