(** The [Transaction] record, Iris layer (issue #206 T1, issue #198 Part II).

    Definitions
    - [node_span v]: the span a node contributes to a record (head id, length).
    - [own_id_spans sl dq ids]: the [[]idSpan] at [sl] denotes the char-id
      set [ids] (the union of its spans' ids), every span fitting [w64]
      (what [containsId]'s range test needs): a record's slice as
      [textDelta] reads it.
    - [own_transaction_changes tr inserted tombstoned changed]: the
      transaction record at [tr] has recorded exactly the char ids
      [inserted] (its [insertSet]), the char ids [tombstoned] (its
      [deleteSet]) and the type addresses [changed] (its [changed] map).
      The two span slices denote their sets as [own_delete_ids] reads a
      [[]idSpan]: the union of the spans' char ids; every recorded span
      fits [w64], which is what [containsId]'s range test needs. The
      record's fourth field, the store the transaction belongs to, is not
      the record's: [own_transaction] ([store/heap.v]) holds it.

    Laws
    - [node_span_char_ids]: a node's span fits and denotes its run's chars.
    - [own_transaction_changes_spans_acc]: borrow the record's two span
      slices as the sets they denote ([store.notify]'s walk reads them).

    The record's WPs ([newTransaction], [recordInsert], [recordDelete]) are
    [transaction/wp_private.v]; the transaction handle a caller holds,
    [own_transaction], wraps the record around [own_store_data] and is the
    store's ([store/heap.v]), as is [wp_store__transact]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From iris.algebra Require Import auth gmap gset.
From New.proof.id Require Import value.
From New.proof.item Require Import run_theory model value.
From New.proof.ytype Require Import model.
From New.proof.store Require Import model value.

Section transaction_heap.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(* [own_slice_cap] is timeless but the New.golang slice library ships no such
   instance ([store/heap] provides its own; this file does not Require it, so
   repeat it here). *)
#[global] Instance own_slice_cap_timeless (V : Type) `{!ZeroVal V} `{!TypedPointsto V} (s : slice.t) (dq : dfrac) :
  Timeless (own_slice_cap V s dq).
Proof. rewrite own_slice_cap_unseal /own_slice_cap_def. apply _. Qed.

(* ===== definitions ======================================================== *)

(** [node_span v]: the span a node contributes to the record, its head id
    and its length as one [idSpan] (what [recordInsert] / [recordDelete]
    append). *)
Definition node_span (v : yjs.item.t) : yjs.idSpan.t :=
  yjs.idSpan.mk v.(yjs.item.id') (W64 (length v.(yjs.item.content').(yjs.content.content'))).

Definition own_id_spans (sl : slice.t) (dq : dfrac) (ids : gset YjsId) : iProp Σ :=
  ∃ (vs : list yjs.idSpan.t),
    "Hspans" ∷ sl ↦*{dq} vs ∗
    "%Hspans_wf" ∷ ⌜Forall span_no_overflow vs⌝ ∗
    "%Hspans_ids" ∷ ⌜ids = ⋃ (span_ids <$> vs)⌝.

(** The transaction record: what the transaction recorded so far, as the
    three record fields of the [Transaction] struct. The [changed] map holds
    [true] at every recorded type (a Go set). The struct's fourth field, the
    store the transaction belongs to, is not the record's: [own_transaction]
    ([store/heap]) holds it, so that a store method recording into [tr]
    takes only the record. *)
Definition own_transaction_changes (tr : loc)
    (inserted tombstoned : gset YjsId) (changed : gset loc) : iProp Σ :=
  ∃ (insert_sl delete_sl : slice.t) (changed_mref : loc)
    (insert_vs delete_vs : list yjs.idSpan.t),
    "Hinsertf" ∷ (tr .[(yjs.Transaction.t), "insertSet"]) ↦ insert_sl ∗
    "Hinsert" ∷ insert_sl ↦* insert_vs ∗
    "Hinsertcap" ∷ own_slice_cap yjs.idSpan.t insert_sl (DfracOwn 1) ∗
    "%Hinsertwf" ∷ ⌜Forall span_no_overflow insert_vs⌝ ∗
    "%Hinserted" ∷ ⌜inserted = ⋃ (span_ids <$> insert_vs)⌝ ∗
    "Hdeletef" ∷ (tr .[(yjs.Transaction.t), "deleteSet"]) ↦ delete_sl ∗
    "Hdelete" ∷ delete_sl ↦* delete_vs ∗
    "Hdeletecap" ∷ own_slice_cap yjs.idSpan.t delete_sl (DfracOwn 1) ∗
    "%Hdeletewf" ∷ ⌜Forall span_no_overflow delete_vs⌝ ∗
    "%Htombstoned" ∷ ⌜tombstoned = ⋃ (span_ids <$> delete_vs)⌝ ∗
    "Hchangedf" ∷ (tr .[(yjs.Transaction.t), "changed"]) ↦ changed_mref ∗
    "Hchanged" ∷ changed_mref ↦$ (gset_to_gmap true changed : gmap loc bool).

#[global] Instance own_transaction_changes_timeless tr inserted tombstoned changed :
  Timeless (own_transaction_changes tr inserted tombstoned changed).
Proof. rewrite /own_transaction_changes. apply _. Qed.

(* ===== lemmas ============================================================= *)

(** What a node's span records is its run: a node whose id, content length
    and run agree ([own_item_node]'s pins) contributes a span that fits a
    word and denotes exactly the run's char ids. *)
Lemma node_span_char_ids (v : yjs.item.t) (r : ItemRun) :
  run_wf (run_items r) ->
  toYjsId v.(yjs.item.id') = item_id (run_head_item r) ->
  length v.(yjs.item.content').(yjs.content.content') = length (run_items r) ->
  run_fits r ->
  span_no_overflow (node_span v) ∧ span_ids (node_span v) = char_ids (run_items r).
Proof.
  move=> Hwf Hid Hlen Hfits.
  have Hclk : uint.nat v.(yjs.item.id').(yjs.id.clock') = run_clock r.
  { rewrite /run_clock -Hid //. }
  have Hlen64 : (Z.of_nat (length (run_items r)) < 2^64)%Z.
  { move: Hfits. rewrite /run_fits. lia. }
  split.
  { rewrite /span_no_overflow /node_span /range_no_overflow /= Hlen.
    move: Hfits. rewrite /run_fits -Hclk. word. }
  have Hstep : run_step (run_items r) := run_wf_run_step _ Hwf.
  have Hhead : item_id (run_head_item r) = toYjsId v.(yjs.item.id') by rewrite Hid.
  have Hlenw : length (run_items r) = uint.nat (W64 (length v.(yjs.item.content').(yjs.content.content'))).
  { rewrite Hlen. word. }
  have Hcons : run_items r = run_head_item r :: List.tl (run_items r).
  { rewrite /run_head_item. destruct (run_items r); [by destruct Hwf | reflexivity]. }
  rewrite Hcons in Hstep Hlenw *.
  rewrite /node_span. exact (span_ids_char_ids _ _ _ _ Hhead Hstep Hlenw).
Qed.

Lemma own_transaction_changes_spans_acc (tr : loc)
    (inserted tombstoned : gset YjsId) (changed : gset loc) :
  own_transaction_changes tr inserted tombstoned changed -∗
  ∃ (insert_sl delete_sl : slice.t),
    (tr .[(yjs.Transaction.t), "insertSet"]) ↦ insert_sl ∗
    (tr .[(yjs.Transaction.t), "deleteSet"]) ↦ delete_sl ∗
    own_id_spans insert_sl (DfracOwn 1) inserted ∗
    own_id_spans delete_sl (DfracOwn 1) tombstoned ∗
    ((tr .[(yjs.Transaction.t), "insertSet"]) ↦ insert_sl -∗
     (tr .[(yjs.Transaction.t), "deleteSet"]) ↦ delete_sl -∗
     own_id_spans insert_sl (DfracOwn 1) inserted -∗
     own_id_spans delete_sl (DfracOwn 1) tombstoned -∗
     own_transaction_changes tr inserted tombstoned changed).
Proof.
  iIntros "H". iNamed "H". iExists insert_sl, delete_sl. iFrame "Hinsertf Hdeletef".
  iSplitL "Hinsert". { iExists insert_vs. iFrame "Hinsert". done. }
  iSplitL "Hdelete". { iExists delete_vs. iFrame "Hdelete". done. }
  iIntros "Hinsertf Hdeletef Hins Hdel".
  iDestruct "Hins" as (insert_vs') "(Hinsert' & %Hinsertwf' & %Hinserted')".
  iDestruct "Hdel" as (delete_vs') "(Hdelete' & %Hdeletewf' & %Htombstoned')".
  iExists insert_sl, delete_sl, changed_mref, insert_vs', delete_vs'. iFrame "∗". done.
Qed.

End transaction_heap.
