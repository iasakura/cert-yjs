(** The [Transaction] record, Iris layer (issue #206 T1, issue #198 Part II).

    Definitions
    - [own_transaction_changes tr s_loc inserted tombstoned changed]: the
      transaction record at [tr] belongs to the store at [s_loc] and has
      recorded exactly the char ids [inserted] (its [insertSet]), the char
      ids [tombstoned] (its [deleteSet]) and the type addresses [changed]
      (its [changed] map). The two span slices denote their sets as
      [own_delete_ids] reads a [[]idSpan]: the union of the spans' char
      ids; every recorded span fits [w64], which is what [containsId]'s
      range test needs.

    Laws
    - [own_transaction_changes_store]: the record names its store.

    The record's WPs ([newTransaction], [recordInsert], [recordDelete]) are
    [transaction/wp_private.v]; the transaction handle a caller holds,
    [own_transaction], wraps the record around [own_store] and is the
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

(** The transaction record: its store, and what it recorded so far. The
    [changed] map holds [true] at every recorded type (a Go set). *)
Definition own_transaction_changes (tr s_loc : loc)
    (inserted tombstoned : gset YjsId) (changed : gset loc) : iProp Σ :=
  ∃ (trv : yjs.Transaction.t) (insert_vs delete_vs : list yjs.idSpan.t),
    "Htr" ∷ tr ↦ trv ∗
    "%Htrstore" ∷ ⌜trv.(yjs.Transaction.store') = s_loc⌝ ∗
    "Hinsert" ∷ trv.(yjs.Transaction.insertSet') ↦* insert_vs ∗
    "Hinsertcap" ∷ own_slice_cap yjs.idSpan.t trv.(yjs.Transaction.insertSet') (DfracOwn 1) ∗
    "%Hinsertwf" ∷ ⌜Forall span_no_overflow insert_vs⌝ ∗
    "%Hinserted" ∷ ⌜inserted = ⋃ (span_ids <$> insert_vs)⌝ ∗
    "Hdelete" ∷ trv.(yjs.Transaction.deleteSet') ↦* delete_vs ∗
    "Hdeletecap" ∷ own_slice_cap yjs.idSpan.t trv.(yjs.Transaction.deleteSet') (DfracOwn 1) ∗
    "%Hdeletewf" ∷ ⌜Forall span_no_overflow delete_vs⌝ ∗
    "%Htombstoned" ∷ ⌜tombstoned = ⋃ (span_ids <$> delete_vs)⌝ ∗
    "Hchanged" ∷ trv.(yjs.Transaction.changed') ↦$ (gset_to_gmap true changed : gmap loc bool).

#[global] Instance own_transaction_changes_timeless tr s_loc inserted tombstoned changed :
  Timeless (own_transaction_changes tr s_loc inserted tombstoned changed).
Proof. rewrite /own_transaction_changes. apply _. Qed.

(* ===== lemmas ============================================================= *)

Lemma own_transaction_changes_store (tr s_loc : loc)
    (inserted tombstoned : gset YjsId) (changed : gset loc) :
  own_transaction_changes tr s_loc inserted tombstoned changed -∗
  ∃ (trv : yjs.Transaction.t), tr ↦ trv ∗ ⌜trv.(yjs.Transaction.store') = s_loc⌝ ∗
    (tr ↦ trv -∗ own_transaction_changes tr s_loc inserted tombstoned changed).
Proof.
  iIntros "H". iNamed "H". iExists trv. iFrame "Htr". iSplit; first done.
  iIntros "Htr". iExists trv, insert_vs, delete_vs. iFrame "∗". done.
Qed.

End transaction_heap.
