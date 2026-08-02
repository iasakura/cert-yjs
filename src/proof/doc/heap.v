(** The [Doc], Iris layer.

    Definitions
    - [is_Doc dv s_loc γs γh]: the handle is a [Doc] over the store at
      [s_loc]. Persistent.

    The pure doc-level model is [doc/model.v]; the sync entry point is
    [doc/ApplySyncUpdate.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.
From New.proof.ytype Require Import model value heap.
From New.proof.store Require Import model value heap.
From New.proof.text Require Import heap.

Section doc.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

(* [is_Store] (from store/store) is generalized over the store lock + item-set RA,
   so mirror its Context here to apply it. *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.

(* [is_Store]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; mirror the instance here to apply [is_Store]. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

(* ===== definitions ======================================================== *)

(* [pending_item_rooted] / [is_pending_rooted] are pure [Prop]s (issue #54), so
   [own_store]'s [Hpendroot] conjunct is a [⌜..⌝] and needs no instances. *)

(** Doc handle (persistent): reads ONLY [Doc.store] (immutable ⇒ [↦□]) and
    delegates to [is_Store]. Since [Text] holds the store directly (y-octo: the
    YTypeRef carries the store ref), [is_Text] does NOT go through [is_Doc]; this
    predicate is the Doc-level handle used by the eventual [wp_NewDoc] /
    [wp_Doc__GetText] specs (GetText: consume [is_Doc dv s_loc γ], create a YType
    under the lock, return [is_Text t []]). *)
Definition is_Doc (dv s_loc : loc) (γs : store_names) (γh : history_names) : iProp Σ :=
  ∃ (dvv : yjs.Doc.t),
    "Hdoc" ∷ dv ↦□ dvv ∗
    "%Hstore" ∷ ⌜dvv.(yjs.Doc.store') = s_loc⌝ ∗
    "His_store" ∷ is_Store s_loc γs γh.

#[global] Instance is_Doc_persistent dv s_loc γs γh : Persistent (is_Doc dv s_loc γs γh).
Proof. apply _. Qed.

End doc.
