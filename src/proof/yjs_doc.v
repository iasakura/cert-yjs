(** Doc-layer invariant / WP proofs — mirrors yjs/doc.go. Currently just the
    [Doc] representation predicate [is_Doc]; it is the home for the eventual
    [wp_NewDoc] / [wp_Doc__GetText] proofs (GetText consumes [is_Doc] and returns
    [is_Text t []], which is why this module sits after [yjs_text] in the
    dependency order: core → common → id → item → ytype → store → text → doc). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id yjs_item yjs_ytype yjs_history yjs_store yjs_text.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.

Section doc.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
(* [is_Store] (from yjs_store) is generalized over the store lock + item-set RA,
   so mirror its Context here to apply it. *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

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
