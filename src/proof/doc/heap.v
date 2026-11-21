(** The [Doc], Iris layer.

    Definitions
    - [is_Doc dv s_loc γs γh may_insert]: the handle is a [Doc] over the
      store at [s_loc], and [may_insert] is the document's insert rule:
      [may_insert origin unit] says that a transaction opened with the
      origin [origin] may insert the code unit [unit] (issue #131). The
      rule is chosen by whoever creates the document ([wp_NewDoc]) and
      never changes. Persistent.

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

(* [is_store_ref] (from store/store) is generalized over the store lock + item-set RA,
   so mirror its Context here to apply it. *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := (list w16).

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.

(* [is_store_ref]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; mirror the instance here to apply [is_store_ref]. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO store_state))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem A * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.
Context {observers_agree_inG : inG Σ (dfrac_agreeR (leibnizO registered_entries))}.

(* ===== definitions ======================================================== *)

(* [pending_item_rooted] / [is_pending_rooted] are pure [Prop]s (issue #54), so
   [own_store_data]'s [Hpendroot] conjunct is a [⌜..⌝] and needs no instances. *)

(** Doc handle (persistent): reads ONLY [Doc.store] (immutable ⇒ [↦□]) and
    delegates to [is_store_ref]. Since [Text] holds the store directly (y-octo: the
    YTypeRef carries the store ref), [is_Text] does NOT go through [is_Doc]; this
    predicate is the Doc-level handle the [wp_NewDoc] / [wp_Doc__GetOrCreateText] specs
    are stated over (GetOrCreateText: consume [is_Doc dv s_loc γ], look up or create the
    YType under the write lock, return [is_Text t γs γh name []]).
    [may_insert] is the document's insert rule; the store keeps it in
    [sn_may_insert], and the last conjunct says that the parameter is that
    rule. *)
Definition is_Doc (dv ref : loc) (γs : store_names) (γh : history_names)
    (may_insert : go_string -> w16 -> Prop) : iProp Σ :=
  ∃ (dvv : yjs.Doc.t),
    "Hdoc" ∷ dv ↦□ dvv ∗
    "%Hstore" ∷ ⌜dvv.(yjs.Doc.store') = ref⌝ ∗
    "His_store" ∷ is_store_ref ref γs γh ∗
    "%Hmay_insert" ∷ ⌜γs.(sn_may_insert) = may_insert⌝.

#[global] Instance is_Doc_persistent dv ref γs γh may_insert :
  Persistent (is_Doc dv ref γs γh may_insert).
Proof. apply _. Qed.

End doc.
