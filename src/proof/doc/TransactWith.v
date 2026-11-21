(** [wp_Doc__TransactWith] (issue #131): [Doc.Transact] with an origin for
    the transaction. The origin goes to the update observers
    ([Doc.ObserveUpdate]) and selects what the document's insert rule
    ([is_Doc]'s parameter [may_insert]) allows the transaction to insert. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.transaction Require Import transaction.
From New.proof.store Require Import store.
From New.proof.text Require Import text.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.doc Require Import model heap.

Section doc_TransactWith.

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


(** [Doc.TransactWith]: as [wp_Doc__Transact], for the origin the caller
    gives. *)
Lemma wp_Doc__TransactWith (dv ref : loc) (γs : store_names) (γh : history_names)
    (may_insert : go_string -> w16 -> Prop) (origin : go_string) (f : func.t)
    (Q : ClientId -> list Ev -> DocModel -> list (TId * IntegrateInput (A := A)) -> gset YjsId -> iProp Σ) :
  {{{ is_pkg_init yjs ∗ is_Doc dv ref γs γh may_insert ∗
      closure_runs_transaction (store_of_ref ref) γs γh (may_insert origin) f Q }}}
    dv @! (go.PointerType yjs.Doc) @! "TransactWith" #origin #f
  {{{ RET #(); ∃ (c : ClientId) (h' : list Ev) (m' : DocModel)
        (pend' : list (TId * IntegrateInput (A := A))) (deleted' : gset YjsId),
      Q c h' m' pend' deleted' }}}.
Proof.
  wp_start as "(#His_doc & Hf)".
  iNamed "His_doc". subst ref may_insert. wp_auto.
  wp_apply (wp_transact with "[$His_store $Hf]").
  iIntros "HQ". wp_auto.
  iApply ("HΦ" with "HQ").
Qed.

End doc_TransactWith.
