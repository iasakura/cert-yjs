(** [wp_Doc__Transact]: the transaction as the document's write scope
    (issue #206 T1, issue #198 Part II): [f] runs once with a fresh
    transaction of the document's store, every write inside it one unit
    under the store's write lock. *)
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

Section doc_Transact.

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
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.


(** [Doc.Transact]: what [store.transact] gives, at the document
    ([closure_runs_transaction] is the closure's obligation: run the fresh
    transaction to an end state where [Q] holds). *)
Lemma wp_Doc__Transact (dv s_loc : loc) (γs : store_names) (γh : history_names) (f : func.t)
    (Q : ClientId -> list Ev -> DocModel -> list (TId * IntegrateInput (A := A)) -> gset YjsId -> iProp Σ) :
  {{{ is_pkg_init yjs ∗ is_Doc dv s_loc γs γh ∗ closure_runs_transaction s_loc γs γh f Q }}}
    dv @! (go.PointerType yjs.Doc) @! "Transact" #f
  {{{ RET #(); ∃ (c : ClientId) (h' : list Ev) (m' : DocModel)
        (pend' : list (TId * IntegrateInput (A := A))) (deleted' : gset YjsId),
      Q c h' m' pend' deleted' }}}.
Proof.
  wp_start as "(#His_doc & Hf)".
  iNamed "His_doc". subst s_loc. wp_auto.
  wp_apply (wp_store__transact with "[$His_store $Hf]").
  iIntros "HQ". wp_auto.
  iApply ("HΦ" with "HQ").
Qed.

End doc_Transact.
