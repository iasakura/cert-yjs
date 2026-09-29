(** [wp_Doc__Transact]: the transaction as the document's write scope
    (issue #206 T1, issue #198 Part II): the write lock is taken once, [f]
    runs with a fresh transaction of the document's store, the observers of
    the changed types are notified ([wp_store__notify]), the lock is
    released. Higher-order in [f] ([closure_runs_transaction], a one-shot
    wand, so the closure may carry the caller's resources in): the caller
    proves [f]'s body against [own_transaction] at whatever state the store
    is in, and chooses what it wants to know afterwards ([Q]). In [store/]
    rather than [doc/] because [Text.Insert] and [Text.Delete] ([text/],
    below [doc/]) are one-write transactions around it. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.sync_proof Require Import base mutex rwmutex rwmutex_guard.
From New.proof Require Import tok_set.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.store Require Import model value heap wp_private notify.
From New.proof.transaction Require Import transaction.

Section store_Transact.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

(* [is_Doc] (from store/store) is generalized over the store lock + item-set RA,
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

(* [is_Doc]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; mirror the instance here to apply [is_Doc]. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem go_string * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.


(** [Doc.Transact]: the transaction at the document
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
  wp_start as "(#His_doc & Hf)". rewrite /closure_runs_transaction.
  iPoseProof "His_doc" as "Hdoc_fields". iNamed "Hdoc_fields".
  wp_auto.
  wp_apply (wp_Doc__wlock with "[$His_doc]"). iIntros "[Hlk Hinv]".
  iDestruct "Hinv" as (c h m pend deleted) "Hstore".
  wp_auto.
  wp_apply wp_newTransaction. iIntros (tr) "Hchanges".
  wp_auto.
  iDestruct (own_transaction_fresh with "Hchanges Hstore") as "Htx".
  wp_apply ("Hf" with "[$Htx]").
  iIntros (h' m' pend' deleted' inserted tombstoned changed) "[Htx HQ]".
  wp_auto.
  wp_apply (wp_store__notify with "[$Htx]"). iIntros "Hstore".
  wp_auto.
  wp_apply (wp_Doc__wunlock with "[$His_doc $Hlk $Hstore]").
  iApply "HΦ". iExists c, h', m', pend', deleted'. iFrame "HQ".
Qed.

End store_Transact.
