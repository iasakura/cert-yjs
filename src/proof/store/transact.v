(** [store.transact], the transaction as the store's write scope (issue #206
    T1, issue #198 Part II): the write lock is taken once, [f] runs with the
    transaction handle, the lock is released. [wp_store__transact] is
    higher-order in [f] ([closure_runs_transaction], a one-shot wand, so the
    closure may carry the caller's resources in): the caller proves [f]'s
    body against [own_transaction] at whatever state the store is in, and
    chooses what it wants to know afterwards ([Q]). The observers of the changed
    types are notified here before the unlock once they exist (Part II C2);
    until then the transaction only records. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import algebra.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.sync_proof Require Import base mutex rwmutex rwmutex_guard.
From New.proof Require Import tok_set.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.store Require Import model value heap wp_private.
From New.proof.transaction Require Import transaction.

Section store_transact.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

Local Notation Input := (TId * IntegrateInput (A := A))%type.

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem go_string * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.

(** A fresh transaction on the locked store: the record has recorded nothing,
    so every clause of [own_transaction] is vacuous. *)
Lemma own_transaction_fresh (tr s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel) (pend : list Input) (deleted : gset YjsId) :
  own_transaction_changes tr s_loc ∅ ∅ ∅ -∗
  own_store s_loc γs γh c h m pend deleted -∗
  own_observer_registry s_loc γs γh m deleted -∗
  own_transaction tr s_loc γs γh c h m pend deleted ∅ ∅ ∅.
Proof.
  iIntros "Hchanges Hstore Hreg".
  iExists ∅, m, deleted. iFrame "Hchanges Hstore Hreg".
  iSplit; first (iPureIntro; apply transaction_start_fresh).
  iSplit; first iApply changed_types_bound_empty.
  iPureIntro. split_and!.
  - move=> i Hi. set_solver.
  - set_solver.
  - move=> i Hi. set_solver.
Qed.

Lemma wp_store__transact (s_loc : loc) (γs : store_names) (γh : history_names) (f : func.t)
    (Q : ClientId -> list Ev -> DocModel -> list Input -> gset YjsId -> iProp Σ) :
  {{{ is_pkg_init yjs ∗ is_Store s_loc γs γh ∗ closure_runs_transaction s_loc γs γh f Q }}}
    s_loc @! (go.PointerType yjs.store) @! "transact" #f
  {{{ RET #(); ∃ (c : ClientId) (h' : list Ev) (m' : DocModel) (pend' : list Input) (deleted' : gset YjsId),
      Q c h' m' pend' deleted' }}}.
Proof.
  wp_start as "(#His_store & Hf)". rewrite /closure_runs_transaction.
  wp_auto.
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hlk Hinv]".
  iDestruct "Hinv" as (c h m pend deleted) "[Hstore Hreg]".
  wp_auto.
  wp_apply wp_newTransaction. iIntros (tr) "Hchanges".
  wp_auto.
  iDestruct (own_transaction_fresh with "Hchanges Hstore Hreg") as "Htx".
  wp_apply ("Hf" with "[$Htx]").
  iIntros (h' m' pend' deleted' inserted tombstoned changed) "[Htx HQ]".
  wp_auto.
  iDestruct "Htx" as (changed_locs m0 deleted0) "Htx". iNamed "Htx".
  wp_apply (wp_Store__wunlock with "[$His_store $Hlk $Hstore]").
  iApply "HΦ". iExists c, h', m', pend', deleted'. iFrame "HQ".
Qed.

End store_transact.
