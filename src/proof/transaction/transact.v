(** [transact], the transaction as the store's write scope (issue #206
    T1, issue #198 Part II): the write lock is taken once, [f] runs with the
    transaction handle, the lock is released. [wp_transact] is
    higher-order in [f] ([closure_runs_transaction], a one-shot wand, so the
    closure may carry the caller's resources in): the caller proves [f]'s
    body against [own_transaction] at whatever state the store is in, and
    chooses what it wants to know afterwards ([Q]). The observers of the
    changed types are notified before the unlock ([wp_Transaction__notify],
    Part II C2), which is where the store's observers catch up with its data.

    The transitions of the store's predicate across one transaction, in
    order: the write lock hands out the issue #219 split, the core, the
    session and the observers told up to the store's current model and
    tombstones ([wp_Store__wlock]); this proof rebuilds [own_store] from
    the split ([own_store_data_build]) and [own_transaction_fresh] (below)
    wraps it with the fresh record into [own_transaction], the predicate
    the closure runs on; [wp_Transaction__notify] turns [own_transaction]
    back out as the split at coincident states, which the write lock
    takes back ([wp_Store__wunlock]); since issue #219's consumer move,
    [own_transaction] itself is the split plus the record, so no
    conversion happens at this boundary. *)
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
From New.proof.store Require Import store.
From New.proof.transaction Require Import model heap wp_private notify.

Section transaction_transact.

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

(** [own_store] (states coincident) to [own_transaction]: a fresh
    transaction on the locked store. The record has recorded nothing, so
    every clause of the record's meaning is vacuous and the start state is
    the current one ([transaction_start_fresh]). *)
Lemma own_transaction_fresh (tr s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel) (state : store_state) (ds : gset YjsId) :
  own_transaction_changes tr s_loc ∅ ∅ ∅ -∗
  own_store_core s_loc γs state ds ∗
  own_store_session γs γh c h m state ds ∗
  own_observers s_loc γs γh m (pool_tombstoned (ss_pool state)) -∗
  own_transaction tr s_loc γs γh c h m (ss_pending state) (pool_tombstoned (ss_pool state)) ∅ ∅ ∅.
Proof.
  iIntros "Hchanges (Hcore & Hsession & Hobservers)".
  iExists state, ds, m, (pool_tombstoned (ss_pool state)).
  iSplitR; first done.
  iSplitR; first done.
  iSplitL "Hcore Hobservers"; first iFrame "Hcore Hobservers".
  iFrame "Hsession".
  iSplit; last (iPureIntro; apply transaction_start_fresh).
  iExists ∅. iFrame "Hchanges".
  iSplit; first iApply changed_types_bound_empty.
  iPureIntro. split_and!.
  - move=> i Hi. set_solver.
  - set_solver.
  - move=> i Hi. set_solver.
Qed.

Lemma wp_transact (ref : loc) (γs : store_names) (γh : history_names) (f : func.t)
    (Q : ClientId -> list Ev -> DocModel -> list Input -> gset YjsId -> iProp Σ) :
  {{{ is_pkg_init yjs ∗ is_Store ref γs γh ∗ closure_runs_transaction (store_of_ref ref) γs γh f Q }}}
    @! yjs.transact #ref #f
  {{{ RET #(); ∃ (c : ClientId) (h' : list Ev) (m' : DocModel) (pend' : list Input) (deleted' : gset YjsId),
      Q c h' m' pend' deleted' }}}.
Proof.
  wp_start as "(#His_store & Hf)". rewrite /closure_runs_transaction.
  wp_auto.
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hlk Hinv]".
  iDestruct "Hinv" as (c h m) "Hstore".
  wp_auto.
  iDestruct "Hstore" as (state0 ds0) "(Hcore & Hsession & Hobservers0)".
  wp_apply wp_newTransaction. iIntros (tr) "Hchanges".
  wp_auto.
  iDestruct (own_transaction_fresh with "Hchanges [$Hcore $Hsession $Hobservers0]") as "Htx".
  wp_apply ("Hf" with "[$Htx]").
  iIntros (h' m' pend' deleted' inserted tombstoned changed) "[Htx HQ]".
  wp_auto.
  wp_apply (wp_Transaction__notify with "[$Htx]"). iIntros "Hstore".
  wp_auto.
  iDestruct "Hstore" as (state' ds') "(%Hpend' & %Hdel' & Hstore & Hsession')".
  iEval (rewrite Hdel') in "Hstore".
  iDestruct "Hstore" as "[Hcore' Hobs']".
  wp_apply (wp_Store__wunlock with "[$His_store $Hlk $Hcore' $Hsession' $Hobs']").
  iApply "HΦ". iExists c, h', m', pend', deleted'. iFrame "HQ".
Qed.

End transaction_transact.
