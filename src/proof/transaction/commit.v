(** [Transaction.commit] (issue #131): the end of a transaction. The
    observers of the types the transaction changed are told ([notify]),
    then the update observers ([notifyUpdate]); the store comes back with
    its observers at its data's state, which is what the write lock takes
    back. The premise is what the transaction's closure showed of what it
    inserted ([closure_runs_transaction]). *)
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
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.store Require Import store appendSpanStructs.
From New.proof.transaction Require Import model heap wp_private notify insertedStructs notifyUpdate.
From New.proof.delta Require Import delta.

(* iris.algebra pushes [nat_scope], retuning the default [<] / [≤]; the
   word-arithmetic proofs write [Z] comparisons unannotated, so restore
   [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section transaction_commit.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := (list w16).

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

Local Notation Input := (TId * IntegrateInput (A := A))%type.

Local Notation snapshot := (list (YjsItem A * bool)).

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO store_state))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem A * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.
Context {observers_agree_inG : inG Σ (dfrac_agreeR (leibnizO registered_entries))}.

(* ===== lemmas ============================================================= *)

Lemma wp_Transaction__commit (tr s_loc : loc) (γs : store_names) (γh : history_names)
    (origin : go_string) (c : ClientId) (h : list Ev) (m : DocModel) (pend : list Input)
    (deleted inserted tombstoned : gset YjsId) (changed : gset P) :
  {{{ is_pkg_init yjs ∗
      own_transaction tr s_loc γs γh origin c h m pend deleted inserted tombstoned changed ∗
      ⌜inserted_units_allowed (γs.(sn_may_insert) origin) m inserted⌝ }}}
    tr @! (go.PointerType yjs.Transaction) @! "commit" #()
  {{{ RET #(); ∃ (state : store_state) (delete_set : gset YjsId),
      ⌜state_pending_tombstoned state pend deleted⌝ ∗
      own_store s_loc γs γh 1 state delete_set m deleted ∗
      own_replica_history γs γh c h m state delete_set }}}.
Proof.
  wp_start as "(Htx & %Hallowed)".
  wp_auto.
  wp_apply (wp_Transaction__notify with "[$Htx]"). iIntros "Htx".
  wp_auto.
  wp_apply (wp_Transaction__notifyUpdate with "[$Htx]").
  { iPureIntro. exact Hallowed. }
  iIntros "Htx".
  wp_auto.
  iApply "HΦ".
  iDestruct "Htx" as (state delete_set insert_slice delete_slice) "Htx". iNamed "Htx".
  iExists state, delete_set. iFrame "Hstore Hreplica_history". done.
Qed.

End transaction_commit.
