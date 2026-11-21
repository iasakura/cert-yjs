(** [Transaction.notifyUpdate] (issue #131): the update half of the end of a
    transaction. After the observers of the types were told ([notify]),
    every callback registered with [Doc.ObserveUpdate] is called with the
    transaction's update, encoded by its own encoder, and the transaction's
    origin. The store establishes the callback's precondition
    ([is_update_callback]) from what it holds: the batch read back from the
    store is certified in the global history and its items fit machine
    words, and the closure of the transaction showed that what it inserted
    is allowed by the document's insert rule for the origin. *)
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
From New.proof.transaction Require Import model heap wp_private insertedStructs.
From New.proof.delta Require Import delta.

(* iris.algebra pushes [nat_scope], retuning the default [<] / [≤]; the
   word-arithmetic proofs write [Z] comparisons unannotated, so restore
   [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section transaction_notifyUpdate.

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

(** The items of the notified transaction's model have clocks whose
    successor fits a machine word (the pool's [pool_item_clock_fits] through
    the registry): each can go on the wire as a one-unit struct. *)
#[local] Lemma own_transaction_notified_item_clock_fits (tr s_loc : loc) (γs : store_names)
    (γh : history_names) (c : ClientId) (h : list Ev) (m : DocModel) (pend : list Input)
    (deleted inserted : gset YjsId) :
  own_transaction_notified tr s_loc γs γh c h m pend deleted inserted -∗
  ⌜∀ (name : P) (item : YjsItem A), item ∈ doc_model_get m (RootId name) ->
     (Z.of_nat (clock (item_id item)) + 1 < 2^64)%Z⌝.
Proof.
  iIntros "Htx". iDestruct "Htx" as (state ds insert_sl) "Htx". iNamed "Htx".
  iDestruct (own_replica_history_registry_models with "Hreplica_history") as %[Hmodels Hbound].
  iNamed "Hstore". iNamed "Hcore".
  iDestruct (own_store_state_run_pool_invs with "Hstate") as %Hpool_invs.
  iDestruct (own_store_state_registry_coh with "Hstate") as %(Hregistered & _ & _).
  iPureIntro. move=> name item Hitem.
  have Hnonempty : doc_model_get m (RootId name) ≠ [].
  { move=> Hnil. rewrite Hnil in Hitem. by apply elem_of_nil in Hitem. }
  destruct (Hbound _ Hnonempty) as (name' & parent & [= <-] & Hbind).
  destruct (Hregistered name parent Hbind) as [tm Htm].
  apply (pool_item_clock_fits _ parent tm item Hpool_invs Htm).
  by rewrite -(Hmodels name parent tm Hbind Htm).
Qed.

(** Every item of the notified transaction's model is certified in the
    global history, with exactly its input ([history_model_certified], for
    the history the transaction holds). *)
#[local] Lemma own_transaction_notified_model_certified (tr s_loc : loc) (γs : store_names)
    (γh : history_names) (c : ClientId) (h : list Ev) (m : DocModel) (pend : list Input)
    (deleted inserted : gset YjsId) (E : coPset) :
  ↑histN ⊆ E ->
  is_history (A := A) (P := P) γh -∗
  own_transaction_notified tr s_loc γs γh c h m pend deleted inserted ={E}=∗
    own_transaction_notified tr s_loc γs γh c h m pend deleted inserted ∗
    □ (∀ (t : TId) (item : YjsItem A), ⌜item ∈ doc_model_get m t⌝ -∗
         is_op_cert γh (t, OpInsert (input_of_item item))).
Proof.
  iIntros (HE) "#Hishist Htx".
  iDestruct "Htx" as (state ds insert_sl) "Htx". iNamed "Htx".
  iDestruct "Hreplica_history" as (acc) "Hreplica_history". iNamed "Hreplica_history".
  iMod (history_model_certified γh c h m E HE Hhcoh with "Hishist Hhist") as "[Hhist #Hcerts]".
  iModIntro. iFrame "Hcerts".
  iExists state, ds, insert_sl. iFrame "Hstore Htrstore Hinsertf Hinsert". iSplitR; first done.
  iExists acc. iFrame "Hhist Hpendcert Hacc". done.
Qed.

(** Borrowing what [notifyUpdate] reads: the transaction's [store] field,
    the store's [updateObservers] field and the slice it holds, with the
    contract of every registration. *)
#[local] Lemma own_transaction_notified_update_observers_acc (tr s_loc : loc) (γs : store_names)
    (γh : history_names) (c : ClientId) (h : list Ev) (m : DocModel) (pend : list Input)
    (deleted inserted : gset YjsId) :
  own_transaction_notified tr s_loc γs γh c h m pend deleted inserted -∗
  ∃ (observers_slice : slice.t) (observers : list yjs.updateObserver.t),
    (tr .[(yjs.Transaction.t), "store"]) ↦ s_loc ∗
    (s_loc .[(yjs.store.t), "updateObservers"]) ↦ observers_slice ∗
    observers_slice ↦* observers ∗
    □ ([∗ list] observer ∈ observers, is_update_observer γs.(sn_may_insert) γh observer) ∗
    ((tr .[(yjs.Transaction.t), "store"]) ↦ s_loc -∗
     (s_loc .[(yjs.store.t), "updateObservers"]) ↦ observers_slice -∗
     observers_slice ↦* observers -∗
     own_transaction_notified tr s_loc γs γh c h m pend deleted inserted).
Proof.
  iIntros "Htx". iDestruct "Htx" as (state ds insert_sl) "Htx". iNamed "Htx".
  iDestruct "Hstore" as "[Hcore Hobservers]".
  iDestruct "Hobservers" as (observers_mref) "(Hobserversf & Hregistry & Hupdate_observers)".
  iDestruct "Hupdate_observers" as (observers_slice observers)
    "(Hupdate_observers_field & Hupdate_observers_slice & Hupdate_observers_cap & #Hupdate_observers_specs)".
  iExists observers_slice, observers.
  iFrame "Htrstore Hupdate_observers_field Hupdate_observers_slice Hupdate_observers_specs".
  iIntros "Htrstore Hupdate_observers_field Hupdate_observers_slice".
  iExists state, ds, insert_sl. iSplitR; first done.
  iFrame "Hreplica_history Htrstore Hinsertf Hinsert Hcore".
  iExists observers_mref. iFrame "Hobserversf Hregistry".
  iExists observers_slice, observers.
  iFrame "Hupdate_observers_field Hupdate_observers_slice Hupdate_observers_cap Hupdate_observers_specs".
Qed.

(** The structs read back for what a transaction inserted are well formed:
    each character is an item of a root type, whose clock fits. *)
#[local] Lemma inserted_structs_update_wf (structs : list Input) (m : DocModel)
    (inserted : gset YjsId) :
  structs_expand_to_items structs (λ name item,
    item ∈ doc_model_get m (RootId name) ∧ item_id item ∈ inserted) ->
  (∀ (name : P) (item : YjsItem A), item ∈ doc_model_get m (RootId name) ->
     (Z.of_nat (clock (item_id item)) + 1 < 2^64)%Z) ->
  update_wf (expand_inputs structs).
Proof.
  move=> Hstructs Hfits. split.
  - move=> input Hinput.
    have Hone := expand_inputs_unit_content structs input Hinput.
    destruct (proj1 (Hstructs input) Hinput) as (name & item & [Hitem _] & ->).
    rewrite /input_fits Hone /=. exact (Hfits name item Hitem).
  - move=> input Hinput.
    destruct (proj1 (Hstructs input) Hinput) as (name & item & _ & ->).
    rewrite /pending_item_rooted. case_decide; last done. by exists name.
Qed.

(** What the closure showed of the inserted items holds of the structs
    read back for them. *)
#[local] Lemma inserted_structs_units_allowed (allowed : w16 -> Prop) (structs : list Input)
    (m : DocModel) (inserted : gset YjsId) :
  structs_expand_to_items structs (λ name item,
    item ∈ doc_model_get m (RootId name) ∧ item_id item ∈ inserted) ->
  inserted_units_allowed allowed m inserted ->
  structs_units_allowed allowed structs.
Proof.
  move=> Hstructs Hallowed struct Hstruct. apply Forall_forall => unit Hunit.
  destruct (expand_inputs_content_unit structs struct unit Hstruct Hunit) as (op & Hop & Hcontent).
  destruct (proj1 (Hstructs op) Hop) as (name & item & [Hitem Hid] & ->).
  have Hitem_allowed := Hallowed name item Hitem Hid.
  rewrite /input_of_item /= in Hcontent. rewrite Hcontent in Hitem_allowed.
  exact (proj1 (Forall_singleton _ _) Hitem_allowed).
Qed.

(** [notifyUpdate]: the transaction and its origin field come back as they
    were. The rule premise is what [transact] received from the closure
    ([closure_runs_transaction]); the callbacks' contracts are in the store
    ([own_update_observers]). *)
Lemma wp_Transaction__notifyUpdate (tr s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel) (pend : list Input)
    (deleted inserted : gset YjsId) (origin : go_string) :
  {{{ is_pkg_init yjs ∗ own_transaction_notified tr s_loc γs γh c h m pend deleted inserted ∗
      own_transaction_origin tr origin ∗
      ⌜inserted_units_allowed (γs.(sn_may_insert) origin) m inserted⌝ }}}
    tr @! (go.PointerType yjs.Transaction) @! "notifyUpdate" #()
  {{{ RET #(); own_transaction_notified tr s_loc γs γh c h m pend deleted inserted ∗
      own_transaction_origin tr origin }}}.
Proof.
  rewrite /own_transaction_origin.
  wp_start as "(Htx & Horigin & %Hallowed)".
  iDestruct (own_transaction_notified_item_clock_fits with "Htx") as %Hfits.
  (* ---- is anybody registered? ---- *)
  iDestruct (own_transaction_notified_update_observers_acc with "Htx")
    as (observers_slice0 observers0) "(Htrstore & Hfield & Hslice & #Hspecs0 & Hclose)".
  wp_auto.
  iDestruct (own_slice_len with "Hslice") as %[Hobservers0_length Hobservers0_nonneg].
  destruct (decide (observers_slice0.(slice.len) = W64 0)) as [Hnone | Hsome].
  { rewrite bool_decide_eq_true_2 //. wp_auto. iApply "HΦ". iFrame "Horigin".
    iApply ("Hclose" with "Htrstore Hfield Hslice"). }
  rewrite bool_decide_eq_false_2 //.
  (* the first registration carries the global history's invariant *)
  have [observer0 Hobserver0] : is_Some (observers0 !! 0%nat).
  { apply lookup_lt_is_Some. clear -Hsome Hobservers0_length Hobservers0_nonneg. word. }
  iDestruct (big_sepL_lookup _ _ 0%nat observer0 Hobserver0 with "Hspecs0") as "Hobserver0".
  iDestruct "Hobserver0" as (encode0) "(#Hishist & _ & _)".
  iDestruct ("Hclose" with "Htrstore Hfield Hslice") as "Htx".
  wp_auto.
  (* ---- the update ---- *)
  wp_apply (wp_Transaction__insertedStructs with "[$Htx]").
  iIntros (structs_slice structs) "(Htx & Hstructs & %Hstructs)".
  wp_auto.
  destruct (decide (structs_slice.(slice.len) = W64 0)) as [Hempty | Hcontent].
  { rewrite bool_decide_eq_true_2 //. wp_auto. iApply "HΦ". iFrame "Horigin Htx". }
  rewrite bool_decide_eq_false_2 //.
  iMod (own_transaction_notified_model_certified _ _ _ _ _ _ _ _ _ _ ⊤ with "Hishist Htx")
    as "[Htx #Hcerts]"; first done.
  iAssert (is_update_certified γh structs) as "#Hcertified".
  { iSplit; first (iPureIntro; exact (inserted_structs_update_wf structs m inserted Hstructs Hfits)).
    rewrite /is_pending_certified. iApply big_sepL_forall. iIntros (k input Hk).
    destruct (proj1 (Hstructs input) (list_elem_of_lookup_2 _ _ _ Hk)) as (name & item & [Hitem _] & ->).
    iApply ("Hcerts" $! (RootId name) item Hitem). }
  have Hunits : structs_units_allowed (γs.(sn_may_insert) origin) structs :=
    inserted_structs_units_allowed _ structs m inserted Hstructs Hallowed.
  (* ---- every registration, in the slice's order ---- *)
  iDestruct (own_transaction_notified_update_observers_acc with "Htx")
    as (observers_slice observers) "(Htrstore & Hfield & Hslice & #Hspecs & Hclose)".
  wp_auto.
  iDestruct (own_slice_len with "Hslice") as %[Hobservers_length Hobservers_nonneg].
  iAssert (∃ (i : w64),
      "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i⌝)%I with "[i]" as "IH".
  { iExists (W64 0). iFrame "i". iPureIntro. word. }
  wp_for "IH".
  destruct (decide (sint.Z i < sint.Z observers_slice.(slice.len))) as [Hinside | Hpast]; last first.
  { rewrite bool_decide_eq_false_2 //. wp_auto. iApply "HΦ". iFrame "Horigin".
    iApply ("Hclose" with "Htrstore Hfield Hslice"). }
  rewrite bool_decide_eq_true_2 //.
  wp_auto.
  rewrite decide_True; last (clear -Hinside Hi; word).
  have [observer Hobserver] : is_Some (observers !! sint.nat i).
  { apply lookup_lt_is_Some. clear -Hinside Hi Hobservers_length. word. }
  iDestruct (own_slice_elem_acc (sint.Z i) observer observers_slice (DfracOwn 1) observers with "Hslice")
    as "[Helem Hgive]".
  { clear -Hinside Hi. word. }
  { exact Hobserver. }
  wp_auto.
  iDestruct ("Hgive" $! observer with "Helem") as "Hslice".
  iEval (rewrite (list_insert_id _ _ _ Hobserver)) in "Hslice".
  iDestruct (big_sepL_lookup _ _ _ observer Hobserver with "Hspecs") as "Hobserver".
  iDestruct "Hobserver" as (encode) "(_ & #Hencoder & #Hcallback)".
  wp_apply ("Hencoder" with "[$Hstructs]").
  iIntros (bytes_slice) "(Hstructs & Hbytes & Hbytes_cap)".
  wp_auto.
  wp_apply ("Hcallback" $! bytes_slice structs origin with "[$Hbytes $Hbytes_cap $Hcertified]").
  { iPureIntro. exact Hunits. }
  wp_for_post.
  iFrame. iPureIntro. clear -Hinside Hi. word.
Qed.

End transaction_notifyUpdate.
