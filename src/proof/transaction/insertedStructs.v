(** [Transaction.insertedStructs] (issue #131): the structs a transaction
    integrated, read back from the store as decoded update items. What the
    caller learns is stated per character over the transaction's public
    model: the characters the structs carry are exactly the items of the
    document model whose ids the transaction recorded as inserted, each
    under the name of its root. That is what a sender needs to find the
    certificates of what it is about to encode, and to know that it sends
    everything the transaction inserted. *)
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
From New.proof.transaction Require Import model heap wp_private.
From New.proof.delta Require Import delta.

(* iris.algebra pushes [nat_scope], retuning the default [<] / [≤]; the
   word-arithmetic proofs write [Z] comparisons unannotated, so restore
   [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section transaction_insertedStructs.

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

Lemma wp_Transaction__insertedStructs (tr s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel) (pend : list Input)
    (deleted inserted tombstoned : gset YjsId) (changed : gset P) :
  {{{ is_pkg_init yjs ∗ own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed }}}
    tr @! (go.PointerType yjs.Transaction) @! "insertedStructs" #()
  {{{ (structs_slice : slice.t) (structs : list Input), RET #structs_slice;
      own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed ∗
      own_update_structs structs_slice (DfracOwn 1) structs ∗
      ⌜structs_expand_to_items structs (λ name item,
         item ∈ doc_model_get m (RootId name) ∧ item_id item ∈ inserted)⌝ }}}.
Proof.
  wp_start as "Htx".
  iDestruct "Htx" as (state ds m0 deleted0) "Htx". iNamed "Htx".
  iDestruct (own_replica_history_registry_models with "Hreplica_history") as %[Hmodels Hbound].
  iAssert (⌜pool_registry_coh (ss_bind state) (ss_pool state)⌝)%I as %Hregistry_coh.
  { iNamed "Hstore". iNamed "Hcore". iApply (own_store_state_registry_coh with "Hstate"). }
  (* the items of the registry are the items of the public model *)
  have Hregistry_items : ∀ (name : P) (item : YjsItem A),
      registry_has_item (ss_bind state) (ss_pool state) name item <-> item ∈ doc_model_get m (RootId name).
  { move=> name item. split.
    - intros (parent & tm & Hname & Hparent & Hitem). by rewrite (Hmodels name parent tm Hname Hparent).
    - move=> Hitem.
      have Hnonempty : doc_model_get m (RootId name) ≠ [].
      { move=> Hnil. rewrite Hnil in Hitem. by apply elem_of_nil in Hitem. }
      destruct (Hbound _ Hnonempty) as (name' & parent & [= <-] & Hbind).
      destruct (proj1 Hregistry_coh name parent Hbind) as [tm Htm].
      exists parent, tm. split_and!; [exact Hbind | exact Htm |].
      by rewrite -(Hmodels name parent tm Hbind Htm). }
  iDestruct "Hrecord" as (changed_locs) "Hrecord". iNamed "Hrecord". iNamed "Hchanges".
  wp_auto.
  iAssert (∃ (i : w64) (structs_slice : slice.t) (structs : list Input),
      "tr" ∷ tr_ptr ↦ tr ∗ "s" ∷ s_ptr ↦ s_loc ∗ "i" ∷ i_ptr ↦ i ∗
      "structs" ∷ structs_ptr ↦ structs_slice ∗
      "Hinsertf" ∷ (tr .[(yjs.Transaction.t), "insertSet"]) ↦ insert_sl ∗
      "Hinsert" ∷ insert_sl ↦* insert_vs ∗
      "Hstore" ∷ own_store s_loc γs γh 1 state ds m0 deleted0 ∗
      "Hstructs" ∷ own_update_structs structs_slice (DfracOwn 1) structs ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ ∗
      "%Hstructs_model" ∷ ⌜structs_expand_to_items structs (λ name item,
           item ∈ doc_model_get m (RootId name) ∧
           item_id item ∈ ⋃ (span_ids <$> take (sint.nat i) insert_vs))⌝)%I
    with "[tr s i structs Hinsertf Hinsert Hstore]" as "IH".
  { iExists (W64 0), slice.nil, []. iFrame "tr s i structs Hinsertf Hinsert Hstore".
    iSplitL.
    { iExists []. iSplitL; first iApply own_slice_nil. iSplitL; first iApply own_slice_cap_nil.
      by iApply big_sepL2_nil. }
    iPureIntro. split; first done.
    move=> input. split; first by move=> /elem_of_nil.
    intros (name & item & [_ Hid] & _). exfalso.
    replace (sint.nat (W64 0)) with 0%nat in Hid by word.
    rewrite take_0 /= in Hid. by apply elem_of_empty in Hid. }
  wp_for "IH".
  iDestruct (own_slice_len with "Hinsert") as %[Hinsert_length Hinsert_nonneg].
  destruct (decide (sint.Z i < sint.Z insert_sl.(slice.len))) as [Hinside | Hpast]; last first.
  { (* every span is read: hand the transaction back *)
    rewrite bool_decide_eq_false_2 //. wp_auto.
    iApply ("HΦ" $! structs_slice structs). iFrame "Hstructs".
    iSplitL; last first.
    { iPureIntro. move: Hstructs_model.
      rewrite take_ge; last (clear -Hpast Hi Hinsert_length Hinsert_nonneg; word).
      by rewrite -Hinserted. }
    iExists state, ds, m0, deleted0. iSplitR; first done.
    iFrame "Hstore Hreplica_history". iSplitL; last done.
    iExists changed_locs. iFrame "Hchanged_bound".
    iSplitL; last done.
    iExists insert_sl, delete_sl, changed_mref, insert_vs, delete_vs.
    iFrame "Htrstore Hinsertf Hinsert Hinsertcap Hdeletef Hdelete Hdeletecap Hchangedf Hchanged". done. }
  rewrite bool_decide_eq_true_2 //.
  wp_auto.
  rewrite decide_True; last (clear -Hinside Hi; word).
  have [span Hspan_lookup] : is_Some (insert_vs !! sint.nat i).
  { apply lookup_lt_is_Some. clear -Hinside Hi Hinsert_length. word. }
  iDestruct (own_slice_elem_acc (sint.Z i) span insert_sl (DfracOwn 1) insert_vs with "Hinsert")
    as "[Helem Hgive]".
  { clear -Hinside Hi. word. }
  { exact Hspan_lookup. }
  wp_auto.
  iDestruct ("Hgive" $! span with "Helem") as "Hinsert".
  iEval (rewrite (list_insert_id _ _ _ Hspan_lookup)) in "Hinsert".
  have Hspan_fits : span_no_overflow span.
  { exact (proj1 (Forall_forall _ _) Hinsertwf span (list_elem_of_lookup_2 _ _ _ Hspan_lookup)). }
  wp_apply (wp_store__appendSpanStructs s_loc γs γh state ds m0 deleted0 structs_slice structs span
              Hspan_fits with "[$Hstore $Hstructs]").
  iIntros (result_slice appended) "(Hstore & Hstructs & %Happended)".
  wp_auto.
  wp_for_post.
  iFrame. iPureIntro. split; first (clear -Hinside Hi; word).
  have Htake : ∀ n : nat, n = S (sint.nat i) ->
      take n insert_vs = take (sint.nat i) insert_vs ++ [span].
  { move=> n ->. exact (take_S_r _ _ _ Hspan_lookup). }
  erewrite Htake; last (clear -Hinside Hi Hinsert_nonneg; word).
  rewrite fmap_app union_list_app_L /= union_empty_r_L.
  move=> input. rewrite expand_inputs_app elem_of_app (Hstructs_model input) (Happended input).
  split.
  - intros [(name & item & [Hitem Hid] & ->) | (name & item & [Hregistry Hid] & ->)];
      exists name, item; (split; last reflexivity).
    + split; first exact Hitem. apply elem_of_union. by left.
    + split; first by apply Hregistry_items. apply elem_of_union. by right.
  - intros (name & item & [Hitem Hid] & ->). apply elem_of_union in Hid as [Hid | Hid].
    + left. by exists name, item.
    + right. exists name, item. split; last reflexivity. split; [by apply Hregistry_items | exact Hid].
Qed.

End transaction_insertedStructs.
