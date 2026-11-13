(** [Transaction.insertedStructs] (issue #131): the structs a transaction
    integrated, read back from the store as decoded update items. What the
    caller learns is stated per character over the transaction's public
    model: every character the structs carry is an item of the document
    model whose id the transaction recorded as inserted, under the name of
    its root. That is what a sender needs to find the certificates of what
    it is about to encode. *)
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
      ⌜∀ op, op ∈ expand_inputs structs ->
         ∃ (name : P) (it : YjsItem A),
           it ∈ doc_model_get m (RootId name) ∧ op = (RootId name, input_of_item it) ∧
           item_id it ∈ inserted⌝ }}}.
Proof.
  wp_start as "Htx".
  iDestruct "Htx" as (state ds m0 deleted0) "Htx". iNamed "Htx".
  iDestruct (own_replica_history_registry_models with "Hreplica_history") as %[Hmodels _].
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
      "%Hstructs_model" ∷ ⌜∀ op, op ∈ expand_inputs structs ->
         ∃ (name : P) (it : YjsItem A),
           it ∈ doc_model_get m (RootId name) ∧ op = (RootId name, input_of_item it) ∧
           item_id it ∈ inserted⌝)%I
    with "[tr s i structs Hinsertf Hinsert Hstore]" as "IH".
  { iExists (W64 0), slice.nil, []. iFrame "tr s i structs Hinsertf Hinsert Hstore".
    iSplitL.
    { iExists []. iSplitL; first iApply own_slice_nil. iSplitL; first iApply own_slice_cap_nil.
      by iApply big_sepL2_nil. }
    iPureIntro. split; first done. by move=> op /elem_of_nil. }
  wp_for "IH".
  iDestruct (own_slice_len with "Hinsert") as %[Hinsert_length Hinsert_nonneg].
  destruct (decide (sint.Z i < sint.Z insert_sl.(slice.len))) as [Hinside | Hpast]; last first.
  { (* every span is read: hand the transaction back *)
    rewrite bool_decide_eq_false_2 //. wp_auto.
    iApply ("HΦ" $! structs_slice structs). iFrame "Hstructs".
    iSplitL; last done.
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
  move=> op. rewrite expand_inputs_app elem_of_app.
  move=> [Hold | Hnew]; first exact (Hstructs_model op Hold).
  destruct (Happended op Hnew) as (name & parent & tm & r & it & Hname & Hparent & Hr & Hit & -> & Hid).
  exists name, it. split_and!; last first.
  - rewrite Hinserted elem_of_union_list. exists (span_ids span). split; last exact Hid.
    apply list_elem_of_fmap. exists span. split; [reflexivity | exact (list_elem_of_lookup_2 _ _ _ Hspan_lookup)].
  - reflexivity.
  - rewrite (Hmodels name parent tm Hname Hparent) /tm_arr /runs_flatten list_elem_of_join.
    exists (run_items r). split; first exact Hit. apply list_elem_of_fmap. by exists r.
Qed.

End transaction_insertedStructs.
