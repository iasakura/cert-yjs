(** The [Transaction] record's operations (issue #206 T1): what a transaction
    records while it runs.

    - [wp_newTransaction]: a fresh record, of the given store, that has
      recorded nothing.
    - [wp_Transaction__recordInsert]: a freshly integrated node joins the
      insert set (its head id and length as one span) and its parent joins
      the changed types.
    - [wp_Transaction__recordDelete]: a node this transaction tombstones
      joins the delete set the same way, and its parent the changed types.

    Both record steps read the node's id and length off its points-to; they
    are called by [store.Integrate] and [deleteNode] on a node the store
    holds, which borrow the node for the call. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From iris.algebra Require Import auth gmap gset.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import model.
From New.proof.store Require Import model value.
From New.proof.transaction Require Import heap.

Section transaction_wp.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Lemma wp_newTransaction (s_loc : loc) :
  {{{ is_pkg_init yjs }}}
    @! yjs.newTransaction #s_loc
  {{{ (tr : loc), RET #tr; own_transaction_changes tr s_loc ∅ ∅ ∅ }}}.
Proof.
  wp_start. wp_auto.
  wp_apply wp_map_make1. iIntros (changed_mref) "Hchanged". wp_auto.
  wp_alloc tr as "Htr". wp_auto.
  iApply "HΦ".
  iExists _, [], []. iFrame "Htr".
  rewrite gset_to_gmap_empty. iFrame "Hchanged".
  iSplitR; first done.
  iSplitL; first iApply own_slice_nil.
  iSplitL; first iApply own_slice_cap_nil.
  iSplitR; first done.
  iSplitR; first done.
  iSplitL; first iApply own_slice_nil.
  iSplitL; first iApply own_slice_cap_nil.
  done.
Qed.

Lemma wp_Transaction__recordInsert (tr s_loc parent lc : loc) (dq : dfrac) (v : yjs.item.t)
    (inserted tombstoned : gset YjsId) (changed : gset loc) :
  span_no_overflow (node_span v) ->
  {{{ is_pkg_init yjs ∗ own_transaction_changes tr s_loc inserted tombstoned changed ∗ lc ↦{dq} v }}}
    tr @! (go.PointerType yjs.Transaction) @! "recordInsert" #parent #lc
  {{{ RET #();
      own_transaction_changes tr s_loc (inserted ∪ span_ids (node_span v)) tombstoned
        (changed ∪ {[parent]}) ∗
      lc ↦{dq} v }}}.
Proof.
  move=> Hfits.
  wp_start as "(Hchanges & Hv)". iNamed "Hchanges". wp_auto.
  wp_apply (wp_item__Len with "[$Hv]"). iIntros "[Hv _]". wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
  wp_apply (wp_slice_append with "[$Hinsert $Hinsertcap $Hs2]").
  iIntros (sl') "(Hinsert & Hinsertcap & _)". wp_auto.
  wp_apply (wp_map_insert with "Hchanged"). iIntros "Hchanged". wp_auto.
  iApply "HΦ". iFrame "Hv".
  iExists _, (insert_vs ++ [node_span v]), delete_vs. simpl.
  iFrame "Htr Hinsert Hinsertcap Hdelete Hdeletecap".
  rewrite (union_comm_L changed) gset_to_gmap_union_singleton. iFrame "Hchanged".
  iPureIntro. split_and!; [done | | | done | done].
  - apply Forall_app. split; [exact Hinsertwf | by apply Forall_singleton].
  - rewrite span_union_snoc Hinserted. apply union_comm_L.
Qed.

Lemma wp_Transaction__recordDelete (tr s_loc lc : loc) (dq : dfrac) (v : yjs.item.t)
    (inserted tombstoned : gset YjsId) (changed : gset loc) :
  span_no_overflow (node_span v) ->
  {{{ is_pkg_init yjs ∗ own_transaction_changes tr s_loc inserted tombstoned changed ∗ lc ↦{dq} v }}}
    tr @! (go.PointerType yjs.Transaction) @! "recordDelete" #lc
  {{{ RET #();
      own_transaction_changes tr s_loc inserted (tombstoned ∪ span_ids (node_span v))
        (changed ∪ {[v.(yjs.item.parent')]}) ∗
      lc ↦{dq} v }}}.
Proof.
  move=> Hfits.
  wp_start as "(Hchanges & Hv)". iNamed "Hchanges". wp_auto.
  wp_apply (wp_item__Len with "[$Hv]"). iIntros "[Hv _]". wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
  wp_apply (wp_slice_append with "[$Hdelete $Hdeletecap $Hs2]").
  iIntros (sl') "(Hdelete & Hdeletecap & _)". wp_auto.
  wp_apply (wp_map_insert with "Hchanged"). iIntros "Hchanged". wp_auto.
  iApply "HΦ". iFrame "Hv".
  iExists _, insert_vs, (delete_vs ++ [node_span v]). simpl.
  iFrame "Htr Hinsert Hinsertcap Hdelete Hdeletecap".
  rewrite (union_comm_L changed) gset_to_gmap_union_singleton. iFrame "Hchanged".
  iPureIntro. split_and!; [done | done | done | | ].
  - apply Forall_app. split; [exact Hdeletewf | by apply Forall_singleton].
  - rewrite span_union_snoc Htombstoned. apply union_comm_L.
Qed.

End transaction_wp.
