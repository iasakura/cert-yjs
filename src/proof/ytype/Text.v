(** [wp_yType__Text]: the visible-string read, a left-to-right walk over the
    item DLL concatenating the content of every non-tombstoned node (issue
    #125). Read-only, so stated at a generic [dq]; the return value is the
    pure [visible_string] of the cell model, which is what ties
    [Text.String] to the snapshot the read lock exposes.

    Stated over the representation predicates of [ytype/heap.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import model value heap.

Local Open Scope Z_scope.

Section ytype.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Lemma wp_yType__Text (parent : loc) (dq : dfrac) (cells : list item_cell)
    (arr : list (YjsItem A)) :
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent dq cells arr }}}
    parent @! (go.PointerType yjs.yType) @! "Text" #()
  {{{ RET #(visible_string (cells_model cells)); own_ytype_cells parent dq cells arr }}}.
Proof.
  wp_start as "Hyt". iNamed "Hyt".
  iDestruct (own_dll_head_node dq cells _ tl with "Hdll") as %Hhead.
  wp_auto.
  iAssert (∃ (k : nat),
    "Hp" ∷ parent ↦{dq} yt ∗
    "Hdll" ∷ own_dll dq yt.(yjs.yType.start') tl null null cells ∗
    "Hresult" ∷ result_ptr ↦ visible_string (cells_model (take k cells)) ∗
    "Hcur" ∷ cur_ptr ↦ node_loc cells (Z.of_nat k) ∗
    "%Hk" ∷ ⌜(k <= length cells)%nat⌝)%I
    with "[Hparent Hdll result cur]" as "IH".
  { iExists 0%nat. rewrite take_0 /= -Hhead. iFrame. iPureIntro; lia. }
  wp_for "IH".
  destruct (decide (k < length cells)%nat) as [Hlt | Hge].
  - (* cur ≠ null: read the node, append its content when visible, advance *)
    iDestruct (node_loc_lt_not_null dq cells _ tl k Hlt with "Hdll") as "[%Hnn Hdll]".
    rewrite (bool_decide_eq_false_2 (node_loc cells (Z.of_nat k) = null) Hnn).
    simpl negb.
    destruct (cells !! k) as [c|] eqn:Hc; [| apply lookup_ge_None in Hc; lia].
    iDestruct (own_dll_acc dq cells _ tl k c Hc with "Hdll") as "H". iNamed "H".
    iEval (rewrite -Hcloc) in "Hcur".
    rewrite decide_True; [| reflexivity].
    wp_auto.
    wp_apply (wp_item__Deleted c.(ic_loc) dq itemVal with "[$Hcval]"). iIntros "Hcval".
    rewrite (flags_if_deleted itemVal (ic_deleted c) Hflags).
    destruct (ic_deleted c) eqn:Hd; simpl negb.
    + (* tombstone: contributes nothing *)
      wp_auto.
      iDestruct ("Hback" with "Hcval") as "Hdll".
      wp_for_post.
      iFrame "HΦ". iExists (S k). iFrame "Hp Hdll".
      rewrite (visible_string_take_S cells k c _ Hc Hcontent) Hd app_nil_r.
      iFrame "Hresult".
      rewrite Hcr. replace (Z.of_nat k + 1)%Z with (Z.of_nat (S k)) by lia.
      iFrame "Hcur". iPureIntro. lia.
    + (* visible: append the node's content string *)
      wp_auto.
      iDestruct ("Hback" with "Hcval") as "Hdll".
      wp_for_post.
      iFrame "HΦ". iExists (S k). iFrame "Hp Hdll".
      rewrite (visible_string_take_S cells k c _ Hc Hcontent) Hd.
      iFrame "Hresult".
      rewrite Hcr. replace (Z.of_nat k + 1)%Z with (Z.of_nat (S k)) by lia.
      iFrame "Hcur". iPureIntro. lia.
  - (* cur = null: the walk is done, return the accumulated string *)
    have Hkeq : k = length cells by lia.
    have Hnull : node_loc cells (Z.of_nat k) = null.
    { rewrite /node_loc decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
    rewrite (bool_decide_eq_true_2 (node_loc cells (Z.of_nat k) = null) Hnull).
    simpl negb.
    rewrite decide_False; [| done]. rewrite decide_True; [| done].
    wp_auto.
    rewrite Hkeq take_ge; [| lia].
    iApply "HΦ".
    iExists yt, tl. iFrame "Hp Hdll".
    iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar].
Qed.

End ytype.
