(** The [yType] type: the heap representation of a root sequence and the WP spec
    of its visible-index navigation.

    In y-octo [YType] is the lock-guarded inner data structure while the [YText]
    handle lives outside the lock; this module owns the [YType] side and is closed
    over implementation ([yjs/ytype.go]), spec, and proof:

    - [is_ytype] / [is_valid_ytype]: a heap [yType] whose [start] heads an item
      DLL ([is_dll], from [yjs_item]), isomorphic to a model list that — for
      [is_valid_ytype] — satisfies [YjsArrInvariant]. [len] counts the visible
      (non-deleted) cells ([num_visible]); deletions tombstone cells without
      removing them, so [cells] / [arr] keep every item.
    - [wp_yType__findPos]: the tombstone-aware walk to a visible character index,
      returning the straddling neighbours (an existential list position [p]);
      feeds the [Store.Integrate] loop in [Text.Insert] and [Text.Delete].

    Sits between [yjs_item] (the per-node / DLL / deletion layer it builds on) and
    [yjs_store] (which states [Store.Integrate] against [is_ytype]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id yjs_item.

(* The [findPos] word-arithmetic proof writes [Z] comparisons unannotated, so fix
   [Z_scope] as the default (matching the environment it was developed in). *)
Local Open Scope Z_scope.

Section ytype.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(** [is_ytype parent cells arr]: [parent] is a heap [yType] whose [start] heads
    the DLL [cells], which is isomorphic to the model [arr]. [len] counts the
    visible (non-deleted) cells ([num_visible]); a deletion tombstones a cell (set
    its [ic_deleted] bit) without removing it, so [cells] / [arr] keep every
    item. *)
Definition is_ytype (parent : loc) (cells : list item_cell) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ (yt : yjs.yType.t) (tl : loc),
    "Hparent" ∷ parent ↦ yt ∗
    "Hdll" ∷ is_dll yt.(yjs.yType.start') tl null null cells ∗
    "%Hlen" ∷ ⌜yt.(yjs.yType.len') = W64 (num_visible cells)⌝ ∗
    "%Hrepr" ∷ ⌜cells_repr arr cells arr⌝.

(** The full data-structure invariant: a heap [yType] representing a *valid*
    model [arr] — DLL structure + isomorphism to a [YjsArrInvariant] list. *)
Definition is_valid_ytype (parent : loc) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ cells,
    "Htext" ∷ is_ytype parent cells arr ∗
    "%Hinv" ∷ ⌜YjsArrInvariant arr⌝.

(** General tombstone-aware [findPos]: walk to the visible character index [idx]
    (≤ number of *visible* nodes) and return the straddling neighbours. The Go
    walks two loops: a skip loop that advances past leading tombstones, then a
    count loop that spends the budget [idx] on visible ([Indexable]) nodes only.
    Deletions make the answer a *list* position [p] (the node index, ≥ the visible
    index because tombstones are skipped), so the spec returns an existential [p ≤
    length cells] with the two straddle locations [node_loc cells (p-1)] /
    [node_loc cells p] (which are [null] out of range). That an adjacent
    ([left]/[right]) pair is all the [Insert] / [Delete] callers need. *)
Lemma wp_yType__findPos (parent : loc) (cells : list item_cell)
    (arr : list (YjsItem A)) (idx : w64) :
  {{{ is_pkg_init yjs ∗ is_ytype parent cells arr }}}
    parent @! (go.PointerType yjs.yType) @! "findPos" #idx
  {{{ (lft rgt : loc) (p : nat), RET (#lft, #rgt);
      is_ytype parent cells arr ∗
      ⌜(p <= length cells)%nat⌝ ∗
      ⌜lft = node_loc cells (Z.of_nat p - 1)⌝ ∗
      ⌜rgt = node_loc cells (Z.of_nat p)⌝ }}}.
Proof.
  wp_start as "Hyt". iNamed "Hyt".
  iDestruct (is_dll_head_node cells _ tl with "Hdll") as %Hhead.
  destruct cells as [|c0 cs].
  - (* empty document: both loops are no-ops, return (null, null) at p = 0 *)
    iDestruct "Hdll" as %[Hs Ht]. wp_auto. rewrite Hs.
    iAssert ("Hp" ∷ parent ↦ yt ∗ "Hl" ∷ left_ptr ↦ null ∗ "Hr" ∷ right_ptr ↦ null ∗ "Hidx" ∷ index_ptr ↦ idx)%I
      with "[Hparent left right index]" as "IH".
    { iFrame. }
    wp_for "IH".
    iAssert ("Hp" ∷ parent ↦ yt ∗ "Hl" ∷ left_ptr ↦ null ∗ "Hr" ∷ right_ptr ↦ null ∗ "Hrem" ∷ remaining_ptr ↦ idx)%I
      with "[Hp Hl Hr remaining]" as "IH".
    { iFrame. }
    wp_for "IH".
    wp_if_destruct.
    + wp_auto. iApply ("HΦ" $! null null 0%nat). iSplitL "Hp".
      { iExists yt, null. iFrame "Hp". iPureIntro. split_and!; [exact Hs | reflexivity | exact Hlen | exact Hrepr]. }
      iPureIntro. split_and!; [lia | rewrite /node_loc; case_decide; reflexivity | rewrite /node_loc; case_decide; reflexivity].
    + iApply ("HΦ" $! null null 0%nat). iSplitL "Hp".
      { iExists yt, null. iFrame "Hp". iPureIntro. split_and!; [exact Hs | reflexivity | exact Hlen | exact Hrepr]. }
      iPureIntro. split_and!; [lia | rewrite /node_loc; case_decide; reflexivity | rewrite /node_loc; case_decide; reflexivity].
  - (* non-empty: skip leading tombstones, then count visible nodes to [idx] *)
    wp_auto.
    (* ----- skip loop invariant (runs before [remaining := index]) ----- *)
    iAssert (∃ (q : nat),
      "Hp" ∷ parent ↦ yt ∗
      "Hdll" ∷ is_dll yt.(yjs.yType.start') tl null null (c0 :: cs) ∗
      "Hindex" ∷ index_ptr ↦ idx ∗
      "Hleftp" ∷ left_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q - 1) ∗
      "Hrightp" ∷ right_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q) ∗
      "%Hq" ∷ ⌜(q <= length (c0 :: cs))%nat⌝)%I
      with "[Hparent Hdll index left right]" as "IH".
    { iExists 0%nat. iFrame "Hparent Hdll index".
      replace (Z.of_nat 0 - 1)%Z with (-1)%Z by lia.
      have Hm1 : node_loc (c0 :: cs) (-1)%Z = null by (rewrite /node_loc; case_decide; [lia | done]).
      rewrite Hm1. iFrame "left".
      have Hr0 : node_loc (c0 :: cs) (Z.of_nat 0) = yt.(yjs.yType.start') by rewrite Hhead.
      rewrite Hr0. iFrame "right". iPureIntro. simpl; lia. }
    wp_for "IH".
    destruct (decide (q < length (c0 :: cs))%nat) as [Hqlt | Hqge].
    + (* right ≠ null: evaluate Deleted; tombstone ⇒ advance, else exit to count *)
      iDestruct (node_loc_lt_not_null (c0 :: cs) yt.(yjs.yType.start') tl q Hqlt with "Hdll") as "[%Hnn Hdll]".
      rewrite (bool_decide_eq_false_2 (node_loc (c0 :: cs) q = null) Hnn). simpl negb.
      destruct ((c0 :: cs) !! q) as [cq|] eqn:Hcq; [| apply lookup_ge_None in Hcq; lia].
      iDestruct (is_dll_acc (c0 :: cs) yt.(yjs.yType.start') tl q cq Hcq with "Hdll") as "H". iNamed "H".
      iEval (rewrite -Hcloc) in "Hrightp".
      wp_auto.
      wp_apply (wp_item__Deleted cq.(ic_loc) iv with "[$Hcval]"). iIntros "Hcval".
      rewrite (flags_if_deleted iv (ic_deleted cq) Hflags).
      destruct (ic_deleted cq) eqn:Hdq.
      * (* tombstone: advance the cursor, re-establish the skip invariant *)
        rewrite decide_True; [| reflexivity].
        wp_auto.
        iDestruct ("Hback" with "Hcval") as "Hdll".
        wp_for_post.
        iFrame "HΦ". iExists (S q). iFrame "Hp Hdll Hindex".
        rewrite Hcr. replace (Z.of_nat (S q) - 1)%Z with (Z.of_nat q) by lia.
        replace (Z.of_nat (S q)) with (Z.of_nat q + 1)%Z by lia.
        rewrite Hcloc. iFrame "Hleftp Hrightp". iPureIntro. lia.
      * (* first visible node: skip loop exits, run the count loop from [q] *)
        rewrite decide_False; [| done]. rewrite decide_True; [| done].
        iDestruct ("Hback" with "Hcval") as "Hdll".
        iEval (rewrite Hcloc) in "Hrightp".
        iClear "Hcol Hcor".
        wp_auto.
        iAssert (∃ (q2 : nat) (rem : w64),
          "Hp" ∷ parent ↦ yt ∗
          "Hdll" ∷ is_dll yt.(yjs.yType.start') tl null null (c0 :: cs) ∗
          "Hleftp" ∷ left_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q2 - 1) ∗
          "Hrightp" ∷ right_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q2) ∗
          "Hrem" ∷ remaining_ptr ↦ rem ∗
          "%Hq2" ∷ ⌜(q2 <= length (c0 :: cs))%nat⌝)%I
          with "[Hp Hdll Hleftp Hrightp remaining]" as "IH".
        { iExists q, idx. iFrame "Hp Hdll Hleftp Hrightp remaining". iPureIntro. exact Hq. }
        wp_for "IH".
        case_bool_decide as Hrem.
        2:{ wp_auto. rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (node_loc (c0 :: cs) (Z.of_nat q2 - 1)) (node_loc (c0 :: cs) q2) q2).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr]. }
            iPureIntro. split_and!; [exact Hq2 | reflexivity | reflexivity]. }
        wp_auto.
        destruct (decide (q2 < length (c0 :: cs))%nat) as [Hq2lt | Hq2ge].
        2:{ have Hnull2 : node_loc (c0 :: cs) q2 = null.
            { rewrite /node_loc decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
            rewrite (bool_decide_eq_true_2 (node_loc (c0 :: cs) q2 = null) Hnull2). simpl negb.
            rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (node_loc (c0 :: cs) (Z.of_nat q2 - 1)) (node_loc (c0 :: cs) q2) q2).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr]. }
            iPureIntro. split_and!; [exact Hq2 | reflexivity | reflexivity]. }
        iDestruct (node_loc_lt_not_null (c0 :: cs) yt.(yjs.yType.start') tl q2 Hq2lt with "Hdll") as "[%Hnn2 Hdll]".
        rewrite (bool_decide_eq_false_2 (node_loc (c0 :: cs) q2 = null) Hnn2). simpl negb.
        rewrite decide_True; [| done].
        destruct ((c0 :: cs) !! q2) as [c2|] eqn:Hc2; [| apply lookup_ge_None in Hc2; lia].
        iDestruct (is_dll_acc (c0 :: cs) yt.(yjs.yType.start') tl q2 c2 Hc2 with "Hdll") as (iv2 olid2 orid2)
          "(%Hc2loc & %Hc2l & %Hc2r & %Hc2id & %Hc2cont & %Hc2olid & %Hc2orid & %Hc2flags & %Hc2contlen & Hc2val & #Hc2ol & #Hc2or & Hback2)".
        have Hcount2 : is_countable_flag iv2 = true := flags_if_countable iv2 (ic_deleted c2) Hc2flags.
        have Hdel2 : is_deleted_flag iv2 = ic_deleted c2 := flags_if_deleted iv2 (ic_deleted c2) Hc2flags.
        iEval (rewrite -Hc2loc) in "Hrightp".
        wp_auto.
        wp_apply (wp_item__Indexable c2.(ic_loc) iv2 Hcount2 with "[$Hc2val]"). iIntros "Hc2val".
        rewrite Hdel2.
        destruct (ic_deleted c2) eqn:Hd2; simpl negb; wp_auto.
        2:{ wp_apply (wp_item__Len c2.(ic_loc) iv2 with "[$Hc2val]"). iIntros "Hc2val".
            rewrite Hc2contlen. wp_auto.
            iDestruct ("Hback2" with "Hc2val") as "Hdll".
            wp_for_post.
            iFrame "HΦ". iExists (S q2), (w64_word_instance.(word.sub) rem (W64 1)).
            iFrame "Hp Hdll Hrem".
            rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
            replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
            rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro. lia. }
        iDestruct ("Hback2" with "Hc2val") as "Hdll".
        wp_for_post.
        iFrame "HΦ". iExists (S q2), rem.
        iFrame "Hp Hdll Hrem".
        rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
        replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
        rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro. lia.
    + (* right = null (q = length): skip loop exits, count loop exits at once *)
      have Hnull : node_loc (c0 :: cs) q = null.
      { rewrite /node_loc decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
      rewrite (bool_decide_eq_true_2 (node_loc (c0 :: cs) q = null) Hnull). simpl negb.
      wp_auto.
      rewrite decide_False; [| done]. rewrite decide_True; [| done].
      wp_auto.
        iAssert (∃ (q2 : nat) (rem : w64),
          "Hp" ∷ parent ↦ yt ∗
          "Hdll" ∷ is_dll yt.(yjs.yType.start') tl null null (c0 :: cs) ∗
          "Hleftp" ∷ left_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q2 - 1) ∗
          "Hrightp" ∷ right_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q2) ∗
          "Hrem" ∷ remaining_ptr ↦ rem ∗
          "%Hq2" ∷ ⌜(q2 <= length (c0 :: cs))%nat⌝)%I
          with "[Hp Hdll Hleftp Hrightp remaining]" as "IH".
        { iExists q, idx. iFrame "Hp Hdll Hleftp Hrightp remaining". iPureIntro. exact Hq. }
        wp_for "IH".
        case_bool_decide as Hrem.
        2:{ wp_auto. rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (node_loc (c0 :: cs) (Z.of_nat q2 - 1)) (node_loc (c0 :: cs) q2) q2).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr]. }
            iPureIntro. split_and!; [exact Hq2 | reflexivity | reflexivity]. }
        wp_auto.
        destruct (decide (q2 < length (c0 :: cs))%nat) as [Hq2lt | Hq2ge].
        2:{ have Hnull2 : node_loc (c0 :: cs) q2 = null.
            { rewrite /node_loc decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
            rewrite (bool_decide_eq_true_2 (node_loc (c0 :: cs) q2 = null) Hnull2). simpl negb.
            rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (node_loc (c0 :: cs) (Z.of_nat q2 - 1)) (node_loc (c0 :: cs) q2) q2).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr]. }
            iPureIntro. split_and!; [exact Hq2 | reflexivity | reflexivity]. }
        iDestruct (node_loc_lt_not_null (c0 :: cs) yt.(yjs.yType.start') tl q2 Hq2lt with "Hdll") as "[%Hnn2 Hdll]".
        rewrite (bool_decide_eq_false_2 (node_loc (c0 :: cs) q2 = null) Hnn2). simpl negb.
        rewrite decide_True; [| done].
        destruct ((c0 :: cs) !! q2) as [c2|] eqn:Hc2; [| apply lookup_ge_None in Hc2; lia].
        iDestruct (is_dll_acc (c0 :: cs) yt.(yjs.yType.start') tl q2 c2 Hc2 with "Hdll") as (iv2 olid2 orid2)
          "(%Hc2loc & %Hc2l & %Hc2r & %Hc2id & %Hc2cont & %Hc2olid & %Hc2orid & %Hc2flags & %Hc2contlen & Hc2val & #Hc2ol & #Hc2or & Hback2)".
        have Hcount2 : is_countable_flag iv2 = true := flags_if_countable iv2 (ic_deleted c2) Hc2flags.
        have Hdel2 : is_deleted_flag iv2 = ic_deleted c2 := flags_if_deleted iv2 (ic_deleted c2) Hc2flags.
        iEval (rewrite -Hc2loc) in "Hrightp".
        wp_auto.
        wp_apply (wp_item__Indexable c2.(ic_loc) iv2 Hcount2 with "[$Hc2val]"). iIntros "Hc2val".
        rewrite Hdel2.
        destruct (ic_deleted c2) eqn:Hd2; simpl negb; wp_auto.
        2:{ wp_apply (wp_item__Len c2.(ic_loc) iv2 with "[$Hc2val]"). iIntros "Hc2val".
            rewrite Hc2contlen. wp_auto.
            iDestruct ("Hback2" with "Hc2val") as "Hdll".
            wp_for_post.
            iFrame "HΦ". iExists (S q2), (w64_word_instance.(word.sub) rem (W64 1)).
            iFrame "Hp Hdll Hrem".
            rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
            replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
            rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro. lia. }
        iDestruct ("Hback2" with "Hc2val") as "Hdll".
        wp_for_post.
        iFrame "HΦ". iExists (S q2), rem.
        iFrame "Hp Hdll Hrem".
        rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
        replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
        rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro. lia.
Qed.

End ytype.
