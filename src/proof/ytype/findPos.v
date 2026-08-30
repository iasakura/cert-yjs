(** [wp_yType__findPos]: the tombstone-aware walk to a visible character index,
    returning the straddling neighbours and the in-node offset ([find_pos], over
    an existential list position [p]). Feeds the [Store.Integrate] loop in
    [Text.Insert] and [Text.Delete]; read-only, so stated at a generic [dq].

    Stated over the representation predicates of [ytype/heap.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import model value heap.

(* The [findPos] word-arithmetic proof writes [Z] comparisons unannotated, so fix
   [Z_scope] as the default (matching the environment it was developed in). *)
Local Open Scope Z_scope.

Section ytype.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(** General tombstone-aware [findPos]: walk to the visible character index [idx]
    and return the straddling neighbours plus the in-node offset. The Go walks
    two loops: a skip loop that advances past leading tombstones, then a count
    loop that spends the budget [idx] on visible ([Indexable]) nodes. Deletions
    make the answer a *list* position [p] (the node index, ≥ the visible index
    because tombstones are skipped), so the spec returns an existential [p ≤
    length cells] with the two straddle locations [node_loc cells (p-1)] /
    [node_loc cells p] (which are [null] out of range). When the budget lands
    strictly inside a multi-element run (issue #28) the returned [off] is
    nonzero and measures into the VISIBLE node at [p-1], strictly below its run
    length; [off] = 0 means a node-boundary position. The adjacent
    ([left]/[right]) pair is all the M1 [Insert] / [Delete] callers consume;
    the offset feeds the normalize/split path (M3). *)
Lemma wp_yType__findPos (parent : loc) (dq : dfrac) (cells : list item_cell)
    (arr : list (YjsItem A)) (idx : w64) :
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent dq cells arr }}}
    parent @! (go.PointerType yjs.yType) @! "findPos" #idx
  {{{ (lft rgt : loc) (p : nat) (off : w64), RET (#lft, #rgt, #off);
      own_ytype_cells parent dq cells arr ∗ ⌜find_pos cells p lft rgt off⌝ }}}.
Proof.
  wp_start as "Hyt". iNamed "Hyt".
  iDestruct (own_dll_head_node dq cells _ tl with "Hdll") as %Hhead.
  destruct cells as [|c0 cs].
  - (* empty document: both loops are no-ops, return (null, null, 0) at p = 0 *)
    iDestruct "Hdll" as %[Hs Ht]. wp_auto. rewrite Hs.
    iAssert ("Hp" ∷ parent ↦{dq} yt ∗ "Hl" ∷ left_ptr ↦ null ∗ "Hr" ∷ right_ptr ↦ null ∗ "Hidx" ∷ index_ptr ↦ idx)%I
      with "[Hparent left right index]" as "IH".
    { iFrame. }
    wp_for "IH".
    iAssert ("Hp" ∷ parent ↦{dq} yt ∗ "Hl" ∷ left_ptr ↦ null ∗ "Hr" ∷ right_ptr ↦ null ∗ "Hrem" ∷ remaining_ptr ↦ idx ∗ "Hoff" ∷ offset_ptr ↦ (W64 0))%I
      with "[Hp Hl Hr remaining offset]" as "IH".
    { iFrame. }
    wp_for "IH".
    wp_if_destruct.
    + wp_auto. iApply ("HΦ" $! null null 0%nat (W64 0)). iSplitL "Hp".
      { iExists yt, null. iFrame "Hp". iPureIntro. split_and!; [exact Hs | reflexivity | exact Hlen | exact Hrepr | exact Hcpar]. }
      iPureIntro. split_and!; [lia | rewrite /node_loc; case_decide; reflexivity | rewrite /node_loc; case_decide; reflexivity | by left].
    + iApply ("HΦ" $! null null 0%nat (W64 0)). iSplitL "Hp".
      { iExists yt, null. iFrame "Hp". iPureIntro. split_and!; [exact Hs | reflexivity | exact Hlen | exact Hrepr | exact Hcpar]. }
      iPureIntro. split_and!; [lia | rewrite /node_loc; case_decide; reflexivity | rewrite /node_loc; case_decide; reflexivity | by left].
  - (* non-empty: skip leading tombstones, then count visible nodes to [idx] *)
    wp_auto.
    (* ----- skip loop invariant (runs before [remaining := index]) ----- *)
    iAssert (∃ (q : nat),
      "Hp" ∷ parent ↦{dq} yt ∗
      "Hdll" ∷ own_dll dq parent yt.(yjs.yType.start') tl null null (c0 :: cs) ∗
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
      iDestruct (node_loc_lt_not_null dq (c0 :: cs) yt.(yjs.yType.start') tl q Hqlt with "Hdll") as "[%Hnn Hdll]".
      rewrite (bool_decide_eq_false_2 (node_loc (c0 :: cs) q = null) Hnn). simpl negb.
      destruct ((c0 :: cs) !! q) as [cq|] eqn:Hcq; [| apply lookup_ge_None in Hcq; lia].
      iDestruct (own_dll_acc_node dq (c0 :: cs) yt.(yjs.yType.start') tl q cq Hcq with "Hdll")
        as (prevq nxtq) "(%Hcloc & %Hcl & %Hcrn & %Hrun & %Hclen & %Hpcq & Hnode & Hback)".
      iDestruct "Hnode" as (itemVal olidq oridq)
        "(Hcval & Hcol & Hcor & %Hinl & %Hinr & %Hid & %Hcontent & %Hparq & %Hprevq & %Hnextq & %Hflags)".
      have Hcr : itemVal.(yjs.item.right') = node_loc (c0 :: cs) (Z.of_nat q + 1).
      { rewrite Hnextq. exact Hcrn. }
      iEval (rewrite -Hcloc) in "Hrightp".
      wp_auto.
      wp_apply (wp_item__Deleted cq.(ic_loc) dq itemVal with "[$Hcval]"). iIntros "Hcval".
      rewrite (flags_if_deleted itemVal (ic_deleted cq) Hflags).
      destruct (ic_deleted cq) eqn:Hdq.
      * (* tombstone: advance the cursor, re-establish the skip invariant *)
        rewrite decide_True; [| reflexivity].
        wp_auto.
        iAssert (own_item_node cq.(ic_loc) dq (input_of_run (cell_run cq)) true
                   (ic_parent cq) prevq nxtq) with "[Hcval Hcol Hcor]" as "Hnode".
        { iExists itemVal, olidq, oridq. iFrame "Hcval Hcol Hcor".
          iPureIntro. split_and!;
            [exact Hinl | exact Hinr | exact Hid | exact Hcontent | exact Hparq
            | exact Hprevq | exact Hnextq | (by rewrite Hflags ?Hdq)]. }
        iDestruct ("Hback" with "Hnode") as "Hdll".
        wp_for_post.
        iFrame "HΦ". iExists (S q). iFrame "Hp Hdll Hindex".
        rewrite Hcr. replace (Z.of_nat (S q) - 1)%Z with (Z.of_nat q) by lia.
        replace (Z.of_nat (S q)) with (Z.of_nat q + 1)%Z by lia.
        rewrite Hcloc. iFrame "Hleftp Hrightp". iPureIntro. lia.
      * (* first visible node: skip loop exits, run the count loop from [q] *)
        rewrite decide_False; [| done]. rewrite decide_True; [| done].
        iAssert (own_item_node cq.(ic_loc) dq (input_of_run (cell_run cq)) false
                   (ic_parent cq) prevq nxtq) with "[Hcval Hcol Hcor]" as "Hnode".
        { iExists itemVal, olidq, oridq. iFrame "Hcval Hcol Hcor".
          iPureIntro. split_and!;
            [exact Hinl | exact Hinr | exact Hid | exact Hcontent | exact Hparq
            | exact Hprevq | exact Hnextq | (by rewrite Hflags ?Hdq)]. }
        iDestruct ("Hback" with "Hnode") as "Hdll".
        iEval (rewrite Hcloc) in "Hrightp".
        wp_auto.
        iAssert (∃ (q2 : nat) (rem off : w64),
          "Hp" ∷ parent ↦{dq} yt ∗
          "Hdll" ∷ own_dll dq parent yt.(yjs.yType.start') tl null null (c0 :: cs) ∗
          "Hleftp" ∷ left_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q2 - 1) ∗
          "Hrightp" ∷ right_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q2) ∗
          "Hrem" ∷ remaining_ptr ↦ rem ∗
          "Hoffp" ∷ offset_ptr ↦ off ∗
          "%Hq2" ∷ ⌜(q2 <= length (c0 :: cs))%nat⌝ ∗
          "%Hoffinv" ∷ ⌜off = W64 0 ∨
             (0 < uint.Z off)%Z ∧ rem = W64 0 ∧ (1 <= q2)%nat ∧
             (∃ c, (c0 :: cs) !! (q2 - 1)%nat = Some c ∧ ic_deleted c = false ∧
                   (uint.nat off < length (ic_run c))%nat)⌝)%I
          with "[Hp Hdll Hleftp Hrightp remaining offset]" as "IH".
        { iExists q, idx, (W64 0). iFrame "Hp Hdll Hleftp Hrightp remaining offset".
          iPureIntro. split; [exact Hq | by left]. }
        wp_for "IH".
        case_bool_decide as Hrem.
        2:{ wp_auto. rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (node_loc (c0 :: cs) (Z.of_nat q2 - 1)) (node_loc (c0 :: cs) q2) q2 off).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar]. }
            iPureIntro. split_and!; [exact Hq2 | reflexivity | reflexivity |].
            destruct Hoffinv as [-> | (Hpos & _ & Hq21 & Hc)]; [by left | right; exact (conj Hpos (conj Hq21 Hc))]. }
        wp_auto.
        have Hoff0 : off = W64 0.
        { destruct Hoffinv as [-> | (_ & Hrem0 & _)]; [done | exfalso; rewrite Hrem0 in Hrem; word]. }
        subst off.
        destruct (decide (q2 < length (c0 :: cs))%nat) as [Hq2lt | Hq2ge].
        2:{ have Hnull2 : node_loc (c0 :: cs) q2 = null.
            { rewrite /node_loc decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
            rewrite (bool_decide_eq_true_2 (node_loc (c0 :: cs) q2 = null) Hnull2). simpl negb.
            rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (node_loc (c0 :: cs) (Z.of_nat q2 - 1)) (node_loc (c0 :: cs) q2) q2 (W64 0)).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar]. }
            iPureIntro. split_and!; [exact Hq2 | reflexivity | reflexivity | by left]. }
        iDestruct (node_loc_lt_not_null dq (c0 :: cs) yt.(yjs.yType.start') tl q2 Hq2lt with "Hdll") as "[%Hnn2 Hdll]".
        rewrite (bool_decide_eq_false_2 (node_loc (c0 :: cs) q2 = null) Hnn2). simpl negb.
        rewrite decide_True; [| done].
        destruct ((c0 :: cs) !! q2) as [c2|] eqn:Hc2; [| apply lookup_ge_None in Hc2; lia].
        iDestruct (own_dll_acc_node dq (c0 :: cs) yt.(yjs.yType.start') tl q2 c2 Hc2 with "Hdll")
          as (prev2 nxt2) "(%Hc2loc & %Hc2l & %Hc2rn & %Hc2run & %Hc2len & %Hpc2 & Hnode2 & Hback2)".
        iDestruct "Hnode2" as (iv2 olid2 orid2)
          "(Hc2val & Hc2ol & Hc2or & %Hc2inl & %Hc2inr & %Hc2id & %Hc2cont & %Hc2par & %Hc2prev & %Hc2next & %Hc2flags)".
        have Hcount2 : is_countable_flag iv2 = true := flags_if_countable iv2 (ic_deleted c2) Hc2flags.
        have Hdel2 : is_deleted_flag iv2 = ic_deleted c2 := flags_if_deleted iv2 (ic_deleted c2) Hc2flags.
        have Hc2r : iv2.(yjs.item.right') = node_loc (c0 :: cs) (Z.of_nat q2 + 1).
        { rewrite Hc2next. exact Hc2rn. }
        iEval (rewrite -Hc2loc) in "Hrightp".
        wp_auto.
        wp_apply (wp_item__Indexable c2.(ic_loc) dq iv2 Hcount2 with "[$Hc2val]"). iIntros "Hc2val".
        rewrite Hdel2.
        destruct (ic_deleted c2) eqn:Hd2; simpl negb; wp_auto.
        2:{ (* visible node: spend the budget, or record the in-run offset *)
            wp_apply (wp_item__Len c2.(ic_loc) dq iv2 with "[$Hc2val]"). iIntros "Hc2val".
            wp_auto.
            case_bool_decide as Hcmp; wp_auto.
            - (* remaining < Len: the index lands inside this run (issue #28) *)
              iAssert (own_item_node c2.(ic_loc) dq (input_of_run (cell_run c2)) false
                         (ic_parent c2) prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
              { iExists iv2, olid2, orid2. iFrame "Hc2val Hc2ol Hc2or".
                iPureIntro. split_and!;
                  [exact Hc2inl | exact Hc2inr | exact Hc2id | exact Hc2cont | exact Hc2par
                  | exact Hc2prev | exact Hc2next | (by rewrite Hc2flags ?Hd2)]. }
              iDestruct ("Hback2" with "Hnode2") as "Hdll".
              wp_for_post.
              iFrame "HΦ". iExists (S q2), (W64 0), rem.
              iFrame "Hp Hdll Hrem Hoffp".
              rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
              replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
              rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro.
              have Hrlen : length (ic_run c2) = length (iv2.(yjs.item.content').(yjs.content.content')).
              { have Hstr : iv2.(yjs.item.content').(yjs.content.content')
                          = in_content (input_of_run (cell_run c2)) := Hc2cont.
                rewrite Hstr. symmetry. exact Hc2len. }
              split; [lia |]. right.
              split_and!; [word | done | lia |].
              exists c2. replace (S q2 - 1)%nat with q2 by lia.
              split_and!; [exact Hc2 | exact Hd2 | rewrite Hrlen; word].
            - (* Len <= remaining: spend the whole node (the else branch
                 re-reads right.Len(), a second method call) *)
              wp_apply (wp_item__Len c2.(ic_loc) dq iv2 with "[$Hc2val]"). iIntros "Hc2val".
              wp_auto.
              iAssert (own_item_node c2.(ic_loc) dq (input_of_run (cell_run c2)) false
                         (ic_parent c2) prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
              { iExists iv2, olid2, orid2. iFrame "Hc2val Hc2ol Hc2or".
                iPureIntro. split_and!;
                  [exact Hc2inl | exact Hc2inr | exact Hc2id | exact Hc2cont | exact Hc2par
                  | exact Hc2prev | exact Hc2next | (by rewrite Hc2flags ?Hd2)]. }
              iDestruct ("Hback2" with "Hnode2") as "Hdll".
              wp_for_post.
              iFrame "HΦ".
              iExists (S q2), (w64_word_instance.(word.sub) rem (W64 (length (iv2.(yjs.item.content').(yjs.content.content'))))), (W64 0).
              iFrame "Hp Hdll Hrem Hoffp".
              rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
              replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
              rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro. split; [lia | by left]. }
        iAssert (own_item_node c2.(ic_loc) dq (input_of_run (cell_run c2)) true
                   (ic_parent c2) prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
        { iExists iv2, olid2, orid2. iFrame "Hc2val Hc2ol Hc2or".
          iPureIntro. split_and!;
            [exact Hc2inl | exact Hc2inr | exact Hc2id | exact Hc2cont | exact Hc2par
            | exact Hc2prev | exact Hc2next | (by rewrite Hc2flags ?Hd2)]. }
        iDestruct ("Hback2" with "Hnode2") as "Hdll".
        wp_for_post.
        iFrame "HΦ". iExists (S q2), rem, (W64 0).
        iFrame "Hp Hdll Hrem Hoffp".
        rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
        replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
        rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro. split; [lia | by left].
    + (* right = null (q = length): skip loop exits, count loop exits at once *)
      have Hnull : node_loc (c0 :: cs) q = null.
      { rewrite /node_loc decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
      rewrite (bool_decide_eq_true_2 (node_loc (c0 :: cs) q = null) Hnull). simpl negb.
      wp_auto.
      rewrite decide_False; [| done]. rewrite decide_True; [| done].
      wp_auto.
        iAssert (∃ (q2 : nat) (rem off : w64),
          "Hp" ∷ parent ↦{dq} yt ∗
          "Hdll" ∷ own_dll dq parent yt.(yjs.yType.start') tl null null (c0 :: cs) ∗
          "Hleftp" ∷ left_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q2 - 1) ∗
          "Hrightp" ∷ right_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q2) ∗
          "Hrem" ∷ remaining_ptr ↦ rem ∗
          "Hoffp" ∷ offset_ptr ↦ off ∗
          "%Hq2" ∷ ⌜(q2 <= length (c0 :: cs))%nat⌝ ∗
          "%Hoffinv" ∷ ⌜off = W64 0 ∨
             (0 < uint.Z off)%Z ∧ rem = W64 0 ∧ (1 <= q2)%nat ∧
             (∃ c, (c0 :: cs) !! (q2 - 1)%nat = Some c ∧ ic_deleted c = false ∧
                   (uint.nat off < length (ic_run c))%nat)⌝)%I
          with "[Hp Hdll Hleftp Hrightp remaining offset]" as "IH".
        { iExists q, idx, (W64 0). iFrame "Hp Hdll Hleftp Hrightp remaining offset".
          iPureIntro. split; [exact Hq | by left]. }
        wp_for "IH".
        case_bool_decide as Hrem.
        2:{ wp_auto. rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (node_loc (c0 :: cs) (Z.of_nat q2 - 1)) (node_loc (c0 :: cs) q2) q2 off).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar]. }
            iPureIntro. split_and!; [exact Hq2 | reflexivity | reflexivity |].
            destruct Hoffinv as [-> | (Hpos & _ & Hq21 & Hc)]; [by left | right; exact (conj Hpos (conj Hq21 Hc))]. }
        wp_auto.
        have Hoff0 : off = W64 0.
        { destruct Hoffinv as [-> | (_ & Hrem0 & _)]; [done | exfalso; rewrite Hrem0 in Hrem; word]. }
        subst off.
        destruct (decide (q2 < length (c0 :: cs))%nat) as [Hq2lt | Hq2ge].
        2:{ have Hnull2 : node_loc (c0 :: cs) q2 = null.
            { rewrite /node_loc decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
            rewrite (bool_decide_eq_true_2 (node_loc (c0 :: cs) q2 = null) Hnull2). simpl negb.
            rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (node_loc (c0 :: cs) (Z.of_nat q2 - 1)) (node_loc (c0 :: cs) q2) q2 (W64 0)).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar]. }
            iPureIntro. split_and!; [exact Hq2 | reflexivity | reflexivity | by left]. }
        iDestruct (node_loc_lt_not_null dq (c0 :: cs) yt.(yjs.yType.start') tl q2 Hq2lt with "Hdll") as "[%Hnn2 Hdll]".
        rewrite (bool_decide_eq_false_2 (node_loc (c0 :: cs) q2 = null) Hnn2). simpl negb.
        rewrite decide_True; [| done].
        destruct ((c0 :: cs) !! q2) as [c2|] eqn:Hc2; [| apply lookup_ge_None in Hc2; lia].
        iDestruct (own_dll_acc_node dq (c0 :: cs) yt.(yjs.yType.start') tl q2 c2 Hc2 with "Hdll")
          as (prev2 nxt2) "(%Hc2loc & %Hc2l & %Hc2rn & %Hc2run & %Hc2len & %Hpc2 & Hnode2 & Hback2)".
        iDestruct "Hnode2" as (iv2 olid2 orid2)
          "(Hc2val & Hc2ol & Hc2or & %Hc2inl & %Hc2inr & %Hc2id & %Hc2cont & %Hc2par & %Hc2prev & %Hc2next & %Hc2flags)".
        have Hcount2 : is_countable_flag iv2 = true := flags_if_countable iv2 (ic_deleted c2) Hc2flags.
        have Hdel2 : is_deleted_flag iv2 = ic_deleted c2 := flags_if_deleted iv2 (ic_deleted c2) Hc2flags.
        have Hc2r : iv2.(yjs.item.right') = node_loc (c0 :: cs) (Z.of_nat q2 + 1).
        { rewrite Hc2next. exact Hc2rn. }
        iEval (rewrite -Hc2loc) in "Hrightp".
        wp_auto.
        wp_apply (wp_item__Indexable c2.(ic_loc) dq iv2 Hcount2 with "[$Hc2val]"). iIntros "Hc2val".
        rewrite Hdel2.
        destruct (ic_deleted c2) eqn:Hd2; simpl negb; wp_auto.
        2:{ (* visible node: spend the budget, or record the in-run offset *)
            wp_apply (wp_item__Len c2.(ic_loc) dq iv2 with "[$Hc2val]"). iIntros "Hc2val".
            wp_auto.
            case_bool_decide as Hcmp; wp_auto.
            - (* remaining < Len: the index lands inside this run (issue #28) *)
              iAssert (own_item_node c2.(ic_loc) dq (input_of_run (cell_run c2)) false
                         (ic_parent c2) prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
              { iExists iv2, olid2, orid2. iFrame "Hc2val Hc2ol Hc2or".
                iPureIntro. split_and!;
                  [exact Hc2inl | exact Hc2inr | exact Hc2id | exact Hc2cont | exact Hc2par
                  | exact Hc2prev | exact Hc2next | (by rewrite Hc2flags ?Hd2)]. }
              iDestruct ("Hback2" with "Hnode2") as "Hdll".
              wp_for_post.
              iFrame "HΦ". iExists (S q2), (W64 0), rem.
              iFrame "Hp Hdll Hrem Hoffp".
              rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
              replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
              rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro.
              have Hrlen : length (ic_run c2) = length (iv2.(yjs.item.content').(yjs.content.content')).
              { have Hstr : iv2.(yjs.item.content').(yjs.content.content')
                          = in_content (input_of_run (cell_run c2)) := Hc2cont.
                rewrite Hstr. symmetry. exact Hc2len. }
              split; [lia |]. right.
              split_and!; [word | done | lia |].
              exists c2. replace (S q2 - 1)%nat with q2 by lia.
              split_and!; [exact Hc2 | exact Hd2 | rewrite Hrlen; word].
            - (* Len <= remaining: spend the whole node (the else branch
                 re-reads right.Len(), a second method call) *)
              wp_apply (wp_item__Len c2.(ic_loc) dq iv2 with "[$Hc2val]"). iIntros "Hc2val".
              wp_auto.
              iAssert (own_item_node c2.(ic_loc) dq (input_of_run (cell_run c2)) false
                         (ic_parent c2) prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
              { iExists iv2, olid2, orid2. iFrame "Hc2val Hc2ol Hc2or".
                iPureIntro. split_and!;
                  [exact Hc2inl | exact Hc2inr | exact Hc2id | exact Hc2cont | exact Hc2par
                  | exact Hc2prev | exact Hc2next | (by rewrite Hc2flags ?Hd2)]. }
              iDestruct ("Hback2" with "Hnode2") as "Hdll".
              wp_for_post.
              iFrame "HΦ".
              iExists (S q2), (w64_word_instance.(word.sub) rem (W64 (length (iv2.(yjs.item.content').(yjs.content.content'))))), (W64 0).
              iFrame "Hp Hdll Hrem Hoffp".
              rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
              replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
              rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro. split; [lia | by left]. }
        iAssert (own_item_node c2.(ic_loc) dq (input_of_run (cell_run c2)) true
                   (ic_parent c2) prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
        { iExists iv2, olid2, orid2. iFrame "Hc2val Hc2ol Hc2or".
          iPureIntro. split_and!;
            [exact Hc2inl | exact Hc2inr | exact Hc2id | exact Hc2cont | exact Hc2par
            | exact Hc2prev | exact Hc2next | (by rewrite Hc2flags ?Hd2)]. }
        iDestruct ("Hback2" with "Hnode2") as "Hdll".
        wp_for_post.
        iFrame "HΦ". iExists (S q2), rem, (W64 0).
        iFrame "Hp Hdll Hrem Hoffp".
        rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
        replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
        rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro. split; [lia | by left].
Qed.

End ytype.
