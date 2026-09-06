(** [wp_yType__findPos]: the tombstone-aware walk to a visible character index,
    returning the straddling neighbours and the in-node offset
    ([find_pos], over an existential run position [p]). Feeds the [Store.Integrate] loop in
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
    make the answer a *list* position [p] (the run index, at least the visible
    index because tombstones are skipped), so the spec returns an existential
    [p <= length runs] with the two straddle addresses [loc_at ls (p-1)] /
    [loc_at ls p] (which are [null] out of range). When the budget lands
    strictly inside a multi-element run (issue #28) the returned [off] is
    nonzero and measures into the VISIBLE run at [p-1], strictly below its
    length; [off] = 0 means a node-boundary position. The adjacent
    ([left]/[right]) pair is all the M1 [Insert] / [Delete] callers consume;
    the offset feeds the normalize/split path (M3). *)
Lemma wp_yType__findPos (parent : loc) (dq : dfrac) (ls : list loc)
    (tm : type_model) (idx : w64) :
  {{{ is_pkg_init yjs ∗ own_ytype parent dq ls tm }}}
    parent @! (go.PointerType yjs.yType) @! "findPos" #idx
  {{{ (leftNode rightNode : loc) (p : nat) (off : w64), RET (#leftNode, #rightNode, #off);
      own_ytype parent dq ls tm ∗ ⌜find_pos ls (tm_runs tm) p leftNode rightNode off⌝ }}}.
Proof.
  wp_start as "Hyt".
  destruct tm as [runs]. simpl.
  iNamed "Hyt".
  iDestruct (own_dll_length with "Hdll") as %Hlenls.
  iDestruct (own_dll_headptr with "Hdll") as "[%Hhead Hdll]".
  destruct ls as [|l0 ls']; destruct runs as [|r0 rs'];
    [| by iDestruct "Hdll" as %[] | by iDestruct "Hdll" as %[] |].
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
      { iExists yt, null. iFrame "Hp". iPureIntro. split_and!; [exact Hs | reflexivity | exact Hlen]. }
      iPureIntro. split_and!; [lia | rewrite /loc_at; case_decide; reflexivity | rewrite /loc_at; case_decide; reflexivity | by left].
    + iApply ("HΦ" $! null null 0%nat (W64 0)). iSplitL "Hp".
      { iExists yt, null. iFrame "Hp". iPureIntro. split_and!; [exact Hs | reflexivity | exact Hlen]. }
      iPureIntro. split_and!; [lia | rewrite /loc_at; case_decide; reflexivity | rewrite /loc_at; case_decide; reflexivity | by left].
  - (* non-empty: skip leading tombstones, then count visible nodes to [idx] *)
    wp_auto.
    (* ----- skip loop invariant (runs before [remaining := index]) ----- *)
    iAssert (∃ (q : nat),
      "Hp" ∷ parent ↦{dq} yt ∗
      "Hdll" ∷ own_dll dq parent yt.(yjs.yType.start') tl null null (l0 :: ls') (r0 :: rs') ∗
      "Hindex" ∷ index_ptr ↦ idx ∗
      "Hleftp" ∷ left_ptr ↦ loc_at (l0 :: ls') (Z.of_nat q - 1) ∗
      "Hrightp" ∷ right_ptr ↦ loc_at (l0 :: ls') (Z.of_nat q) ∗
      "%Hq" ∷ ⌜(q <= length (l0 :: ls'))%nat⌝)%I
      with "[Hparent Hdll index left right]" as "IH".
    { iExists 0%nat. iFrame "Hparent Hdll index".
      replace (Z.of_nat 0 - 1)%Z with (-1)%Z by lia.
      have Hm1 : loc_at (l0 :: ls') (-1)%Z = null by (rewrite /loc_at; case_decide; [lia | done]).
      rewrite Hm1. iFrame "left".
      have Hr0 : loc_at (l0 :: ls') (Z.of_nat 0) = yt.(yjs.yType.start') by rewrite Hhead.
      rewrite Hr0. iFrame "right". iPureIntro. simpl; lia. }
    wp_for "IH".
    iDestruct (own_dll_length with "Hdll") as %Hlenl.
    destruct (decide (q < length (l0 :: ls'))%nat) as [Hqlt | Hqge].
    + (* right ≠ null: evaluate Deleted; tombstone ⇒ advance, else exit to count *)
      iDestruct (loc_at_lt_not_null dq parent yt.(yjs.yType.start') tl (l0 :: ls') (r0 :: rs') q Hqlt with "Hdll") as "[%Hnn Hdll]".
      rewrite (bool_decide_eq_false_2 (loc_at (l0 :: ls') q = null) Hnn). simpl negb.
      destruct ((l0 :: ls') !! q) as [lq|] eqn:Hlq; [| apply lookup_ge_None in Hlq; lia].
      destruct ((r0 :: rs') !! q) as [rq|] eqn:Hrq; [| apply lookup_ge_None in Hrq; lia].
      iDestruct (own_dll_acc dq parent yt.(yjs.yType.start') tl (l0 :: ls') (r0 :: rs') q lq rq Hlq Hrq with "Hdll")
        as (prevq nxtq) "(%Hcl & %Hcrn & %Hrun & %Hpcq & %Hclen & Hnode & Hback)".
      have Hcloc : lq = loc_at (l0 :: ls') (Z.of_nat q).
      { rewrite /loc_at decide_True; last lia. rewrite Nat2Z.id Hlq //. }
      iDestruct "Hnode" as (itemVal olidq oridq)
        "(Hcval & Hcol & Hcor & %Hinl & %Hinr & %Hid & %Hcontent & %Hparq & %Hprevq & %Hnextq & %Hflags)".
      have Hcr : itemVal.(yjs.item.right') = loc_at (l0 :: ls') (Z.of_nat q + 1).
      { rewrite Hnextq. exact Hcrn. }
      iEval (rewrite -Hcloc) in "Hrightp".
      wp_auto.
      wp_apply (wp_item__Deleted lq dq itemVal with "[$Hcval]"). iIntros "Hcval".
      rewrite (flags_if_deleted itemVal (run_deleted rq) Hflags).
      destruct (run_deleted rq) eqn:Hdq.
      * (* tombstone: advance the cursor, re-establish the skip invariant *)
        rewrite decide_True; [| reflexivity].
        wp_auto.
        iAssert (own_item_node lq dq (input_of_run rq) true
                   parent prevq nxtq) with "[Hcval Hcol Hcor]" as "Hnode".
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
        iAssert (own_item_node lq dq (input_of_run rq) false
                   parent prevq nxtq) with "[Hcval Hcol Hcor]" as "Hnode".
        { iExists itemVal, olidq, oridq. iFrame "Hcval Hcol Hcor".
          iPureIntro. split_and!;
            [exact Hinl | exact Hinr | exact Hid | exact Hcontent | exact Hparq
            | exact Hprevq | exact Hnextq | (by rewrite Hflags ?Hdq)]. }
        iDestruct ("Hback" with "Hnode") as "Hdll".
        iEval (rewrite Hcloc) in "Hrightp".
        wp_auto.
        iAssert (∃ (q2 : nat) (rem off : w64),
          "Hp" ∷ parent ↦{dq} yt ∗
          "Hdll" ∷ own_dll dq parent yt.(yjs.yType.start') tl null null (l0 :: ls') (r0 :: rs') ∗
          "Hleftp" ∷ left_ptr ↦ loc_at (l0 :: ls') (Z.of_nat q2 - 1) ∗
          "Hrightp" ∷ right_ptr ↦ loc_at (l0 :: ls') (Z.of_nat q2) ∗
          "Hrem" ∷ remaining_ptr ↦ rem ∗
          "Hoffp" ∷ offset_ptr ↦ off ∗
          "%Hq2" ∷ ⌜(q2 <= length (l0 :: ls'))%nat⌝ ∗
          "%Hoffinv" ∷ ⌜off = W64 0 ∨
             (0 < uint.Z off)%Z ∧ rem = W64 0 ∧ (1 <= q2)%nat ∧
             (∃ r, (r0 :: rs') !! (q2 - 1)%nat = Some r ∧ run_deleted r = false ∧
                   (uint.nat off < length (run_items r))%nat)⌝)%I
          with "[Hp Hdll Hleftp Hrightp remaining offset]" as "IH".
        { iExists q, idx, (W64 0). iFrame "Hp Hdll Hleftp Hrightp remaining offset".
          iPureIntro. split; [exact Hq | by left]. }
        wp_for "IH".
        iDestruct (own_dll_length with "Hdll") as %Hlenl2.
        case_bool_decide as Hrem.
        2:{ wp_auto. rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (loc_at (l0 :: ls') (Z.of_nat q2 - 1)) (loc_at (l0 :: ls') q2) q2 off).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. exact Hlen. }
            iPureIntro. split_and!; [lia | reflexivity | reflexivity |].
            destruct Hoffinv as [-> | (Hpos & _ & Hq21 & Hc)]; [by left | right; exact (conj Hpos (conj Hq21 Hc))]. }
        wp_auto.
        have Hoff0 : off = W64 0.
        { destruct Hoffinv as [-> | (_ & Hrem0 & _)]; [done | exfalso; rewrite Hrem0 in Hrem; word]. }
        subst off.
        destruct (decide (q2 < length (l0 :: ls'))%nat) as [Hq2lt | Hq2ge].
        2:{ have Hnull2 : loc_at (l0 :: ls') q2 = null.
            { rewrite /loc_at decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
            rewrite (bool_decide_eq_true_2 (loc_at (l0 :: ls') q2 = null) Hnull2). simpl negb.
            rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (loc_at (l0 :: ls') (Z.of_nat q2 - 1)) (loc_at (l0 :: ls') q2) q2 (W64 0)).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. exact Hlen. }
            iPureIntro. split_and!; [lia | reflexivity | reflexivity | by left]. }
        iDestruct (loc_at_lt_not_null dq parent yt.(yjs.yType.start') tl (l0 :: ls') (r0 :: rs') q2 Hq2lt with "Hdll") as "[%Hnn2 Hdll]".
        rewrite (bool_decide_eq_false_2 (loc_at (l0 :: ls') q2 = null) Hnn2). simpl negb.
        rewrite decide_True; [| done].
        destruct ((l0 :: ls') !! q2) as [l2|] eqn:Hl2; [| apply lookup_ge_None in Hl2; lia].
        destruct ((r0 :: rs') !! q2) as [r2|] eqn:Hr2; [| apply lookup_ge_None in Hr2; lia].
        iDestruct (own_dll_acc dq parent yt.(yjs.yType.start') tl (l0 :: ls') (r0 :: rs') q2 l2 r2 Hl2 Hr2 with "Hdll")
          as (prev2 nxt2) "(%Hc2l & %Hc2rn & %Hc2run & %Hpc2 & %Hc2len & Hnode2 & Hback2)".
        have Hc2loc : l2 = loc_at (l0 :: ls') (Z.of_nat q2).
        { rewrite /loc_at decide_True; last lia. rewrite Nat2Z.id Hl2 //. }
        iDestruct "Hnode2" as (iv2 olid2 orid2)
          "(Hc2val & Hc2ol & Hc2or & %Hc2inl & %Hc2inr & %Hc2id & %Hc2cont & %Hc2par & %Hc2prev & %Hc2next & %Hc2flags)".
        have Hcount2 : is_countable_flag iv2 = true := flags_if_countable iv2 (run_deleted r2) Hc2flags.
        have Hdel2 : is_deleted_flag iv2 = run_deleted r2 := flags_if_deleted iv2 (run_deleted r2) Hc2flags.
        have Hc2r : iv2.(yjs.item.right') = loc_at (l0 :: ls') (Z.of_nat q2 + 1).
        { rewrite Hc2next. exact Hc2rn. }
        iEval (rewrite -Hc2loc) in "Hrightp".
        wp_auto.
        wp_apply (wp_item__Indexable l2 dq iv2 Hcount2 with "[$Hc2val]"). iIntros "Hc2val".
        rewrite Hdel2.
        destruct (run_deleted r2) eqn:Hd2; simpl negb; wp_auto.
        2:{ (* visible node: spend the budget, or record the in-run offset *)
            wp_apply (wp_item__Len l2 dq iv2 with "[$Hc2val]"). iIntros "Hc2val".
            wp_auto.
            case_bool_decide as Hcmp; wp_auto.
            - (* remaining < Len: the index lands inside this run (issue #28) *)
              iAssert (own_item_node l2 dq (input_of_run r2) false
                         parent prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
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
              have Hrlen : length (run_items r2) = length (iv2.(yjs.item.content').(yjs.content.content')).
              { have Hstr : iv2.(yjs.item.content').(yjs.content.content')
                          = in_content (input_of_run r2) := Hc2cont.
                rewrite Hstr. symmetry. exact Hc2len. }
              split; [lia |]. right.
              split_and!; [word | done | lia |].
              exists r2. replace (S q2 - 1)%nat with q2 by lia.
              split_and!; [exact Hr2 | exact Hd2 | rewrite Hrlen; word].
            - (* Len <= remaining: spend the whole node (the else branch
                 re-reads right.Len(), a second method call) *)
              wp_apply (wp_item__Len l2 dq iv2 with "[$Hc2val]"). iIntros "Hc2val".
              wp_auto.
              iAssert (own_item_node l2 dq (input_of_run r2) false
                         parent prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
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
        iAssert (own_item_node l2 dq (input_of_run r2) true
                   parent prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
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
      have Hnull : loc_at (l0 :: ls') q = null.
      { rewrite /loc_at decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
      rewrite (bool_decide_eq_true_2 (loc_at (l0 :: ls') q = null) Hnull). simpl negb.
      wp_auto.
      rewrite decide_False; [| done]. rewrite decide_True; [| done].
      wp_auto.
        iAssert (∃ (q2 : nat) (rem off : w64),
          "Hp" ∷ parent ↦{dq} yt ∗
          "Hdll" ∷ own_dll dq parent yt.(yjs.yType.start') tl null null (l0 :: ls') (r0 :: rs') ∗
          "Hleftp" ∷ left_ptr ↦ loc_at (l0 :: ls') (Z.of_nat q2 - 1) ∗
          "Hrightp" ∷ right_ptr ↦ loc_at (l0 :: ls') (Z.of_nat q2) ∗
          "Hrem" ∷ remaining_ptr ↦ rem ∗
          "Hoffp" ∷ offset_ptr ↦ off ∗
          "%Hq2" ∷ ⌜(q2 <= length (l0 :: ls'))%nat⌝ ∗
          "%Hoffinv" ∷ ⌜off = W64 0 ∨
             (0 < uint.Z off)%Z ∧ rem = W64 0 ∧ (1 <= q2)%nat ∧
             (∃ r, (r0 :: rs') !! (q2 - 1)%nat = Some r ∧ run_deleted r = false ∧
                   (uint.nat off < length (run_items r))%nat)⌝)%I
          with "[Hp Hdll Hleftp Hrightp remaining offset]" as "IH".
        { iExists q, idx, (W64 0). iFrame "Hp Hdll Hleftp Hrightp remaining offset".
          iPureIntro. split; [exact Hq | by left]. }
        wp_for "IH".
        iDestruct (own_dll_length with "Hdll") as %Hlenl2.
        case_bool_decide as Hrem.
        2:{ wp_auto. rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (loc_at (l0 :: ls') (Z.of_nat q2 - 1)) (loc_at (l0 :: ls') q2) q2 off).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. exact Hlen. }
            iPureIntro. split_and!; [lia | reflexivity | reflexivity |].
            destruct Hoffinv as [-> | (Hpos & _ & Hq21 & Hc)]; [by left | right; exact (conj Hpos (conj Hq21 Hc))]. }
        wp_auto.
        have Hoff0 : off = W64 0.
        { destruct Hoffinv as [-> | (_ & Hrem0 & _)]; [done | exfalso; rewrite Hrem0 in Hrem; word]. }
        subst off.
        destruct (decide (q2 < length (l0 :: ls'))%nat) as [Hq2lt | Hq2ge].
        2:{ have Hnull2 : loc_at (l0 :: ls') q2 = null.
            { rewrite /loc_at decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
            rewrite (bool_decide_eq_true_2 (loc_at (l0 :: ls') q2 = null) Hnull2). simpl negb.
            rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (loc_at (l0 :: ls') (Z.of_nat q2 - 1)) (loc_at (l0 :: ls') q2) q2 (W64 0)).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. exact Hlen. }
            iPureIntro. split_and!; [lia | reflexivity | reflexivity | by left]. }
        iDestruct (loc_at_lt_not_null dq parent yt.(yjs.yType.start') tl (l0 :: ls') (r0 :: rs') q2 Hq2lt with "Hdll") as "[%Hnn2 Hdll]".
        rewrite (bool_decide_eq_false_2 (loc_at (l0 :: ls') q2 = null) Hnn2). simpl negb.
        rewrite decide_True; [| done].
        destruct ((l0 :: ls') !! q2) as [l2|] eqn:Hl2; [| apply lookup_ge_None in Hl2; lia].
        destruct ((r0 :: rs') !! q2) as [r2|] eqn:Hr2; [| apply lookup_ge_None in Hr2; lia].
        iDestruct (own_dll_acc dq parent yt.(yjs.yType.start') tl (l0 :: ls') (r0 :: rs') q2 l2 r2 Hl2 Hr2 with "Hdll")
          as (prev2 nxt2) "(%Hc2l & %Hc2rn & %Hc2run & %Hpc2 & %Hc2len & Hnode2 & Hback2)".
        have Hc2loc : l2 = loc_at (l0 :: ls') (Z.of_nat q2).
        { rewrite /loc_at decide_True; last lia. rewrite Nat2Z.id Hl2 //. }
        iDestruct "Hnode2" as (iv2 olid2 orid2)
          "(Hc2val & Hc2ol & Hc2or & %Hc2inl & %Hc2inr & %Hc2id & %Hc2cont & %Hc2par & %Hc2prev & %Hc2next & %Hc2flags)".
        have Hcount2 : is_countable_flag iv2 = true := flags_if_countable iv2 (run_deleted r2) Hc2flags.
        have Hdel2 : is_deleted_flag iv2 = run_deleted r2 := flags_if_deleted iv2 (run_deleted r2) Hc2flags.
        have Hc2r : iv2.(yjs.item.right') = loc_at (l0 :: ls') (Z.of_nat q2 + 1).
        { rewrite Hc2next. exact Hc2rn. }
        iEval (rewrite -Hc2loc) in "Hrightp".
        wp_auto.
        wp_apply (wp_item__Indexable l2 dq iv2 Hcount2 with "[$Hc2val]"). iIntros "Hc2val".
        rewrite Hdel2.
        destruct (run_deleted r2) eqn:Hd2; simpl negb; wp_auto.
        2:{ (* visible node: spend the budget, or record the in-run offset *)
            wp_apply (wp_item__Len l2 dq iv2 with "[$Hc2val]"). iIntros "Hc2val".
            wp_auto.
            case_bool_decide as Hcmp; wp_auto.
            - (* remaining < Len: the index lands inside this run (issue #28) *)
              iAssert (own_item_node l2 dq (input_of_run r2) false
                         parent prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
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
              have Hrlen : length (run_items r2) = length (iv2.(yjs.item.content').(yjs.content.content')).
              { have Hstr : iv2.(yjs.item.content').(yjs.content.content')
                          = in_content (input_of_run r2) := Hc2cont.
                rewrite Hstr. symmetry. exact Hc2len. }
              split; [lia |]. right.
              split_and!; [word | done | lia |].
              exists r2. replace (S q2 - 1)%nat with q2 by lia.
              split_and!; [exact Hr2 | exact Hd2 | rewrite Hrlen; word].
            - (* Len <= remaining: spend the whole node (the else branch
                 re-reads right.Len(), a second method call) *)
              wp_apply (wp_item__Len l2 dq iv2 with "[$Hc2val]"). iIntros "Hc2val".
              wp_auto.
              iAssert (own_item_node l2 dq (input_of_run r2) false
                         parent prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
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
        iAssert (own_item_node l2 dq (input_of_run r2) true
                   parent prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
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
