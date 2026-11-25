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

Notation A := (list w16).

(** General tombstone-aware [findPos]: walk to the visible character index [idx]
    and return the straddling neighbours plus the in-node offset. The Go walks
    one loop, from the head of the list, that spends the budget [idx] on
    visible ([Indexable]) nodes and passes the tombstones on its way.
    Deletions make the answer a *list* position [p] (the run index, at least
    the visible index because tombstones are passed), so the spec returns an
    existential [p <= length runs] with the two straddle addresses
    [loc_at ls (p-1)] / [loc_at ls p] (which are [null] out of range). When
    the budget lands strictly inside a multi-element run (issue #28) the
    returned [off] is nonzero and measures into the VISIBLE run at [p-1],
    strictly below its length; [off] = 0 means a node-boundary position. The
    adjacent ([left]/[right]) pair is all the [Insert] / [Delete] callers
    consume; the offset feeds their split. *)
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
  wp_auto.
  (* the count loop: the cursor [q2] walks right from the head, spending the
     budget on visible runs *)
  iAssert (∃ (q2 : nat) (rem off : w64),
    "Hp" ∷ parent ↦{dq} yt ∗
    "Hdll" ∷ own_dll dq parent yt.(yjs.yType.start') tl null null ls runs ∗
    "Hleftp" ∷ left_ptr ↦ loc_at ls (Z.of_nat q2 - 1) ∗
    "Hrightp" ∷ right_ptr ↦ loc_at ls (Z.of_nat q2) ∗
    "Hrem" ∷ remaining_ptr ↦ rem ∗
    "Hoffp" ∷ offset_ptr ↦ off ∗
    "%Hq2" ∷ ⌜(q2 <= length ls)%nat⌝ ∗
    "%Hoffinv" ∷ ⌜off = W64 0 ∨
       (0 < uint.Z off)%Z ∧ rem = W64 0 ∧ (1 <= q2)%nat ∧
       (∃ r, runs !! (q2 - 1)%nat = Some r ∧ run_deleted r = false ∧
             (uint.nat off < length (run_items r))%nat)⌝)%I
    with "[Hparent Hdll left right remaining offset]" as "IH".
  { iExists 0%nat, idx, (W64 0). iFrame "Hparent Hdll remaining offset".
    replace (Z.of_nat 0 - 1)%Z with (-1)%Z by lia.
    have Hm1 : loc_at ls (-1)%Z = null by (rewrite /loc_at; case_decide; [lia | done]).
    rewrite Hm1. iFrame "left".
    have Hr0 : loc_at ls (Z.of_nat 0) = yt.(yjs.yType.start').
    { rewrite Hhead. by destruct ls. }
    rewrite Hr0. iFrame "right". iPureIntro. split; [lia | by left]. }
  wp_for "IH".
  iDestruct (own_dll_length with "Hdll") as %Hlenl2.
  case_bool_decide as Hrem.
  2:{ wp_auto. rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
      iApply ("HΦ" $! (loc_at ls (Z.of_nat q2 - 1)) (loc_at ls q2) q2 off).
      iSplitR "".
      { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. exact Hlen. }
      iPureIntro. split_and!; [lia | reflexivity | reflexivity |].
      destruct Hoffinv as [-> | (Hpos & _ & Hq21 & Hc)]; [by left | right; exact (conj Hpos (conj Hq21 Hc))]. }
  wp_auto.
  have Hoff0 : off = W64 0.
  { destruct Hoffinv as [-> | (_ & Hrem0 & _)]; [done | exfalso; rewrite Hrem0 in Hrem; word]. }
  subst off.
  destruct (decide (q2 < length ls)%nat) as [Hq2lt | Hq2ge].
  2:{ have Hnull2 : loc_at ls q2 = null.
      { rewrite /loc_at decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
      rewrite (bool_decide_eq_true_2 (loc_at ls q2 = null) Hnull2). simpl negb.
      rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
      iApply ("HΦ" $! (loc_at ls (Z.of_nat q2 - 1)) (loc_at ls q2) q2 (W64 0)).
      iSplitR "".
      { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. exact Hlen. }
      iPureIntro. split_and!; [lia | reflexivity | reflexivity | by left]. }
  iDestruct (loc_at_lt_not_null dq parent yt.(yjs.yType.start') tl ls runs q2 Hq2lt with "Hdll") as "[%Hnn2 Hdll]".
  rewrite (bool_decide_eq_false_2 (loc_at ls q2 = null) Hnn2). simpl negb.
  rewrite decide_True; [| done].
  destruct (ls !! q2) as [l2|] eqn:Hl2; [| apply lookup_ge_None in Hl2; lia].
  destruct (runs !! q2) as [r2|] eqn:Hr2; [| apply lookup_ge_None in Hr2; lia].
  iDestruct (own_dll_acc dq parent yt.(yjs.yType.start') tl ls runs q2 l2 r2 Hl2 Hr2 with "Hdll")
    as (prev2 nxt2) "(%Hc2l & %Hc2rn & %Hc2run & %Hpc2 & %Hc2len & Hnode2 & Hback2)".
  have Hc2loc : l2 = loc_at ls (Z.of_nat q2).
  { rewrite /loc_at decide_True; last lia. rewrite Nat2Z.id Hl2 //. }
  iDestruct "Hnode2" as (iv2 olid2 orid2)
    "(Hc2val & Hc2ol & Hc2or & %Hc2inl & %Hc2inr & %Hc2id & #Hc2cont & %Hc2par & %Hc2prev & %Hc2next & %Hc2flags)".
  have Hcount2 : is_countable_flag iv2 = true := flags_if_countable iv2 (run_deleted r2) Hc2flags.
  have Hdel2 : is_deleted_flag iv2 = run_deleted r2 := flags_if_deleted iv2 (run_deleted r2) Hc2flags.
  have Hc2r : iv2.(yjs.item.right') = loc_at ls (Z.of_nat q2 + 1).
  { rewrite Hc2next. exact Hc2rn. }
  iEval (rewrite -Hc2loc) in "Hrightp".
  wp_auto.
  wp_apply (wp_item__Indexable l2 dq iv2 Hcount2 with "[$Hc2val]"). iIntros "Hc2val".
  rewrite Hdel2.
  destruct (run_deleted r2) eqn:Hd2; simpl negb; wp_auto.
  2:{ (* visible node: spend the budget, or record the in-run offset *)
      wp_apply (wp_item__Len l2 dq iv2 with "[$Hc2val $Hc2cont]"). iIntros "Hc2val".
      wp_auto.
      case_bool_decide as Hcmp; wp_auto.
      - (* remaining < Len: the index lands inside this run (issue #28) *)
        iAssert (own_item_node l2 dq (input_of_run r2) false
                   parent prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
        { iExists iv2, olid2, orid2. iFrame "Hc2val Hc2ol Hc2or Hc2cont".
          iPureIntro. split_and!;
            [exact Hc2inl | exact Hc2inr | exact Hc2id  | exact Hc2par
            | exact Hc2prev | exact Hc2next | (by rewrite Hc2flags ?Hd2)]. }
        iDestruct ("Hback2" with "Hnode2") as "Hdll".
        wp_for_post.
        iFrame "HΦ". iExists (S q2), (W64 0), rem.
        iFrame "Hp Hdll Hrem Hoffp".
        rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
        replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
        rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro.
        have Hrlen : length (run_items r2) = length (in_content (input_of_run r2)).
        { symmetry. exact Hc2len. }
        split; [lia |]. right.
        split_and!; [word | done | lia |].
        exists r2. replace (S q2 - 1)%nat with q2 by lia.
        split_and!; [exact Hr2 | exact Hd2 | rewrite Hrlen; word].
      - (* Len <= remaining: spend the whole node (the else branch
           re-reads right.Len(), a second method call) *)
        wp_apply (wp_item__Len l2 dq iv2 with "[$Hc2val $Hc2cont]"). iIntros "Hc2val".
        wp_auto.
        iAssert (own_item_node l2 dq (input_of_run r2) false
                   parent prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
        { iExists iv2, olid2, orid2. iFrame "Hc2val Hc2ol Hc2or Hc2cont".
          iPureIntro. split_and!;
            [exact Hc2inl | exact Hc2inr | exact Hc2id  | exact Hc2par
            | exact Hc2prev | exact Hc2next | (by rewrite Hc2flags ?Hd2)]. }
        iDestruct ("Hback2" with "Hnode2") as "Hdll".
        wp_for_post.
        iFrame "HΦ".
        iExists (S q2), (w64_word_instance.(word.sub) rem (W64 (length (in_content (input_of_run r2))))), (W64 0).
        iFrame "Hp Hdll Hrem Hoffp".
        rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
        replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
        rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro. split; [lia | by left]. }
  iAssert (own_item_node l2 dq (input_of_run r2) true
             parent prev2 nxt2) with "[Hc2val Hc2ol Hc2or]" as "Hnode2".
  { iExists iv2, olid2, orid2. iFrame "Hc2val Hc2ol Hc2or Hc2cont".
    iPureIntro. split_and!;
      [exact Hc2inl | exact Hc2inr | exact Hc2id  | exact Hc2par
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
