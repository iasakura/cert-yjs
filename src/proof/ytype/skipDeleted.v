(** [wp_skipDeleted]: the walk past the tombstones that follow a list
    position, which [Text.InsertIn] runs between [yType.findPos] and the
    insert so that the new items go after them ([skip_deleted], over the
    cursor into the run list); read-only, so stated at a generic [dq].

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

Notation A := (list w16).

(** [skipDeleted] takes the two neighbours of the cursor [p] into the type's
    run list and returns the two neighbours of the cursor [p'] that
    [skip_deleted] names: every run from [p] up to [p'] is tombstoned and the
    run at [p'], when there is one, is live. The addresses are read off the
    type's address list [ls], [null] outside it, as in [wp_yType__findPos]. *)
Lemma wp_skipDeleted (parent : loc) (dq : dfrac) (ls : list loc)
    (tm : type_model) (p : nat) :
  {{{ is_pkg_init yjs ∗ own_ytype parent dq ls tm ∗
      ⌜(p <= length (tm_runs tm))%nat⌝ }}}
    @! yjs.skipDeleted #(loc_at ls (Z.of_nat p - 1)) #(loc_at ls (Z.of_nat p))
  {{{ (p' : nat), RET (#(loc_at ls (Z.of_nat p' - 1)), #(loc_at ls (Z.of_nat p')));
      own_ytype parent dq ls tm ∗ ⌜skip_deleted (tm_runs tm) p p'⌝ }}}.
Proof.
  wp_start as "[Hyt %Hp]".
  destruct tm as [runs]. simpl in *.
  iNamed "Hyt".
  iDestruct (own_dll_length with "Hdll") as %Hlenls.
  wp_auto.
  (* the cursor [q] walks right from [p] over tombstoned runs only *)
  iAssert (∃ (q : nat),
      "Hdll" ∷ own_dll dq parent yt.(yjs.yType.start') tl null null ls runs ∗
      "Hleftp" ∷ left_ptr ↦ loc_at ls (Z.of_nat q - 1) ∗
      "Hrightp" ∷ right_ptr ↦ loc_at ls (Z.of_nat q) ∗
      "%Hq" ∷ ⌜(p <= q <= length runs)%nat⌝ ∗
      "%Hdel" ∷ ⌜∀ i r, (p <= i < q)%nat -> runs !! i = Some r -> run_deleted r = true⌝)%I
      with "[Hdll left right]" as "IH".
  { iExists p. iFrame "Hdll left right". iPureIntro. split; [lia | intros; lia]. }
  wp_for "IH".
  destruct (decide (q < length ls)%nat) as [Hqlt | Hqge].
  - (* right ≠ null: read its Deleted bit; a tombstone advances the cursor *)
    iDestruct (loc_at_lt_not_null dq parent yt.(yjs.yType.start') tl ls runs q Hqlt with "Hdll") as "[%Hnn Hdll]".
    rewrite (bool_decide_eq_false_2 (loc_at ls q = null) Hnn). simpl negb.
    destruct (ls !! q) as [lq|] eqn:Hlq; [| apply lookup_ge_None in Hlq; lia].
    destruct (runs !! q) as [rq|] eqn:Hrq; [| apply lookup_ge_None in Hrq; simpl in Hlenls; lia].
    iDestruct (own_dll_acc dq parent yt.(yjs.yType.start') tl ls runs q lq rq Hlq Hrq with "Hdll")
      as (prevq nxtq) "(%Hcl & %Hcrn & %Hrun & %Hpcq & %Hclen & Hnode & Hback)".
    have Hcloc : lq = loc_at ls (Z.of_nat q).
    { rewrite /loc_at decide_True; last lia. rewrite Nat2Z.id Hlq //. }
    iDestruct "Hnode" as (itemVal olidq oridq)
      "(Hcval & Hcol & Hcor & %Hinl & %Hinr & %Hid & #Hcontent & %Hparq & %Hprevq & %Hnextq & %Hflags)".
    have Hcr : itemVal.(yjs.item.right') = loc_at ls (Z.of_nat q + 1).
    { rewrite Hnextq. exact Hcrn. }
    iEval (rewrite -Hcloc) in "Hrightp".
    wp_auto.
    wp_apply (wp_item__Deleted lq dq itemVal with "[$Hcval]"). iIntros "Hcval".
    rewrite (flags_if_deleted itemVal (run_deleted rq) Hflags).
    destruct (run_deleted rq) eqn:Hdq.
    + (* tombstone: advance the cursor *)
      rewrite decide_True; [| reflexivity].
      wp_auto.
      iAssert (own_item_node lq dq (input_of_run rq) true parent prevq nxtq)
        with "[Hcval Hcol Hcor]" as "Hnode".
      { iExists itemVal, olidq, oridq. iFrame "Hcval Hcol Hcor Hcontent".
        iPureIntro. split_and!;
          [exact Hinl | exact Hinr | exact Hid | exact Hparq
          | exact Hprevq | exact Hnextq | (by rewrite Hflags ?Hdq)]. }
      iDestruct ("Hback" with "Hnode") as "Hdll".
      wp_for_post.
      iFrame "HΦ Hparent". iExists (S q). iFrame "Hdll".
      rewrite Hcr. replace (Z.of_nat (S q) - 1)%Z with (Z.of_nat q) by lia.
      replace (Z.of_nat (S q)) with (Z.of_nat q + 1)%Z by lia.
      rewrite Hcloc. iFrame "Hleftp Hrightp". iPureIntro.
      split; [simpl in Hlenls; lia |].
      move=> i r Hi Hr. destruct (decide (i = q)) as [-> | Hne].
      * rewrite Hrq in Hr. injection Hr as <-. exact Hdq.
      * apply (Hdel i r); [lia | exact Hr].
    + (* live run: the walk stops in front of it *)
      rewrite decide_False; [| done]. rewrite decide_True; [| done].
      iAssert (own_item_node lq dq (input_of_run rq) false parent prevq nxtq)
        with "[Hcval Hcol Hcor]" as "Hnode".
      { iExists itemVal, olidq, oridq. iFrame "Hcval Hcol Hcor Hcontent".
        iPureIntro. split_and!;
          [exact Hinl | exact Hinr | exact Hid | exact Hparq
          | exact Hprevq | exact Hnextq | (by rewrite Hflags ?Hdq)]. }
      iDestruct ("Hback" with "Hnode") as "Hdll".
      iEval (rewrite Hcloc) in "Hrightp".
      wp_auto.
      iApply ("HΦ" $! q). iSplitR "".
      { iExists yt, tl. iFrame "Hparent Hdll". iPureIntro. exact Hlen. }
      iPureIntro. split_and!; [lia | lia | exact Hdel |].
      move=> r Hr. rewrite Hrq in Hr. injection Hr as <-. exact Hdq.
  - (* right = null: the end of the list *)
    have Hnull : loc_at ls q = null.
    { rewrite /loc_at decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
    rewrite (bool_decide_eq_true_2 (loc_at ls q = null) Hnull). simpl negb.
    wp_auto.
    rewrite decide_False; [| done]. rewrite decide_True; [| done].
    wp_auto.
    iApply ("HΦ" $! q). iSplitR "".
    { iExists yt, tl. iFrame "Hparent Hdll". iPureIntro. exact Hlen. }
    iPureIntro. split_and!; [lia | lia | exact Hdel |].
    move=> r Hr. apply lookup_lt_Some in Hr. simpl in Hlenls. lia.
Qed.

End ytype.
