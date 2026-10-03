(** The unexported helper every delta walk shares (issue #198):
    - [wp_deltaSnoc]: append one entry to a delta, merging it into a
      same-kind last entry: the model's [delta_snoc]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.delta Require Import model value heap.
(* [proof_prelude] leaves [Z_scope] open; the walk's indices are [nat] *)
Local Open Scope nat_scope.

Section delta_wp.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Lemma wp_deltaSnoc (sl : slice.t) (delta : list DeltaOp) (opv : yjs.DeltaOp.t) (op : DeltaOp) :
  {{{ is_pkg_init yjs ∗ own_delta sl (DfracOwn 1) delta ∗ ⌜delta_op_denotes opv op⌝ }}}
    @! yjs.deltaSnoc #sl #opv
  {{{ (sl' : slice.t), RET #sl'; own_delta sl' (DfracOwn 1) (delta_snoc delta op) }}}.
Proof.
  wp_start as "[Hdelta %Hden]". iNamed "Hdelta".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  have Hlenvs : length vs = length delta by eapply Forall2_length; exact Hdenote.
  wp_auto.
  destruct (decide (0 < length vs)%nat) as [Hpos | Hzero]; last first.
  { (* the delta is empty: append *)
    rewrite (bool_decide_eq_false_2 (sint.Z (W64 0) < sint.Z sl.(slice.len))%Z); last word.
    have Hvs : vs = [] by destruct vs; [done | simpl in Hzero; lia].
    have Hd : delta = [] by destruct delta; [done | rewrite Hvs in Hlenvs; simpl in Hlenvs; lia].
    subst vs delta.
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
    wp_apply (wp_slice_append with "[$Hsl $Hcap $Hs2]").
    iIntros (sl') "(Hsl' & Hcap' & _)". wp_auto.
    iApply "HΦ". iExists [opv]. iFrame "Hsl' Hcap'". iPureIntro. simpl.
    constructor; [exact Hden | constructor]. }
  rewrite (bool_decide_eq_true_2 (sint.Z (W64 0) < sint.Z sl.(slice.len))%Z); last word.
  (* the last entry, in the slice and in the model *)
  destruct (lookup_lt_is_Some_2 vs (length vs - 1) ltac:(lia)) as [lastv Hlastv].
  destruct (lookup_lt_is_Some_2 delta (length vs - 1) ltac:(lia)) as [lastop Hlastop].
  have Hdenlast : delta_op_denotes lastv lastop := Forall2_lookup_lr _ _ _ _ _ _ Hdenote Hlastv Hlastop.
  wp_auto.
  rewrite decide_True; last word.
  iDestruct (own_slice_elem_acc (sint.Z (w64_word_instance.(word.sub) sl.(slice.len) (W64 1))) lastv sl (DfracOwn 1) vs with "Hsl") as "[Hel Hgive]".
  { word. }
  { replace (Z.to_nat (sint.Z (w64_word_instance.(word.sub) sl.(slice.len) (W64 1)))) with (length vs - 1)%nat by word. exact Hlastv. }
  wp_auto.
  have Hi : (S (length vs - 1) = length delta)%nat by lia.
  have Hdsplit : delta = take (length vs - 1) delta ++ [lastop].
  { rewrite -{1}(take_drop_middle delta (length vs - 1) lastop Hlastop).
    rewrite (drop_ge delta (S (length vs - 1))); last lia. done. }
  have Hvsplit : vs = take (length vs - 1) vs ++ [lastv].
  { rewrite -{1}(take_drop_middle vs (length vs - 1) lastv Hlastv).
    rewrite (drop_ge vs (S (length vs - 1))); last lia. done. }
  have Hdenpre : Forall2 delta_op_denotes (take (length vs - 1) vs) (take (length vs - 1) delta)
    := Forall2_take _ _ _ _ Hdenote.
  destruct (decide (lastv.(yjs.DeltaOp.Kind') = opv.(yjs.DeltaOp.Kind'))) as [Hsame | Hdiff]; last first.
  { (* another kind: append *)
    rewrite (bool_decide_eq_false_2 (lastv.(yjs.DeltaOp.Kind') = opv.(yjs.DeltaOp.Kind')) Hdiff).
    wp_auto.
    iDestruct ("Hgive" $! lastv with "Hel") as "Hsl".
    rewrite list_insert_id; last (replace (sint.nat (w64_word_instance.(word.sub) sl.(slice.len) (W64 1))) with (length vs - 1)%nat by word; exact Hlastv).
    have Hsnoc : delta_snoc delta op = delta ++ [op].
    { rewrite {1}Hdsplit (delta_snoc_app _ [lastop] op); last done.
      rewrite {2}Hdsplit -app_assoc. f_equal. simpl.
      destruct lastop as [a | s | a], op as [b | t | b];
        destruct Hdenlast as [Hk1 _], Hden as [Hk2 _];
        try (exfalso; apply Hdiff; rewrite Hk1 Hk2; done); reflexivity. }
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
    wp_apply (wp_slice_append with "[$Hsl $Hcap $Hs2]").
    iIntros (sl') "(Hsl' & Hcap' & _)". wp_auto.
    iApply "HΦ". iExists (vs ++ [opv]). rewrite Hsnoc. iFrame "Hsl' Hcap'". iPureIntro.
    apply Forall2_app; first exact Hdenote. constructor; [exact Hden | constructor]. }
  (* the same kind: merge into the last entry, in place *)
  rewrite (bool_decide_eq_true_2 (lastv.(yjs.DeltaOp.Kind') = opv.(yjs.DeltaOp.Kind')) Hsame).
  wp_auto.
  rewrite decide_True; last word.
  wp_auto.
  destruct lastop as [a | s | a], op as [b | t | b];
    destruct Hdenlast as [Hk1 Hv1], Hden as [Hk2 Hv2];
    try (exfalso; rewrite Hk1 Hk2 in Hsame; done).
  - (* retain + retain *)
    rewrite Hk2 (bool_decide_eq_false_2 (W8 0 = W8 1)); last done.
    wp_auto.
    rewrite decide_True; last word.
    wp_auto.
    iDestruct ("Hgive" with "Hel") as "Hsl".
    iApply "HΦ".
    iExists _. iFrame "Hsl Hcap". iPureIntro.
    have Hsnoc : delta_snoc delta (Retain b) = take (length vs - 1) delta ++ [Retain (a + b)].
    { rewrite {1}Hdsplit (delta_snoc_app _ [Retain a] (Retain b)) //. }
    rewrite Hsnoc.
    replace (sint.nat (w64_word_instance.(word.sub) sl.(slice.len) (W64 1))) with (length vs - 1)%nat by word.
    have Hsnoc' : take (length vs - 1) delta ++ [Retain (a + b)] = <[(length vs - 1)%nat := Retain (a + b)]> delta.
    { rewrite {2}Hdsplit insert_app_r_alt; last (rewrite length_take; lia).
      rewrite length_take.
      replace (length vs - 1 - (length vs - 1) `min` length delta)%nat with 0%nat by lia. done. }
    rewrite Hsnoc'.
    apply Forall2_insert; first exact Hdenote.
    split; [exact Hk1 | simpl; rewrite Hv1 Hv2; word].
  - (* insert + insert *)
    rewrite Hk2 (bool_decide_eq_true_2 (W8 1 = W8 1)); last done.
    wp_auto.
    rewrite decide_True; last word.
    wp_auto.
    iDestruct ("Hgive" with "Hel") as "Hsl".
    iApply "HΦ".
    iExists _. iFrame "Hsl Hcap". iPureIntro.
    have Hsnoc : delta_snoc delta (Insert t) = take (length vs - 1) delta ++ [Insert (s ++ t)].
    { rewrite {1}Hdsplit (delta_snoc_app _ [Insert s] (Insert t)) //. }
    rewrite Hsnoc.
    replace (sint.nat (w64_word_instance.(word.sub) sl.(slice.len) (W64 1))) with (length vs - 1)%nat by word.
    have Hsnoc' : take (length vs - 1) delta ++ [Insert (s ++ t)] = <[(length vs - 1)%nat := Insert (s ++ t)]> delta.
    { rewrite {2}Hdsplit insert_app_r_alt; last (rewrite length_take; lia).
      rewrite length_take.
      replace (length vs - 1 - (length vs - 1) `min` length delta)%nat with 0%nat by lia. done. }
    rewrite Hsnoc'.
    apply Forall2_insert; first exact Hdenote.
    split; [exact Hk1 | simpl; rewrite Hv1 Hv2 //].
  - (* delete + delete *)
    rewrite Hk2 (bool_decide_eq_false_2 (W8 2 = W8 1)); last done.
    wp_auto.
    rewrite decide_True; last word.
    wp_auto.
    iDestruct ("Hgive" with "Hel") as "Hsl".
    iApply "HΦ".
    iExists _. iFrame "Hsl Hcap". iPureIntro.
    have Hsnoc : delta_snoc delta (Delete b) = take (length vs - 1) delta ++ [Delete (a + b)].
    { rewrite {1}Hdsplit (delta_snoc_app _ [Delete a] (Delete b)) //. }
    rewrite Hsnoc.
    replace (sint.nat (w64_word_instance.(word.sub) sl.(slice.len) (W64 1))) with (length vs - 1)%nat by word.
    have Hsnoc' : take (length vs - 1) delta ++ [Delete (a + b)] = <[(length vs - 1)%nat := Delete (a + b)]> delta.
    { rewrite {2}Hdsplit insert_app_r_alt; last (rewrite length_take; lia).
      rewrite length_take.
      replace (length vs - 1 - (length vs - 1) `min` length delta)%nat with 0%nat by lia. done. }
    rewrite Hsnoc'.
    apply Forall2_insert; first exact Hdenote.
    split; [exact Hk1 | simpl; rewrite Hv1 Hv2; word].
Qed.

End delta_wp.
