(** The unexported helper every delta walk shares (issue #198):
    - [wp_deltaSnoc]: append one entry to a delta, merging it into a
      same-kind last entry: the model's [delta_snoc]. Two inserts merge into
      a fresh slice (the entries' own content is read-only), which the
      merged entry then holds read-only in turn. *)
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

Notation A := (list w16).

Lemma wp_deltaSnoc (sl : slice.t) (delta : list DeltaOp) (opv : yjs.DeltaOp.t) (op : DeltaOp) :
  {{{ is_pkg_init yjs ∗ own_delta sl (DfracOwn 1) delta ∗ is_delta_op opv op }}}
    @! yjs.deltaSnoc #sl #opv
  {{{ (sl' : slice.t), RET #sl'; own_delta sl' (DfracOwn 1) (delta_snoc delta op) }}}.
Proof.
  wp_start as "[Hdelta #Hden]". iNamed "Hdelta".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  iDestruct (big_sepL2_length with "Hdenote") as %Hlenvs.
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
    iApply "HΦ". iExists [opv]. iFrame "Hsl' Hcap'". simpl.
    iSplit; [iExact "Hden" | done]. }
  rewrite (bool_decide_eq_true_2 (sint.Z (W64 0) < sint.Z sl.(slice.len))%Z); last word.
  (* the last entry, in the slice and in the model *)
  destruct (lookup_lt_is_Some_2 vs (length vs - 1) ltac:(lia)) as [lastv Hlastv].
  destruct (lookup_lt_is_Some_2 delta (length vs - 1) ltac:(lia)) as [lastop Hlastop].
  iDestruct (big_sepL2_lookup _ _ _ (length vs - 1) lastv lastop Hlastv Hlastop with "Hdenote") as "#Hdenlast".
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
  iDestruct "Hdenlast" as "[%Hklast Hclast]". iDestruct "Hden" as "[%Hkop Hcop]".
  have Hk1 : lastv.(yjs.DeltaOp.Kind') = (match lastop with Retain _ => W8 0 | Insert _ => W8 1 | Delete _ => W8 2 end)
    by (destruct lastop; [exact (proj1 Hklast) | exact Hklast | exact (proj1 Hklast)]).
  have Hk2 : opv.(yjs.DeltaOp.Kind') = (match op with Retain _ => W8 0 | Insert _ => W8 1 | Delete _ => W8 2 end)
    by (destruct op; [exact (proj1 Hkop) | exact Hkop | exact (proj1 Hkop)]).
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
        try (exfalso; apply Hdiff; rewrite Hk1 Hk2; done); reflexivity. }
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
    wp_apply (wp_slice_append with "[$Hsl $Hcap $Hs2]").
    iIntros (sl') "(Hsl' & Hcap' & _)". wp_auto.
    iApply "HΦ". iExists (vs ++ [opv]). rewrite Hsnoc. iFrame "Hsl' Hcap'".
    iApply big_sepL2_snoc. iFrame "Hdenote". iSplit; [iPureIntro; exact Hkop | iExact "Hcop"]. }
  (* the same kind: merge into the last entry, in place *)
  rewrite (bool_decide_eq_true_2 (lastv.(yjs.DeltaOp.Kind') = opv.(yjs.DeltaOp.Kind')) Hsame).
  wp_auto.
  rewrite decide_True; last word.
  wp_auto.
  iDestruct (big_sepL2_insert_acc _ _ _ _ _ _ Hlastv Hlastop with "Hdenote") as "[_ Hins]".
  have Hidx : sint.nat (w64_word_instance.(word.sub) sl.(slice.len) (W64 1)) = (length vs - 1)%nat by word.
  destruct lastop as [a | s | a], op as [b | t | b];
    try (exfalso; rewrite Hk1 Hk2 in Hsame; done).
  - (* retain + retain *)
    destruct Hklast as [_ Hv1]. destruct Hkop as [_ Hv2].
    rewrite Hk2 (bool_decide_eq_false_2 (W8 0 = W8 1)); last done.
    wp_auto.
    rewrite decide_True; last word.
    wp_auto.
    iDestruct ("Hgive" with "Hel") as "Hsl".
    iApply "HΦ".
    iExists _. iFrame "Hsl Hcap".
    have Hsnoc : delta_snoc delta (Retain b) = take (length vs - 1) delta ++ [Retain (a + b)].
    { rewrite {1}Hdsplit (delta_snoc_app _ [Retain a] (Retain b)) //. }
    rewrite Hsnoc.
    have Hsnoc' : take (length vs - 1) delta ++ [Retain (a + b)] = <[(length vs - 1)%nat := Retain (a + b)]> delta.
    { rewrite {2}Hdsplit insert_app_r_alt; last (rewrite length_take; lia).
      rewrite length_take.
      replace (length vs - 1 - (length vs - 1) `min` length delta)%nat with 0%nat by lia. done. }
    rewrite Hsnoc' Hidx.
    iApply "Hins". iSplit; [iPureIntro; split; [exact Hk1 | simpl; rewrite Hv1 Hv2; word] | done].
  - (* insert + insert: the two contents are read-only (the entries' own,
       possibly a node's), so they are joined into a fresh slice, which the
       merged entry then holds read-only in turn *)
    rewrite Hk2 (bool_decide_eq_true_2 (W8 1 = W8 1)); last done.
    wp_auto.
    iAssert (slice.nil ↦* ([] : list w16))%I with "[]" as "Hnil0"; first iApply own_slice_nil.
    iAssert (own_slice_cap w16 slice.nil (DfracOwn 1))%I with "[]" as "Hnilcap"; first iApply own_slice_cap_nil.
    wp_apply (wp_slice_append with "[Hnil0 Hnilcap]"); first (iFrame "Hnil0 Hnilcap"; iExact "Hclast").
    iIntros (j1) "(Hj1 & Hj1cap & _)". wp_auto.
    wp_apply (wp_slice_append with "[Hj1 Hj1cap]"); first (iFrame "Hj1 Hj1cap"; iExact "Hcop").
    iIntros (j2) "(Hj2 & Hj2cap & _)". wp_auto.
    iPersist "Hj2".
    rewrite decide_True; last word.
    wp_auto.
    iDestruct ("Hgive" with "Hel") as "Hsl".
    iApply "HΦ".
    iExists _. iFrame "Hsl Hcap".
    have Hsnoc : delta_snoc delta (Insert t) = take (length vs - 1) delta ++ [Insert (s ++ t)].
    { rewrite {1}Hdsplit (delta_snoc_app _ [Insert s] (Insert t)) //. }
    rewrite Hsnoc.
    have Hsnoc' : take (length vs - 1) delta ++ [Insert (s ++ t)] = <[(length vs - 1)%nat := Insert (s ++ t)]> delta.
    { rewrite {2}Hdsplit insert_app_r_alt; last (rewrite length_take; lia).
      rewrite length_take.
      replace (length vs - 1 - (length vs - 1) `min` length delta)%nat with 0%nat by lia. done. }
    rewrite Hsnoc' Hidx.
    iApply "Hins". iSplit; [iPureIntro; exact Hk1 | simpl; iExact "Hj2"].
  - (* delete + delete *)
    destruct Hklast as [_ Hv1]. destruct Hkop as [_ Hv2].
    rewrite Hk2 (bool_decide_eq_false_2 (W8 2 = W8 1)); last done.
    wp_auto.
    rewrite decide_True; last word.
    wp_auto.
    iDestruct ("Hgive" with "Hel") as "Hsl".
    iApply "HΦ".
    iExists _. iFrame "Hsl Hcap".
    have Hsnoc : delta_snoc delta (Delete b) = take (length vs - 1) delta ++ [Delete (a + b)].
    { rewrite {1}Hdsplit (delta_snoc_app _ [Delete a] (Delete b)) //. }
    rewrite Hsnoc.
    have Hsnoc' : take (length vs - 1) delta ++ [Delete (a + b)] = <[(length vs - 1)%nat := Delete (a + b)]> delta.
    { rewrite {2}Hdsplit insert_app_r_alt; last (rewrite length_take; lia).
      rewrite length_take.
      replace (length vs - 1 - (length vs - 1) `min` length delta)%nat with 0%nat by lia. done. }
    rewrite Hsnoc' Hidx.
    iApply "Hins". iSplit; [iPureIntro; split; [exact Hk1 | simpl; rewrite Hv1 Hv2; word] | done].
Qed.

End delta_wp.
