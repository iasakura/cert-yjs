(** [wp_ApplyDelta]: the application-side patch (issue #198). The spec is
    the model's fact alone: a delta that patches the code units [units] to
    [units'] ([apply_delta]) makes the Go return a fresh slice holding
    [units'], and [true]; the input and the delta are only read; a delta a
    [Poll] returned patches the observed text ([apply_text_delta]). The
    counts fit a [uint64] because they are at most the input's length, which
    the Go's own [len] call bounds ([apply_delta_fits], inside the proof).
    The failing case (a retain or a delete past the end, [(nil, false)]) has
    no verified caller and is not specified. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.github_com.mit_pdos.perennial.goose.model Require Import strings.
From New.proof.item Require Import wp_private.
From New.proof.delta Require Import model value heap.

Section delta_apply.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := (list w16).

(* ----- the steps of a run, one op at a time (what the loop invariant
   advances by; [take_S_r] splits the processed prefix) ----- *)

#[local] Lemma delta_run_take_insert (d : list DeltaOp) (k : nat) (t o r s : A) :
  d !! k = Some (Insert t) ->
  delta_run (take k d) s = Some (o, r) ->
  delta_run (take (S k) d) s = Some (o ++ t, r).
Proof.
  move=> Hk Hrun. rewrite (take_S_r _ _ _ Hk) delta_run_app Hrun /=.
  rewrite app_nil_r //.
Qed.

#[local] Lemma delta_run_take_retain (d : list DeltaOp) (k n : nat) (o r s : A) :
  d !! k = Some (Retain n) ->
  delta_run (take k d) s = Some (o, r) ->
  (n <= length r)%nat ->
  delta_run (take (S k) d) s = Some (o ++ take n r, drop n r).
Proof.
  move=> Hk Hrun Hle. rewrite (take_S_r _ _ _ Hk) delta_run_app Hrun /=.
  rewrite decide_True; last done. rewrite /= app_nil_r //.
Qed.

#[local] Lemma delta_run_take_delete (d : list DeltaOp) (k n : nat) (o r s : A) :
  d !! k = Some (Delete n) ->
  delta_run (take k d) s = Some (o, r) ->
  (n <= length r)%nat ->
  delta_run (take (S k) d) s = Some (o, drop n r).
Proof.
  move=> Hk Hrun Hle. rewrite (take_S_r _ _ _ Hk) delta_run_app Hrun /=.
  rewrite decide_True; last done. rewrite /= app_nil_r //.
Qed.

(** An op that runs past the end fails the whole delta. *)
#[local] Lemma delta_run_overrun (d : list DeltaOp) (k n : nat) (o r s : A) :
  (d !! k = Some (Retain n) ∨ d !! k = Some (Delete n)) ->
  delta_run (take k d) s = Some (o, r) ->
  (length r < n)%nat ->
  delta_run d s = None.
Proof.
  move=> Hk Hrun Hlt.
  destruct Hk as [Hk | Hk].
  - rewrite -(take_drop_middle d k _ Hk) delta_run_app Hrun /=.
    rewrite decide_False //. lia.
  - rewrite -(take_drop_middle d k _ Hk) delta_run_app Hrun /=.
    rewrite decide_False //. lia.
Qed.

Lemma wp_ApplyDelta (s : slice.t) (dq : dfrac) (units units' : A)
    (sl : slice.t) (dq' : dfrac) (delta : list DeltaOp) :
  apply_delta delta units = Some units' ->
  {{{ is_pkg_init yjs ∗ s ↦*{dq} units ∗ own_delta sl dq' delta }}}
    @! yjs.ApplyDelta #s #sl
  {{{ (res : slice.t), RET (#res, #true);
      s ↦*{dq} units ∗ own_delta sl dq' delta ∗
      res ↦* units' ∗ own_slice_cap w16 res (DfracOwn 1) }}}.
Proof.
  move=> Hpatch.
  wp_start as "(Hs & Hdelta)". iNamed "Hdelta".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  iDestruct (own_slice_len with "Hs") as %[Hslen Hslen0].
  iDestruct (big_sepL2_length with "Hdenote") as %Hlenvs.
  wp_auto.
  have Hfits : delta_fits delta := apply_delta_fits _ _ _ Hpatch ltac:(word).
  have Hslw : s.(slice.len) = W64 (length units) by word.
  iEval (rewrite Hslw) in "remaining".
  (* the outer loop: the ops before [k] ran the input to [drop pos units],
     and [result] holds their output in a fresh slice the loop owns *)
  iAssert (∃ (k pos : nat) (res : slice.t) (out : A),
    "Hk" ∷ k_ptr ↦ W64 k ∗
    "Hresult" ∷ result_ptr ↦ res ∗
    "Hres" ∷ res ↦* out ∗
    "Hrescap" ∷ own_slice_cap w16 res (DfracOwn 1) ∗
    "Hposition" ∷ position_ptr ↦ W64 pos ∗
    "Hremaining" ∷ remaining_ptr ↦ W64 (Z.of_nat (length units - pos)) ∗
    "Hs_ptr" ∷ s_ptr ↦ s ∗
    "Hs" ∷ s ↦*{dq} units ∗
    "Hdelta" ∷ delta_ptr ↦ sl ∗
    "Hsl" ∷ sl ↦*{dq'} vs ∗
    "%Hkle" ∷ ⌜(k <= length delta)%nat⌝ ∗
    "%Hposle" ∷ ⌜(pos <= length units)%nat⌝ ∗
    "%Hrun" ∷ ⌜delta_run (take k delta) units = Some (out, drop pos units)⌝)%I
    with "[k result position remaining s delta Hsl Hs]" as "IH".
  { iExists 0%nat, 0%nat, slice.nil, []. rewrite Nat.sub_0_r drop_0.
    iFrame "k result position remaining s delta Hsl Hs".
    iSplitL; first iApply own_slice_nil. iSplitL; first iApply own_slice_cap_nil.
    iPureIntro. split_and!; [lia | lia | done]. }
  wp_for "IH".
  destruct (decide (k < length delta)%nat) as [Hklt | Hkge].
  - (* one more op *)
    rewrite (bool_decide_eq_true_2 (sint.Z (W64 k) < sint.Z sl.(slice.len))); last word.
    destruct (lookup_lt_is_Some_2 vs k ltac:(lia)) as [opv Hopv].
    destruct (lookup_lt_is_Some_2 delta k Hklt) as [op Hop].
    iDestruct (big_sepL2_lookup _ _ _ k opv op Hopv Hop with "Hdenote") as "#Hden".
    wp_auto.
    rewrite decide_True; last word.
    iDestruct (own_slice_elem_acc (sint.Z (W64 k)) opv sl dq' vs with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z (W64 k))) with k by word. exact Hopv. }
    wp_auto.
    iDestruct ("Hgive" $! opv with "Hel") as "Hsl".
    rewrite list_insert_id; last (replace (Z.to_nat (sint.Z (W64 k))) with k by word; exact Hopv).
    have Hopfits : delta_op_fits op := Forall_lookup_1 _ _ _ _ Hfits Hop.
    iDestruct "Hden" as "[%Hkind Hcop]".
    destruct op as [n | t | n]; simpl in Hopfits.
    + (* retain [n] units *)
      destruct Hkind as [Hkind Hval].
      have HL : uint.Z opv.(yjs.DeltaOp.Length') = Z.of_nat n by rewrite Hval; word.
      rewrite Hkind. wp_auto.
      destruct (decide (n <= length units - pos)%nat) as [Hle | Hgt]; last first.
      { (* overrun: the patch fails *)
        rewrite (bool_decide_eq_true_2 (uint.Z (W64 (length units - pos)%nat) < uint.Z opv.(yjs.DeltaOp.Length'))); last word.
        wp_auto. wp_for_post.
        have Hnone : apply_delta delta units = None.
        { rewrite /apply_delta (delta_run_overrun delta k n out (drop pos units) units (or_introl Hop) Hrun) //.
          rewrite length_drop. lia. }
        rewrite Hnone in Hpatch. discriminate. }
      rewrite (bool_decide_eq_false_2 (uint.Z (W64 (length units - pos)%nat) < uint.Z opv.(yjs.DeltaOp.Length'))); last word.
      wp_auto.
      rewrite Hkind (bool_decide_eq_true_2 (W8 0 = W8 0)); last done.
      wp_auto.
      (* the inner loop copies the next [n] units, one load and append each *)
      iAssert (∃ (i : nat) (resi : slice.t),
        "Hi" ∷ i_ptr ↦ W64 i ∗
        "Hresult" ∷ result_ptr ↦ resi ∗
        "Hres" ∷ resi ↦* (out ++ take i (drop pos units)) ∗
        "Hrescap" ∷ own_slice_cap w16 resi (DfracOwn 1) ∗
        "Hposition" ∷ position_ptr ↦ W64 pos ∗
        "Hs_ptr" ∷ s_ptr ↦ s ∗
        "Hs" ∷ s ↦*{dq} units ∗
        "Hop" ∷ op_ptr ↦ opv ∗
        "%Hile" ∷ ⌜(i <= n)%nat⌝)%I
        with "[i Hresult Hres Hrescap Hposition Hs_ptr Hs op]" as "IHi".
      { iExists 0%nat, res. rewrite take_0 app_nil_r. iFrame "i Hresult Hres Hrescap Hposition Hs_ptr Hs op". iPureIntro. lia. }
      wp_for "IHi".
      destruct (decide (i < n)%nat) as [Hilt | Hige].
      * (* one more unit *)
        rewrite (bool_decide_eq_true_2 (uint.Z (W64 i) < uint.Z opv.(yjs.DeltaOp.Length'))); last word.
        destruct (lookup_lt_is_Some_2 units (pos + i) ltac:(lia)) as [b Hb].
        wp_auto.
        rewrite decide_True; last word.
        wp_apply (wp_load_slice_index with "[$Hs]").
        { word. }
        { iPureIntro. replace (Z.to_nat (sint.Z (w64_word_instance.(word.add) (W64 pos) (W64 i)))) with (pos + i)%nat by word. exact Hb. }
        iIntros "Hs".
        wp_auto.
        wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
        wp_apply (wp_slice_append with "[$Hres $Hrescap $Hs2]").
        iIntros (res') "(Hres & Hrescap & _)". wp_auto. wp_for_post.
        iFrame "Hcap HΦ Hk Hremaining Hdelta Hsl".
        iExists (S i), res'.
        replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
        rewrite (take_S_r (drop pos units) i b); last by rewrite lookup_drop.
        rewrite app_assoc. iFrame "Hi Hresult Hres Hrescap Hposition Hs_ptr Hs Hop". iPureIntro. lia.
      * (* the [n] units are copied: advance the cursor *)
        have Hieq : i = n by word.
        subst i.
        rewrite (bool_decide_eq_false_2 (uint.Z (W64 n) < uint.Z opv.(yjs.DeltaOp.Length'))); last word.
        wp_auto. wp_for_post.
        iFrame "Hcap HΦ".
        iExists (S k), (pos + n)%nat, resi, (out ++ take n (drop pos units)).
        replace (w64_word_instance.(word.add) (W64 k) (W64 1)) with (W64 (S k)) by word.
        replace (w64_word_instance.(word.add) (W64 pos) opv.(yjs.DeltaOp.Length')) with (W64 (Z.of_nat (pos + n))) by word.
        replace (w64_word_instance.(word.sub) (W64 (length units - pos)%nat) opv.(yjs.DeltaOp.Length')) with (W64 (Z.of_nat (length units - (pos + n)))) by word.
        iFrame "Hk Hresult Hres Hrescap Hposition Hremaining Hs_ptr Hs Hdelta Hsl".
        iPureIntro. split_and!; [lia | lia |].
        rewrite (delta_run_take_retain delta k n out (drop pos units) units Hop Hrun); last by rewrite length_drop; lia.
        rewrite drop_drop //.
    + (* insert [t]: the entry's read-only content is appended, as the source *)
      rewrite Hkind. wp_auto.
      wp_apply (wp_slice_append with "[Hres Hrescap]"); first (iFrame "Hres Hrescap"; iExact "Hcop").
      iIntros (res') "(Hres & Hrescap & _)". wp_auto. wp_for_post.
      iFrame "Hcap HΦ".
      iExists (S k), pos, res', (out ++ t).
      replace (w64_word_instance.(word.add) (W64 k) (W64 1)) with (W64 (S k)) by word.
      iFrame "Hk Hresult Hres Hrescap Hposition Hremaining Hs_ptr Hs Hdelta Hsl".
      iPureIntro. split_and!; [lia | lia |].
      exact (delta_run_take_insert delta k t out (drop pos units) units Hop Hrun).
    + (* delete [n] units *)
      destruct Hkind as [Hkind Hval].
      have HL : uint.Z opv.(yjs.DeltaOp.Length') = Z.of_nat n by rewrite Hval; word.
      rewrite Hkind. wp_auto.
      destruct (decide (n <= length units - pos)%nat) as [Hle | Hgt]; last first.
      { rewrite (bool_decide_eq_true_2 (uint.Z (W64 (length units - pos)%nat) < uint.Z opv.(yjs.DeltaOp.Length'))); last word.
        wp_auto. wp_for_post.
        have Hnone : apply_delta delta units = None.
        { rewrite /apply_delta (delta_run_overrun delta k n out (drop pos units) units (or_intror Hop) Hrun) //.
          rewrite length_drop. lia. }
        rewrite Hnone in Hpatch. discriminate. }
      rewrite (bool_decide_eq_false_2 (uint.Z (W64 (length units - pos)%nat) < uint.Z opv.(yjs.DeltaOp.Length'))); last word.
      wp_auto.
      rewrite Hkind (bool_decide_eq_false_2 (W8 2 = W8 0)); last done.
      wp_auto. wp_for_post.
      iFrame "Hcap HΦ".
      iExists (S k), (pos + n)%nat, res, out.
      replace (w64_word_instance.(word.add) (W64 k) (W64 1)) with (W64 (S k)) by word.
      replace (w64_word_instance.(word.add) (W64 pos) opv.(yjs.DeltaOp.Length')) with (W64 (Z.of_nat (pos + n))) by word.
      replace (w64_word_instance.(word.sub) (W64 (length units - pos)%nat) opv.(yjs.DeltaOp.Length')) with (W64 (Z.of_nat (length units - (pos + n)))) by word.
      iFrame "Hk Hresult Hres Hrescap Hposition Hremaining Hs_ptr Hs Hdelta Hsl".
      iPureIntro. split_and!; [lia | lia |].
      rewrite (delta_run_take_delete delta k n out (drop pos units) units Hop Hrun); last by rewrite length_drop; lia.
      rewrite drop_drop //.
  - (* every op ran: keep the rest of the input (the implicit trailing retain) *)
    rewrite (bool_decide_eq_false_2 (sint.Z (W64 k) < sint.Z sl.(slice.len))); last word.
    have Hkeq : k = length delta by word.
    rewrite Hkeq take_ge in Hrun; last lia.
    wp_auto.
    iAssert (∃ (j : nat) (resj : slice.t),
      "Hresult" ∷ result_ptr ↦ resj ∗
      "Hres" ∷ resj ↦* (out ++ take j (drop pos units)) ∗
      "Hrescap" ∷ own_slice_cap w16 resj (DfracOwn 1) ∗
      "Hposition" ∷ position_ptr ↦ W64 (pos + j)%nat ∗
      "Hs_ptr" ∷ s_ptr ↦ s ∗
      "Hs" ∷ s ↦*{dq} units ∗
      "%Hjle" ∷ ⌜(pos + j <= length units)%nat⌝)%I
      with "[Hresult Hres Hrescap Hposition Hs_ptr Hs]" as "IHj".
    { iExists 0%nat, res. rewrite take_0 app_nil_r Nat.add_0_r. iFrame "Hresult Hres Hrescap Hposition Hs_ptr Hs". iPureIntro. lia. }
    wp_for "IHj".
    rewrite Hslw.
    destruct (decide (pos + j < length units)%nat) as [Hjlt | Hjge].
    + rewrite (bool_decide_eq_true_2 (uint.Z (W64 (pos + j)%nat) < uint.Z (W64 (length units)))); last word.
      destruct (lookup_lt_is_Some_2 units (pos + j) Hjlt) as [b Hb].
      wp_auto.
      rewrite decide_True; last word.
      wp_apply (wp_load_slice_index with "[$Hs]").
      { word. }
      { iPureIntro. replace (Z.to_nat (sint.Z (W64 (pos + j)%nat))) with (pos + j)%nat by word. exact Hb. }
      iIntros "Hs". wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hres $Hrescap $Hs2]").
      iIntros (res') "(Hres & Hrescap & _)". wp_auto. wp_for_post.
      iFrame "Hcap HΦ Hsl".
      iExists (S j), res'.
      replace (w64_word_instance.(word.add) (W64 (pos + j)%nat) (W64 1)) with (W64 (pos + S j)%nat) by word.
      rewrite (take_S_r (drop pos units) j b); last by rewrite lookup_drop.
      rewrite app_assoc. iFrame "Hresult Hres Hrescap Hposition Hs_ptr Hs". iPureIntro. lia.
    + rewrite (bool_decide_eq_false_2 (uint.Z (W64 (pos + j)%nat) < uint.Z (W64 (length units)))); last word.
      wp_auto.
      have Hsome : apply_delta delta units = Some (out ++ drop pos units).
      { rewrite /apply_delta Hrun //. }
      rewrite Hsome in Hpatch. injection Hpatch as Hstr'.
      have Htk : take j (drop pos units) = drop pos units by (apply take_ge; rewrite length_drop; lia).
      iEval (rewrite Htk Hstr') in "Hres".
      iApply ("HΦ" $! resj). iFrame "Hs Hres Hrescap". iExists vs. iFrame "Hsl Hcap". iExact "Hdenote".
Qed.

End delta_apply.
