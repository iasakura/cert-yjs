(** [wp_ApplyDelta]: the application-side patch (issue #198). Pure over its
    two arguments: it returns [apply_delta delta s] and whether it succeeded;
    a delta a [Poll] returned always does ([apply_text_delta]). The delta
    must fit ([delta_fits]: the Go compares [uint64] counts), which a delta
    that patches a Go string does ([apply_delta_fits]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.github_com.mit_pdos.perennial.goose.model Require Import strings.
From New.proof.textobserver Require Import model value heap.

Section text_observer.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

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

Lemma wp_ApplyDelta (str : go_string) (sl : slice.t) (dq : dfrac) (delta : list DeltaOp) :
  {{{ is_pkg_init yjs ∗ own_delta sl dq delta ∗ ⌜delta_fits delta⌝ }}}
    @! yjs.ApplyDelta #str #sl
  {{{ RET (#(default ""%go (apply_delta delta str)), #(bool_decide (is_Some (apply_delta delta str))));
      own_delta sl dq delta }}}.
Proof.
  wp_start as "[Hdelta %Hfits]". iNamed "Hdelta".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  have Hlenvs : length vs = length delta := Forall2_length Hdenote.
  wp_auto.
  wp_apply wp_string_len. iIntros "%Hstrlen".
  wp_auto.
  (* the outer loop: the ops before [k] ran the string to [drop pos str] *)
  iAssert (∃ (k pos : nat) (out : go_string),
    "Hk" ∷ k_ptr ↦ W64 k ∗
    "Hresult" ∷ result_ptr ↦ out ∗
    "Hposition" ∷ position_ptr ↦ W64 pos ∗
    "Hremaining" ∷ remaining_ptr ↦ W64 (Z.of_nat (length str - pos)) ∗
    "Hs" ∷ s_ptr ↦ str ∗
    "Hdelta" ∷ delta_ptr ↦ sl ∗
    "Hsl" ∷ sl ↦*{dq} vs ∗
    "%Hkle" ∷ ⌜(k <= length delta)%nat⌝ ∗
    "%Hposle" ∷ ⌜(pos <= length str)%nat⌝ ∗
    "%Hrun" ∷ ⌜delta_run (take k delta) str = Some (out, drop pos str)⌝)%I
    with "[k result position remaining s delta Hsl]" as "IH".
  { iExists 0%nat, 0%nat, ""%go. rewrite Nat.sub_0_r drop_0.
    iFrame "k result position remaining s delta Hsl". iPureIntro. split_and!; [lia | lia | done]. }
  wp_for "IH".
  destruct (decide (k < length delta)%nat) as [Hklt | Hkge].
  - (* one more op *)
    rewrite (bool_decide_eq_true_2 (sint.Z (W64 k) < sint.Z sl.(slice.len))); last word.
    destruct (lookup_lt_is_Some_2 vs k ltac:(lia)) as [opv Hopv].
    destruct (lookup_lt_is_Some_2 delta k Hklt) as [op Hop].
    have Hden : delta_op_denotes opv op := Forall2_lookup_lr _ _ _ _ _ _ Hdenote Hopv Hop.
    wp_auto.
    rewrite decide_True; last word.
    iDestruct (own_slice_elem_acc (sint.Z (W64 k)) opv sl dq vs with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z (W64 k))) with k by word. exact Hopv. }
    wp_auto.
    iDestruct ("Hgive" $! opv with "Hel") as "Hsl".
    rewrite list_insert_id; last (replace (Z.to_nat (sint.Z (W64 k))) with k by word; exact Hopv).
    have Hopfits : delta_op_fits op := Forall_lookup_1 _ _ _ _ Hfits Hop.
    destruct op as [n | t | n]; destruct Hden as [Hkind Hval]; simpl in Hopfits.
    + (* retain [n] chars *)
      have HL : uint.Z opv.(yjs.DeltaOp.Length') = Z.of_nat n by rewrite Hval; word.
      rewrite Hkind. wp_auto.
      destruct (decide (n <= length str - pos)%nat) as [Hle | Hgt]; last first.
      { (* overrun: the patch fails *)
        rewrite (bool_decide_eq_true_2 (uint.Z (W64 (length str - pos)%nat) < uint.Z opv.(yjs.DeltaOp.Length'))); last word.
        wp_auto. wp_for_post.
        have Hnone : apply_delta delta str = None.
        { rewrite /apply_delta (delta_run_overrun delta k n out (drop pos str) str (or_introl Hop) Hrun) //.
          rewrite length_drop. lia. }
        iEval (rewrite Hnone (bool_decide_eq_false_2 (is_Some (@None A)) ltac:(by move=> [x Hx])) /=) in "HΦ".
        iApply "HΦ". iExists vs. iFrame "Hsl Hcap". done. }
      rewrite (bool_decide_eq_false_2 (uint.Z (W64 (length str - pos)%nat) < uint.Z opv.(yjs.DeltaOp.Length'))); last word.
      wp_auto.
      rewrite Hkind (bool_decide_eq_true_2 (W8 0 = W8 0)); last done.
      wp_auto.
      (* the inner loop copies the next [n] bytes *)
      iAssert (∃ (i : nat),
        "Hi" ∷ i_ptr ↦ W64 i ∗
        "Hresult" ∷ result_ptr ↦ (out ++ take i (drop pos str)) ∗
        "Hposition" ∷ position_ptr ↦ W64 pos ∗
        "Hs" ∷ s_ptr ↦ str ∗
        "Hop" ∷ op_ptr ↦ opv ∗
        "%Hile" ∷ ⌜(i <= n)%nat⌝)%I
        with "[i Hresult Hposition Hs op]" as "IHi".
      { iExists 0%nat. rewrite take_0 app_nil_r. iFrame "i Hresult Hposition Hs op". iPureIntro. lia. }
      wp_for "IHi".
      destruct (decide (i < n)%nat) as [Hilt | Hige].
      * (* one more byte *)
        rewrite (bool_decide_eq_true_2 (uint.Z (W64 i) < uint.Z opv.(yjs.DeltaOp.Length'))); last word.
        destruct (lookup_lt_is_Some_2 str (pos + i) ltac:(lia)) as [b Hb].
        wp_auto.
        replace (sint.nat (w64_word_instance.(word.add) (W64 pos) (W64 i))) with (pos + i)%nat by word.
        rewrite Hb.
        wp_auto. wp_for_post.
        iFrame "Hcap HΦ Hk Hremaining Hdelta Hsl".
        iExists (S i).
        replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
        rewrite (take_S_r (drop pos str) i b); last by rewrite lookup_drop.
        rewrite app_assoc. iFrame "Hi Hresult Hposition Hs Hop". iPureIntro. lia.
      * (* the [n] bytes are copied: advance the cursor *)
        have Hieq : i = n by word.
        subst i.
        rewrite (bool_decide_eq_false_2 (uint.Z (W64 n) < uint.Z opv.(yjs.DeltaOp.Length'))); last word.
        wp_auto. wp_for_post.
        iFrame "Hcap HΦ".
        iExists (S k), (pos + n)%nat, (out ++ take n (drop pos str)).
        replace (w64_word_instance.(word.add) (W64 k) (W64 1)) with (W64 (S k)) by word.
        replace (w64_word_instance.(word.add) (W64 pos) opv.(yjs.DeltaOp.Length')) with (W64 (Z.of_nat (pos + n))) by word.
        replace (w64_word_instance.(word.sub) (W64 (length str - pos)%nat) opv.(yjs.DeltaOp.Length')) with (W64 (Z.of_nat (length str - (pos + n)))) by word.
        iFrame "Hk Hresult Hposition Hremaining Hs Hdelta Hsl".
        iPureIntro. split_and!; [lia | lia |].
        rewrite (delta_run_take_retain delta k n out (drop pos str) str Hop Hrun); last by rewrite length_drop; lia.
        rewrite drop_drop //.
    + (* insert [t] *)
      rewrite Hkind. wp_auto. wp_for_post.
      iFrame "Hcap HΦ".
      iExists (S k), pos, (out ++ t).
      replace (w64_word_instance.(word.add) (W64 k) (W64 1)) with (W64 (S k)) by word.
      rewrite Hval. iFrame "Hk Hresult Hposition Hremaining Hs Hdelta Hsl".
      iPureIntro. split_and!; [lia | lia |].
      exact (delta_run_take_insert delta k t out (drop pos str) str Hop Hrun).
    + (* delete [n] chars *)
      have HL : uint.Z opv.(yjs.DeltaOp.Length') = Z.of_nat n by rewrite Hval; word.
      rewrite Hkind. wp_auto.
      destruct (decide (n <= length str - pos)%nat) as [Hle | Hgt]; last first.
      { rewrite (bool_decide_eq_true_2 (uint.Z (W64 (length str - pos)%nat) < uint.Z opv.(yjs.DeltaOp.Length'))); last word.
        wp_auto. wp_for_post.
        have Hnone : apply_delta delta str = None.
        { rewrite /apply_delta (delta_run_overrun delta k n out (drop pos str) str (or_intror Hop) Hrun) //.
          rewrite length_drop. lia. }
        iEval (rewrite Hnone (bool_decide_eq_false_2 (is_Some (@None A)) ltac:(by move=> [x Hx])) /=) in "HΦ".
        iApply "HΦ". iExists vs. iFrame "Hsl Hcap". done. }
      rewrite (bool_decide_eq_false_2 (uint.Z (W64 (length str - pos)%nat) < uint.Z opv.(yjs.DeltaOp.Length'))); last word.
      wp_auto.
      rewrite Hkind (bool_decide_eq_false_2 (W8 2 = W8 0)); last done.
      wp_auto. wp_for_post.
      iFrame "Hcap HΦ".
      iExists (S k), (pos + n)%nat, out.
      replace (w64_word_instance.(word.add) (W64 k) (W64 1)) with (W64 (S k)) by word.
      replace (w64_word_instance.(word.add) (W64 pos) opv.(yjs.DeltaOp.Length')) with (W64 (Z.of_nat (pos + n))) by word.
      replace (w64_word_instance.(word.sub) (W64 (length str - pos)%nat) opv.(yjs.DeltaOp.Length')) with (W64 (Z.of_nat (length str - (pos + n)))) by word.
      iFrame "Hk Hresult Hposition Hremaining Hs Hdelta Hsl".
      iPureIntro. split_and!; [lia | lia |].
      rewrite (delta_run_take_delete delta k n out (drop pos str) str Hop Hrun); last by rewrite length_drop; lia.
      rewrite drop_drop //.
  - (* every op ran: keep the rest of the string (the implicit trailing retain) *)
    rewrite (bool_decide_eq_false_2 (sint.Z (W64 k) < sint.Z sl.(slice.len))); last word.
    have Hkeq : k = length delta by word.
    rewrite Hkeq take_ge in Hrun; last lia.
    wp_auto.
    iAssert (∃ (j : nat),
      "Hresult" ∷ result_ptr ↦ (out ++ take j (drop pos str)) ∗
      "Hposition" ∷ position_ptr ↦ W64 (pos + j)%nat ∗
      "Hs" ∷ s_ptr ↦ str ∗
      "%Hjle" ∷ ⌜(pos + j <= length str)%nat⌝)%I
      with "[Hresult Hposition Hs]" as "IHj".
    { iExists 0%nat. rewrite take_0 app_nil_r Nat.add_0_r. iFrame "Hresult Hposition Hs". iPureIntro. lia. }
    wp_for "IHj".
    wp_apply wp_string_len. iIntros "%Hstrlen2".
    wp_auto.
    destruct (decide (pos + j < length str)%nat) as [Hjlt | Hjge].
    + rewrite (bool_decide_eq_true_2 (uint.Z (W64 (pos + j)%nat) < uint.Z (W64 (length str)))); last word.
      rewrite decide_True; last done.
      destruct (lookup_lt_is_Some_2 str (pos + j) Hjlt) as [b Hb].
      wp_auto.
      replace (sint.nat (W64 (pos + j)%nat)) with (pos + j)%nat by word.
      rewrite Hb.
      wp_auto. wp_for_post.
      iFrame "Hcap HΦ Hsl".
      iExists (S j).
      replace (w64_word_instance.(word.add) (W64 (pos + j)%nat) (W64 1)) with (W64 (pos + S j)%nat) by word.
      rewrite (take_S_r (drop pos str) j b); last by rewrite lookup_drop.
      rewrite app_assoc. iFrame "Hresult Hposition Hs". iPureIntro. lia.
    + rewrite (bool_decide_eq_false_2 (uint.Z (W64 (pos + j)%nat) < uint.Z (W64 (length str)))); last word.
      rewrite decide_False; last done. rewrite decide_True; last done.
      wp_auto.
      have Hsome : apply_delta delta str = Some (out ++ drop pos str).
      { rewrite /apply_delta Hrun //. }
      rewrite take_ge; last (rewrite length_drop; lia).
      iEval (rewrite Hsome (bool_decide_eq_true_2 (is_Some (Some (out ++ drop pos str))) ltac:(by eexists)) /=) in "HΦ".
      iApply "HΦ". iExists vs. iFrame "Hsl Hcap". done.
Qed.

End text_observer.
