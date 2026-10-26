(** [wp_yType__Snapshot]: the per-char read with ids, a left-to-right walk
    over the item DLL that reports, for every char of every node, the id it
    carries, its node's tombstone bit and its code unit ([Text.Snapshot],
    issue #239). Read-only on the type, so stated at a generic [dq]; the
    slice returned ([own_snapshot_chars]) holds the [SnapshotChar] values of
    the cell model, which is what ties [Text.Snapshot] to the snapshot the
    read lock exposes, and it is the caller's own (full ownership and
    capacity).

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

Lemma wp_yType__Snapshot (parent : loc) (dq : dfrac) (ls : list loc) (tm : type_model) :
  {{{ is_pkg_init yjs ∗ own_ytype parent dq ls tm }}}
    parent @! (go.PointerType yjs.yType) @! "Snapshot" #()
  {{{ (sl : slice.t), RET #sl;
      own_ytype parent dq ls tm ∗
      own_snapshot_chars sl (DfracOwn 1) (runs_model (tm_runs tm)) }}}.
Proof.
  wp_start as "Hyt".
  destruct tm as [runs]. simpl.
  iNamed "Hyt".
  iDestruct (own_dll_headptr with "Hdll") as "[%Hhd Hdll]".
  have Hhead : yt.(yjs.yType.start') = loc_at ls 0.
  { rewrite Hhd /loc_at. case_decide as Hd0; last lia.
    rewrite /= head_lookup //. }
  wp_auto.
  (* the outer walk: [result] holds the chars of the runs before the cursor *)
  iAssert (∃ (k : nat) (sl : slice.t),
    "Hp" ∷ parent ↦{dq} yt ∗
    "Hdll" ∷ own_dll dq parent yt.(yjs.yType.start') tl null null ls runs ∗
    "Hresult" ∷ result_ptr ↦ sl ∗
    "Hsl" ∷ sl ↦* snapshot_chars (runs_model (take k runs)) ∗
    "Hslcap" ∷ own_slice_cap yjs.SnapshotChar.t sl (DfracOwn 1) ∗
    "Hcur" ∷ cur_ptr ↦ loc_at ls (Z.of_nat k) ∗
    "%Hk" ∷ ⌜(k <= length runs)%nat⌝)%I
    with "[Hparent Hdll result cur]" as "IH".
  { iExists 0%nat, slice.nil. rewrite take_0 /= -Hhead. iFrame "Hparent Hdll result cur".
    iSplitL; first iApply own_slice_nil.
    iSplitL; first iApply own_slice_cap_nil.
    iPureIntro; lia. }
  wp_for "IH".
  iDestruct (own_dll_length with "Hdll") as %Hlenl.
  destruct (decide (k < length runs)%nat) as [Hlt | Hge].
  - (* cur is not null: read the node, walk its chars, advance *)
    iDestruct (loc_at_lt_not_null dq parent yt.(yjs.yType.start') tl ls runs k ltac:(lia) with "Hdll")
      as "[%Hnn Hdll]".
    rewrite (bool_decide_eq_false_2 (loc_at ls (Z.of_nat k) = null) Hnn).
    simpl negb.
    destruct (ls !! k) as [lk|] eqn:Hlk; [| apply lookup_ge_None in Hlk; lia].
    destruct (runs !! k) as [r|] eqn:Hrk; [| apply lookup_ge_None in Hrk; lia].
    iDestruct (own_dll_acc dq parent yt.(yjs.yType.start') tl ls runs k lk r Hlk Hrk with "Hdll")
      as (prevk nxtk) "(%Hcl & %Hcrn & %Hrun & %Hpck & %Hclen & Hnode & Hback)".
    iDestruct "Hnode" as (itemVal olidk oridk)
      "(Hcval & Hcol & Hcor & %Hinl & %Hinr & %Hid & #Hcontent & %Hpark & %Hprevk & %Hnextk & %Hflags)".
    have Hcloc : lk = loc_at ls (Z.of_nat k).
    { rewrite /loc_at decide_True; last lia. rewrite Nat2Z.id Hlk //. }
    have Hcr : itemVal.(yjs.item.right') = loc_at ls (Z.of_nat k + 1).
    { rewrite Hnextk. exact Hcrn. }
    iEval (rewrite -Hcloc) in "Hcur".
    rewrite decide_True; [| reflexivity].
    wp_auto.
    wp_apply (wp_item__Deleted lk dq itemVal with "[$Hcval]"). iIntros "Hcval".
    rewrite (flags_if_deleted itemVal (run_deleted r) Hflags).
    wp_auto.
    (* the inner walk over the node's code units: [result] grows by one
       reported char per unit, the run's head id advanced by the offset *)
    iAssert (∃ (j : nat) (sl' : slice.t),
      "Hresult" ∷ result_ptr ↦ sl' ∗
      "Hsl" ∷ sl' ↦* (snapshot_chars (runs_model (take k runs)) ++
                       snapshot_chars (take j (run_models r))) ∗
      "Hslcap" ∷ own_slice_cap yjs.SnapshotChar.t sl' (DfracOwn 1) ∗
      "Hj" ∷ k_ptr ↦ W64 (Z.of_nat j) ∗
      "%Hj" ∷ ⌜(j <= length (run_items r))%nat⌝)%I
      with "[Hresult Hsl Hslcap k]" as "IHin".
    { iExists 0%nat, sl. rewrite take_0 /= app_nil_r. iFrame "Hresult Hsl Hslcap k".
      iPureIntro; lia. }
    wp_for "IHin".
    iEval (rewrite /is_content) in "Hcontent".
    iDestruct (own_slice_len with "Hcontent") as %[Hulen Hulenz].
    case_bool_decide as Hjlt.
    { (* one more char: the [j]-th unit of the node's content *)
      have Hjpos : (j < length (run_items r))%nat.
      { rewrite -Hclen. move: Hjlt Hulen. rewrite /input_of_run /=. word. }
      destruct (lookup_lt_is_Some_2 (run_items r) j Hjpos) as [x Hx].
      destruct (lookup_lt_is_Some_2 (items_string (run_items r)) j ltac:(lia)) as [u Hu].
      wp_auto.
      rewrite (decide_True (P := (0 ≤ sint.Z (W64 j) < sint.Z itemVal.(yjs.item.content').(yjs.content.content').(slice.len))%Z)); last word.
      wp_apply (wp_load_slice_index with "[$Hcontent]").
      { word. }
      { iPureIntro. rewrite /input_of_run /= in Hulen |- *.
        have Hjeq : sint.nat (W64 j) = j by word.
        rewrite Hjeq. exact Hu. }
      iIntros "_".
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "%bsl [Hbsl _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hsl $Hslcap $Hbsl]").
      iIntros (sl'') "(Hsl'' & Hslcap'' & _)".
      wp_auto.
      wp_for_post.
      iFrame "HΦ Hp Hcur Hcol Hcor Hback deleted Hcval units".
      iExists (S j), sl''. iFrame "Hresult Hslcap''".
      iSplitL "Hsl''".
      { rewrite (run_models_take_S r j x Hx) snapshot_chars_app -app_assoc.
        iExactEq "Hsl''". f_equal. f_equal.
        rewrite /snapshot_chars /= (snapshot_char_run r j x u Hrun Hpck Hx Hu).
        replace (sint.nat (W64 0)) with 0%nat by word. simpl.
        f_equal.
        have Hcid : (input_of_run r).(in_id) = item_id (run_head_item r) by done.
        rewrite Hcid /toYjsId in Hid.
        have Hclient : W64 (run_client r) = itemVal.(yjs.item.id').(yjs.id.clientId').
        { rewrite /run_client -Hid /=. word. }
        have Hclock : W64 (run_clock r) = itemVal.(yjs.item.id').(yjs.id.clock').
        { rewrite /run_clock -Hid /=. word. }
        rewrite Hclient Hclock. done. }
      iSplitL "Hj".
      { replace (w64_word_instance.(word.add) (W64 j) (W64 1)) with (W64 (S j)) by word.
        iFrame "Hj". }
      iPureIntro; lia. }
    (* every unit reported: advance to the next node *)
    have Hjeq : j = length (run_items r).
    { rewrite /input_of_run /= in Hulen. move: Hjlt Hj Hulen Hclen. word. }
    wp_auto.
    iAssert (is_content itemVal.(yjs.item.content') (in_content (input_of_run r)))
      with "[]" as "#Hcontent2".
    { rewrite /is_content. iFrame "Hcontent". }
    iAssert (own_item_node lk dq (input_of_run r) (run_deleted r) parent prevk nxtk)
      with "[Hcval Hcol Hcor]" as "Hnode".
    { iExists itemVal, olidk, oridk. iFrame "Hcval Hcol Hcor Hcontent2".
      iPureIntro. split_and!;
        [exact Hinl | exact Hinr | exact Hid | exact Hpark | exact Hprevk | exact Hnextk
        | exact Hflags]. }
    iDestruct ("Hback" with "Hnode") as "Hdll".
    wp_for_post.
    iFrame "HΦ". iExists (S k), sl'. iFrame "Hp Hdll".
    rewrite (snapshot_chars_take_S runs k r Hrk) Hjeq.
    have Hlenrm : length (run_models r) = length (run_items r).
    { rewrite /run_models length_fmap //. }
    rewrite (take_ge (run_models r)); last lia.
    iFrame "Hresult Hsl Hslcap".
    rewrite Hcr. replace (Z.of_nat k + 1)%Z with (Z.of_nat (S k)) by lia.
    iFrame "Hcur". iPureIntro. lia.
  - (* cur is null: the walk is done, return the accumulated slice *)
    have Hkeq : k = length runs by lia.
    have Hnull : loc_at ls (Z.of_nat k) = null.
    { rewrite /loc_at decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
    rewrite (bool_decide_eq_true_2 (loc_at ls (Z.of_nat k) = null) Hnull).
    simpl negb.
    rewrite decide_False; [| done]. rewrite decide_True; [| done].
    wp_auto.
    have Htk : take k runs = runs by (rewrite Hkeq take_ge //).
    iEval (rewrite Htk) in "Hsl".
    iApply ("HΦ" $! sl).
    iSplitR "Hsl Hslcap"; last (rewrite /own_snapshot_chars; iFrame "Hsl Hslcap").
    iExists yt, tl. iFrame "Hp Hdll".
    iPureIntro. exact Hlen.
Qed.

End ytype.
