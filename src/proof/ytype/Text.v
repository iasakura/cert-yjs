(** [wp_yType__Text]: the visible-text read, a left-to-right walk over the
    item DLL appending the content of every non-tombstoned node to a fresh
    slice (issue #125). Read-only on the type, so stated at a generic [dq];
    the slice returned holds the pure [visible_string] of the cell model,
    which is what ties [Text.CodeUnits] to the snapshot the read lock
    exposes, and it is the caller's own (full ownership and capacity).

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

Lemma wp_yType__Text (parent : loc) (dq : dfrac) (ls : list loc) (tm : type_model) :
  {{{ is_pkg_init yjs ∗ own_ytype parent dq ls tm }}}
    parent @! (go.PointerType yjs.yType) @! "Text" #()
  {{{ (sl : slice.t), RET #sl;
      own_ytype parent dq ls tm ∗
      sl ↦* visible_string (runs_model (tm_runs tm)) ∗
      own_slice_cap w16 sl (DfracOwn 1) }}}.
Proof.
  wp_start as "Hyt".
  destruct tm as [runs]. simpl.
  iNamed "Hyt".
  iDestruct (own_dll_headptr with "Hdll") as "[%Hhd Hdll]".
  have Hhead : yt.(yjs.yType.start') = loc_at ls 0.
  { rewrite Hhd /loc_at. case_decide as Hd0; last lia.
    rewrite /= head_lookup //. }
  wp_auto.
  (* the walk: [result] holds the visible code units of the runs before the
     cursor, a fresh slice the walk owns and appends to *)
  iAssert (∃ (k : nat) (sl : slice.t),
    "Hp" ∷ parent ↦{dq} yt ∗
    "Hdll" ∷ own_dll dq parent yt.(yjs.yType.start') tl null null ls runs ∗
    "Hresult" ∷ result_ptr ↦ sl ∗
    "Hsl" ∷ sl ↦* visible_string (runs_model (take k runs)) ∗
    "Hslcap" ∷ own_slice_cap w16 sl (DfracOwn 1) ∗
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
  - (* cur is not null: read the node, append its content when visible, advance *)
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
    have Hcontold : content <$> run_items r = explode (items_string (run_items r)) := Hpck.
    iEval (rewrite -Hcloc) in "Hcur".
    rewrite decide_True; [| reflexivity].
    wp_auto.
    wp_apply (wp_item__Deleted lk dq itemVal with "[$Hcval]"). iIntros "Hcval".
    rewrite (flags_if_deleted itemVal (run_deleted r) Hflags).
    destruct (run_deleted r) eqn:Hd; simpl negb.
    + (* tombstone: contributes nothing *)
      wp_auto.
      iAssert (own_item_node lk dq (input_of_run r) true parent prevk nxtk)
        with "[Hcval Hcol Hcor]" as "Hnode".
      { iExists itemVal, olidk, oridk. iFrame "Hcval Hcol Hcor Hcontent".
        iPureIntro. split_and!;
          [exact Hinl | exact Hinr | exact Hid | exact Hpark
          | exact Hprevk | exact Hnextk | (by rewrite Hflags ?Hd)]. }
      iDestruct ("Hback" with "Hnode") as "Hdll".
      wp_for_post.
      iFrame "HΦ". iExists (S k), sl. iFrame "Hp Hdll".
      rewrite (visible_string_take_S runs k r _ Hrk Hcontold) Hd app_nil_r.
      iFrame "Hresult Hsl Hslcap".
      rewrite Hcr. replace (Z.of_nat k + 1)%Z with (Z.of_nat (S k)) by lia.
      iFrame "Hcur". iPureIntro. lia.
    + (* visible: append the node's code units, read through its read-only share *)
      wp_auto.
      wp_apply (wp_slice_append with "[Hsl Hslcap]"); first (iFrame "Hsl Hslcap"; iExact "Hcontent").
      iIntros (sl') "(Hsl' & Hslcap' & _)".
      wp_auto.
      iAssert (own_item_node lk dq (input_of_run r) false parent prevk nxtk)
        with "[Hcval Hcol Hcor]" as "Hnode".
      { iExists itemVal, olidk, oridk. iFrame "Hcval Hcol Hcor Hcontent".
        iPureIntro. split_and!;
          [exact Hinl | exact Hinr | exact Hid | exact Hpark
          | exact Hprevk | exact Hnextk | (by rewrite Hflags ?Hd)]. }
      iDestruct ("Hback" with "Hnode") as "Hdll".
      wp_for_post.
      iFrame "HΦ". iExists (S k), sl'. iFrame "Hp Hdll".
      rewrite (visible_string_take_S runs k r _ Hrk Hcontold) Hd.
      iFrame "Hresult Hsl' Hslcap'".
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
    iFrame "Hsl Hslcap".
    iExists yt, tl. iFrame "Hp Hdll".
    iPureIntro. exact Hlen.
Qed.

End ytype.
