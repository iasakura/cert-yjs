(** WP proofs for the sync-protocol execution core (yjs/sync.go): the pure
    decision logic of y-octo's [get_state_vector] / [diff_state_vector], extracted
    so it is provable in isolation from the byte codec (yjs/protocol.go, which is
    the unverified rind, //go:build !goose). This mirrors how [scanConflicts] /
    [findIntegrationLeft] were split out of Integrate.

    Verified here (input -> execution -> output):
    - [wp_computeStateVector]: from the document's decoded item list, build the
      state vector [state_vector_model] (per client, one past its largest clock);
    - [wp_computeDiff]: from the item list and a remote state vector, select
      exactly the structs the peer is missing ([diff_model] = a filter);
    - capstone [diff_of_own_state_vector_empty]: a replica's own state vector
      covers its own document, so diffing against it yields nothing (Step1 against
      yourself sends an empty Step2). This is the correctness meaning of the two
      functions composed.

    The Step2/Update execution (applying a received update) is the already-proven
    [wp_store__applyUpdate] (yjs_store.v). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common.
From iris.algebra Require Import gmap.

Local Open Scope Z_scope.

Section sync.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

(* ===================================================================== *)
(* Pure models                                                            *)
(* ===================================================================== *)

(** The (client, clock) of a decoded struct, read off its id. *)
Definition ui_client (u : yjs.updateItem.t) : w64 := u.(yjs.updateItem.id').(yjs.id.clientId').
Definition ui_clock  (u : yjs.updateItem.t) : w64 := u.(yjs.updateItem.id').(yjs.id.clock').

(** A state vector is a [gmap w64 w64]; a client absent from it reads as 0
    (y-octo: StateVector::get). *)
Definition sv_get (sv : gmap w64 w64) (c : w64) : w64 := default (W64 0) (sv !! c).

(** The effect of [svSetMax] on the model: raise [sv c] to [v] when larger. *)
Definition sv_set_max (sv : gmap w64 w64) (c v : w64) : gmap w64 w64 :=
  if decide (uint.Z (sv_get sv c) < uint.Z v) then <[c := v]> sv else sv.

(** [computeStateVector]'s model: fold each item's next clock (clock+1) in. *)
Definition sv_step (sv : gmap w64 w64) (u : yjs.updateItem.t) : gmap w64 w64 :=
  sv_set_max sv (ui_client u) (word.add (ui_clock u) (W64 1)).

Definition state_vector_model (items : list yjs.updateItem.t) : gmap w64 w64 :=
  foldl sv_step ∅ items.

(** [computeDiff]'s model: keep exactly the structs the peer is missing, i.e.
    whose clock is at or beyond what [sv] records for its client. *)
Definition ui_missing (sv : gmap w64 w64) (u : yjs.updateItem.t) : Prop :=
  (uint.Z (sv_get sv (ui_client u)) <= uint.Z (ui_clock u))%Z.

Global Instance ui_missing_dec sv u : Decision (ui_missing sv u).
Proof. rewrite /ui_missing. apply _. Defined.

Definition diff_model (sv : gmap w64 w64) (items : list yjs.updateItem.t) : list yjs.updateItem.t :=
  filter (ui_missing sv) items.

(* ----- characterization of the diff (the output spec) ----------------- *)

Lemma diff_model_spec (sv : gmap w64 w64) (items : list yjs.updateItem.t) (u : yjs.updateItem.t) :
  u ∈ diff_model sv items <->
  (u ∈ items /\ (uint.Z (sv_get sv (ui_client u)) <= uint.Z (ui_clock u))%Z).
Proof.
  rewrite /diff_model list_elem_of_filter /ui_missing. tauto.
Qed.

(* ----- state-vector monotonicity + coverage --------------------------- *)

Lemma sv_get_set_max_mono (sv : gmap w64 w64) (c v c' : w64) :
  (uint.Z (sv_get sv c') <= uint.Z (sv_get (sv_set_max sv c v) c'))%Z.
Proof.
  rewrite /sv_set_max /sv_get. case_decide as Hlt; [| lia].
  destruct (decide (c' = c)) as [->|Hne].
  - rewrite lookup_insert_eq /=. lia.
  - rewrite lookup_insert_ne //.
Qed.

Lemma sv_get_set_max_hit (sv : gmap w64 w64) (c v : w64) :
  (uint.Z v <= uint.Z (sv_get (sv_set_max sv c v) c))%Z.
Proof.
  rewrite /sv_set_max /sv_get. case_decide as Hlt.
  - rewrite lookup_insert_eq /=. lia.
  - lia.
Qed.

Lemma sv_get_foldl_mono (l : list yjs.updateItem.t) (sv : gmap w64 w64) (c : w64) :
  (uint.Z (sv_get sv c) <= uint.Z (sv_get (foldl sv_step sv l) c))%Z.
Proof.
  revert sv. induction l as [|u l' IH]; intros sv; simpl; [lia|].
  eapply Z.le_trans; [| exact (IH (sv_step sv u))].
  rewrite /sv_step. apply sv_get_set_max_mono.
Qed.

(** Every item is covered by the state vector built from its own document:
    the state vector's entry for the item's client strictly exceeds its clock. *)
Lemma state_vector_model_covers (items : list yjs.updateItem.t) (u : yjs.updateItem.t) :
  (forall w, w ∈ items -> (uint.Z (ui_clock w) + 1 < 2^64)%Z) ->
  u ∈ items ->
  (uint.Z (ui_clock u) < uint.Z (sv_get (state_vector_model items) (ui_client u)))%Z.
Proof.
  intros Hnowrap Hu.
  apply list_elem_of_split in Hu as (l1 & l2 & ->).
  rewrite /state_vector_model foldl_app /=.
  set (sv0 := foldl sv_step ∅ l1).
  set (sv1 := sv_step sv0 u).
  eapply Z.lt_le_trans; [| exact (sv_get_foldl_mono l2 sv1 (ui_client u))].
  (* sv1's entry for u's client is at least u.clock + 1 *)
  have Hhit : (uint.Z (word.add (ui_clock u) (W64 1))
                <= uint.Z (sv_get sv1 (ui_client u)))%Z
    by (rewrite /sv1 /sv_step; apply sv_get_set_max_hit).
  have Hnw : (uint.Z (ui_clock u) + 1 < 2^64)%Z
    by (apply Hnowrap; apply elem_of_app; right; left).
  have Hadd : uint.Z (word.add (ui_clock u) (W64 1)) = (uint.Z (ui_clock u) + 1)%Z by word.
  lia.
Qed.

(** No item of the document is missing from its own state vector, so the diff is
    empty. This is the correctness statement of the two functions composed. *)
Lemma filter_no_elem {A} (P : A -> Prop) `{!forall x, Decision (P x)} (l : list A) :
  (forall x, x ∈ l -> ¬ P x) -> filter P l = [].
Proof.
  induction l as [|x l' IH]; intros Hno; [done|].
  rewrite filter_cons. rewrite decide_False.
  - apply IH. intros y Hy. apply Hno. by right.
  - apply Hno. by left.
Qed.

Lemma diff_of_own_state_vector_empty (items : list yjs.updateItem.t) :
  (forall u, u ∈ items -> (uint.Z (ui_clock u) + 1 < 2^64)%Z) ->
  diff_model (state_vector_model items) items = [].
Proof.
  intros Hnowrap. rewrite /diff_model. apply filter_no_elem.
  intros u Hu. rewrite /ui_missing.
  have := state_vector_model_covers items u Hnowrap Hu. lia.
Qed.

(* ===================================================================== *)
(* WP specs                                                               *)
(* ===================================================================== *)

(** [svGet]: read [sv c], defaulting to 0 (y-octo: StateVector::get). *)
Lemma wp_svGet (svref : loc) (dq : dfrac) (sv : gmap w64 w64) (c : w64) :
  {{{ is_pkg_init yjs ∗ own_map svref dq sv }}}
    @! yjs.svGet #svref #c
  {{{ RET #(sv_get sv c); own_map svref dq sv }}}.
Proof.
  wp_start as "Hm". wp_auto.
  wp_apply (wp_map_lookup2 with "Hm") as "Hm".
  destruct (sv !! c) as [v|] eqn:Hc.
  - rewrite bool_decide_eq_true_2; [| by eauto].
    wp_auto. rewrite /sv_get Hc /=. by iApply "HΦ".
  - rewrite bool_decide_eq_false_2; [| by intros [? ?]].
    wp_auto. rewrite /sv_get Hc /=. by iApply "HΦ".
Qed.

(** [svSetMax]: raise [sv c] to [clk] when larger (y-octo: StateVector::set_max). *)
Lemma wp_svSetMax (svref : loc) (sv : gmap w64 w64) (c clk : w64) :
  {{{ is_pkg_init yjs ∗ own_map svref (DfracOwn 1) sv }}}
    @! yjs.svSetMax #svref #c #clk
  {{{ RET #(); own_map svref (DfracOwn 1) (sv_set_max sv c clk) }}}.
Proof.
  wp_start as "Hm". wp_auto.
  wp_apply (wp_svGet with "[$Hm]") as "Hm".
  case_bool_decide as Hlt.
  - wp_auto. wp_apply (wp_map_insert with "Hm") as "Hm".
    rewrite /sv_set_max decide_True; [| exact Hlt]. by iApply "HΦ".
  - wp_auto. rewrite /sv_set_max decide_False; [| exact Hlt]. by iApply "HΦ".
Qed.

(** [computeStateVector]: build the document's state vector from its item list. *)
Lemma wp_computeStateVector (s : slice.t) (dq : dfrac) (items : list yjs.updateItem.t) :
  {{{ is_pkg_init yjs ∗ s ↦*{dq} items }}}
    @! yjs.computeStateVector #s
  {{{ (mref : loc), RET #mref;
      s ↦*{dq} items ∗ own_map mref (DfracOwn 1) (state_vector_model items) }}}.
Proof.
  wp_start as "Hsl".
  wp_auto.
  wp_apply wp_map_make1 as "%mref Hmap".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  iAssert (∃ (i : w64),
    "Hi" ∷ i_ptr ↦ i ∗ "Hitems" ∷ items_ptr ↦ s ∗ "Hsv" ∷ sv_ptr ↦ mref ∗
    "Hsl" ∷ s ↦*{dq} items ∗
    "Hmap" ∷ own_map mref (DfracOwn 1) (state_vector_model (take (uint.nat i) items)) ∗
    "%Hile" ∷ ⌜(uint.Z i <= Z.of_nat (length items))%Z⌝)%I
    with "[i items sv Hsl Hmap]" as "IH".
  { iExists (W64 0). iFrame. word. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - have Hilt : (uint.nat i < length items)%nat by word.
    destruct (items !! uint.nat i) as [u|] eqn:Hu; [| apply lookup_ge_None in Hu; lia].
    iDestruct (own_slice_elem_acc (sint.Z i) u s dq items with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hu. }
    wp_auto.
    rewrite decide_True; [| word].
    wp_auto.
    wp_apply (wp_svSetMax with "[$Hmap]") as "Hmap".
    iDestruct ("Hgive" $! u with "Hel") as "Hsl".
    rewrite list_insert_id; [| replace (sint.nat i) with (uint.nat i) by word; exact Hu].
    wp_for_post.
    iFrame "HΦ".
    iExists (word.add i (W64 1)).
    iFrame "Hi Hitems Hsv Hsl".
    have Hstep : state_vector_model (take (uint.nat (word.add i (W64 1))) items)
               = sv_set_max (state_vector_model (take (uint.nat i) items))
                   (ui_client u) (word.add (ui_clock u) (W64 1)).
    { have Hi1 : uint.nat (word.add i (W64 1)) = S (uint.nat i) by word.
      rewrite Hi1 (take_S_r items (uint.nat i) u Hu).
      rewrite /state_vector_model foldl_app /=. rewrite /sv_step //. }
    iSplitL "Hmap".
    { rewrite Hstep /ui_client /ui_clock. iFrame "Hmap". }
    iPureIntro. word.
  - wp_auto.
    have Hieq : uint.nat i = length items by word.
    rewrite Hieq take_ge; [| lia].
    iApply "HΦ". iFrame.
Qed.

(** [computeDiff]: select exactly the structs a peer with state vector [sv] is
    missing (y-octo: diff_state_vectors + diff_structs, 1-char subset). *)
Lemma wp_computeDiff (s : slice.t) (dq : dfrac) (items : list yjs.updateItem.t)
    (svref : loc) (dqsv : dfrac) (sv : gmap w64 w64) :
  {{{ is_pkg_init yjs ∗ s ↦*{dq} items ∗ own_map svref dqsv sv }}}
    @! yjs.computeDiff #s #svref
  {{{ (out : slice.t), RET #out;
      s ↦*{dq} items ∗ own_map svref dqsv sv ∗
      out ↦* (diff_model sv items) ∗ own_slice_cap yjs.updateItem.t out (DfracOwn 1) }}}.
Proof.
  wp_start as "(Hsl & Hmap)".
  wp_auto.
  wp_apply wp_slice_literal.
  iSplitR; first done.
  iIntros "%out0 [Hout Houtcap]".
  wp_auto.
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  iAssert (∃ (i : w64) (out : slice.t),
    "Hi" ∷ i_ptr ↦ i ∗ "Hitems" ∷ items_ptr ↦ s ∗ "Hsv" ∷ sv_ptr ↦ svref ∗
    "Hdiff" ∷ diff_ptr ↦ out ∗
    "Hsl" ∷ s ↦*{dq} items ∗ "Hmap" ∷ own_map svref dqsv sv ∗
    "Hout" ∷ out ↦* (diff_model sv (take (uint.nat i) items)) ∗
    "Houtcap" ∷ own_slice_cap yjs.updateItem.t out (DfracOwn 1) ∗
    "%Hile" ∷ ⌜(uint.Z i <= Z.of_nat (length items))%Z⌝)%I
    with "[i items sv diff Hsl Hmap Hout Houtcap]" as "IH".
  { iExists (W64 0), _. iFrame. word. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - have Hilt : (uint.nat i < length items)%nat by word.
    destruct (items !! uint.nat i) as [u|] eqn:Hu; [| apply lookup_ge_None in Hu; lia].
    iDestruct (own_slice_elem_acc (sint.Z i) u s dq items with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hu. }
    wp_auto.
    rewrite decide_True; [| word].
    wp_auto.
    wp_apply (wp_svGet with "[$Hmap]") as "Hmap".
    case_bool_decide as Hmiss.
    + (* item missing: append it to the diff *)
      wp_auto.
      rewrite decide_True; [| word].
      wp_auto.
      wp_apply wp_slice_literal.
      iSplitR; first done.
      iIntros "%s1 [Hs1 _]".
      wp_auto.
      wp_apply (wp_slice_append with "[$Hout $Houtcap $Hs1]") as "%out' (Hout & Houtcap & _)".
      have Hz0 : forall (z : yjs.updateItem.t), <[sint.nat (W64 0):=u]> [z] = [u].
      { intro z. have Hz : sint.nat (W64 0) = 0%nat by word. rewrite Hz //. }
      iEval (rewrite Hz0) in "Hout".
      iDestruct ("Hgive" $! u with "Hel") as "Hsl".
      rewrite list_insert_id; [| replace (sint.nat i) with (uint.nat i) by word; exact Hu].
      wp_for_post.
      iFrame "HΦ".
      iExists (word.add i (W64 1)), out'.
      iFrame "Hi Hitems Hsv Hdiff Hsl Hmap Houtcap".
      have Hfu : filter (ui_missing sv) [u] = [u].
      { rewrite filter_cons decide_True; last (rewrite /ui_missing; exact Hmiss).
        by rewrite filter_nil. }
      have Hnext : diff_model sv (take (uint.nat (word.add i (W64 1))) items)
                 = diff_model sv (take (uint.nat i) items) ++ [u].
      { have Hi1 : uint.nat (word.add i (W64 1)) = S (uint.nat i) by word.
        rewrite Hi1 (take_S_r items (uint.nat i) u Hu) /diff_model filter_app Hfu //. }
      rewrite Hnext. iFrame "Hout". iPureIntro. word.
    + (* item already known: skip *)
      wp_auto.
      iDestruct ("Hgive" $! u with "Hel") as "Hsl".
      rewrite list_insert_id; [| replace (sint.nat i) with (uint.nat i) by word; exact Hu].
      wp_for_post.
      iFrame "HΦ".
      iExists (word.add i (W64 1)), out.
      iFrame "Hi Hitems Hsv Hdiff Hsl Hmap Houtcap".
      have Hfu : filter (ui_missing sv) [u] = [].
      { rewrite filter_cons decide_False; last (rewrite /ui_missing; exact Hmiss).
        by rewrite filter_nil. }
      have Hnext : diff_model sv (take (uint.nat (word.add i (W64 1))) items)
                 = diff_model sv (take (uint.nat i) items).
      { have Hi1 : uint.nat (word.add i (W64 1)) = S (uint.nat i) by word.
        rewrite Hi1 (take_S_r items (uint.nat i) u Hu) /diff_model filter_app Hfu app_nil_r //. }
      rewrite Hnext. iFrame "Hout". iPureIntro. word.
  - wp_auto.
    have Hieq : uint.nat i = length items by word.
    rewrite Hieq take_ge; [| lia].
    iApply "HΦ". iFrame.
Qed.

End sync.
