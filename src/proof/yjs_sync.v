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
    [wp_store__applyUpdate] (yjs_store.v).

    The decoded message handler (issue #63 intermediate, at the bottom):
    [wp_syncDoc__HandleSyncMessage_Step1] (answers with the [diff_model]) and
    [wp_syncDoc__HandleSyncMessage_Apply] (no answer; the doc absorbs the batch
    and its fragment advances). Both specs are stated as changes to the
    document's *fragment*, the state vector viewed as "which updates the doc
    has" ([sv_covers]): Step1's return value is exactly the local structs the
    peer's fragment misses ([diff_model_covers] / [diff_model_subset]), and
    Apply's effect is that the fragment grows to cover [upd] while keeping what
    it had ([state_vector_model_app_covers] + [_app_grew]); one round's
    convergence is [apply_diff_covers].

    Fragment vocabulary caveat (future work): [own_syncDoc] is a standalone
    decoded item list, so the "fragment" here is the doc's own state vector,
    NOT yet the ghost history prefix [is_history_lb] (yjs_history). Tying the
    two ([sv_of] the applied ops = the delivered prefix, so the sync fragment
    IS the replica's [is_history_lb]) needs [HandleSyncMessage]'s apply branch
    to run through [store.applyUpdate] rather than appending to a raw list;
    that store integration is the remaining #51/#63 step. *)
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

(** [sv_covers sv u]: the state vector already accounts for struct [u] (its
    client's next-clock sits strictly past [u]'s clock). This is the "the doc's
    delivered fragment contains [u]" reading of a state vector, and the exact
    complement of [ui_missing] on the total order of clocks. *)
Definition sv_covers (sv : gmap w64 w64) (u : yjs.updateItem.t) : Prop :=
  (uint.Z (ui_clock u) < uint.Z (sv_get sv (ui_client u)))%Z.

Lemma sv_covers_not_missing (sv : gmap w64 w64) (u : yjs.updateItem.t) :
  sv_covers sv u <-> ¬ ui_missing sv u.
Proof. rewrite /sv_covers /ui_missing. lia. Qed.

(* ----- characterization of the diff (the return-value spec) ------------ *)

Lemma diff_model_spec (sv : gmap w64 w64) (items : list yjs.updateItem.t) (u : yjs.updateItem.t) :
  u ∈ diff_model sv items <->
  (u ∈ items /\ (uint.Z (sv_get sv (ui_client u)) <= uint.Z (ui_clock u))%Z).
Proof.
  rewrite /diff_model list_elem_of_filter /ui_missing. tauto.
Qed.

(** The diff a Step1 answer carries is EXACTLY the local structs the peer's
    state vector does not already cover: every element is a local struct the
    peer is missing, and conversely. This is the return-value characterization
    ("which updates the response contains"). *)
Lemma diff_model_covers (sv : gmap w64 w64) (items : list yjs.updateItem.t) (u : yjs.updateItem.t) :
  u ∈ diff_model sv items <-> (u ∈ items /\ ¬ sv_covers sv u).
Proof. rewrite diff_model_spec sv_covers_not_missing /ui_missing. tauto. Qed.

(** ...and it draws only from the local document (never invents structs). *)
Lemma diff_model_subset (sv : gmap w64 w64) (items : list yjs.updateItem.t) :
  ∀ u, u ∈ diff_model sv items -> u ∈ items.
Proof. move=> u. rewrite diff_model_covers. tauto. Qed.

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

(* ----- how the document fragment changes when a batch is applied ------- *)

(** Applying a batch [upd] (append) advances the document's fragment to cover
    every struct in [upd]: after the apply, the state vector accounts for each
    of them. Together with [state_vector_model_app_grew] (nothing already in
    the fragment is lost), this says the fragment grows to exactly the old
    fragment plus [upd]. *)
Lemma state_vector_model_app_covers (items upd : list yjs.updateItem.t) (u : yjs.updateItem.t) :
  (forall w, w ∈ items ++ upd -> (uint.Z (ui_clock w) + 1 < 2^64)%Z) ->
  u ∈ upd ->
  sv_covers (state_vector_model (items ++ upd)) u.
Proof.
  intros Hnowrap Hu. rewrite /sv_covers.
  apply state_vector_model_covers; [exact Hnowrap |].
  apply elem_of_app. by right.
Qed.

(** Convergence of one sync round: after replica A (document [itemsA]) applies
    the diff B answered against A's own state vector, A's fragment covers every
    struct that answer carried, i.e. exactly the structs of B that A had been
    missing. So after the round A's fragment includes B's contribution: the
    exec-core meaning of "sync makes A catch up to B". *)
Lemma apply_diff_covers (itemsA itemsB : list yjs.updateItem.t) (u : yjs.updateItem.t) :
  (forall w, w ∈ itemsA ++ diff_model (state_vector_model itemsA) itemsB ->
     (uint.Z (ui_clock w) + 1 < 2^64)%Z) ->
  u ∈ diff_model (state_vector_model itemsA) itemsB ->
  sv_covers (state_vector_model (itemsA ++ diff_model (state_vector_model itemsA) itemsB)) u.
Proof. move=> Hnowrap Hu. exact (state_vector_model_app_covers itemsA _ u Hnowrap Hu). Qed.

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

(* ===================================================================== *)
(* Decoded SyncMessage handler (issue #63 intermediate)                   *)
(* ===================================================================== *)

(** A syncDoc owns its decoded item list. *)
Definition own_syncDoc (d : loc) (items : list yjs.updateItem.t) : iProp Σ :=
  ∃ (sl : slice.t),
    "Hitems" ∷ (d .[(yjs.syncDoc.t), "items"]) ↦ sl ∗
    "Hsl" ∷ sl ↦* items ∗
    "Hcap" ∷ own_slice_cap yjs.updateItem.t sl (DfracOwn 1).

(** Applying a batch (append) only advances the state vector: never regresses. *)
Lemma state_vector_model_app_grew (items upd : list yjs.updateItem.t) (c : w64) :
  (uint.Z (sv_get (state_vector_model items) c)
     <= uint.Z (sv_get (state_vector_model (items ++ upd)) c))%Z.
Proof. rewrite /state_vector_model foldl_app. apply sv_get_foldl_mono. Qed.

(** Step1: answer with Step2 carrying exactly the structs the peer is missing
    (the [diff_model]). The doc is unchanged.

    The return value is characterized as a fragment difference: the response's
    update slice holds precisely the local structs whose id the peer's state
    vector [sv] does NOT already cover ([diff_model_covers]), and nothing that
    is not local ([diff_model_subset]). So a reader sees, at the spec level,
    which updates the answer contains. *)
Lemma wp_syncDoc__HandleSyncMessage_Step1 (d : loc) (items : list yjs.updateItem.t)
    (msg : yjs.SyncMessage.t) (dqsv : dfrac) (sv : gmap w64 w64) :
  msg.(yjs.SyncMessage.tag') = W64 0 ->
  {{{ is_pkg_init yjs ∗ own_syncDoc d items ∗ own_map msg.(yjs.SyncMessage.sv') dqsv sv }}}
    d @! (go.PointerType yjs.syncDoc) @! "HandleSyncMessage" #msg
  {{{ (resp : yjs.SyncMessage.t) (ok : bool) (diff : list yjs.updateItem.t), RET (#resp, #ok);
      ⌜ok = true⌝ ∗ ⌜resp.(yjs.SyncMessage.tag') = W64 1⌝ ∗
      own_syncDoc d items ∗ own_map msg.(yjs.SyncMessage.sv') dqsv sv ∗
      resp.(yjs.SyncMessage.update') ↦* diff ∗
      own_slice_cap yjs.updateItem.t resp.(yjs.SyncMessage.update') (DfracOwn 1) ∗
      (* the return value = exactly the local structs the peer's sv misses *)
      ⌜∀ u, u ∈ diff <-> (u ∈ items /\ ¬ sv_covers sv u)⌝ ∗
      ⌜∀ u, u ∈ diff -> u ∈ items⌝ }}}.
Proof.
  intros Htag. wp_start as "(Hdoc & Hmap)". iNamed "Hdoc".
  wp_auto.
  rewrite Htag.
  rewrite bool_decide_eq_true_2; [| done].
  wp_auto.
  wp_apply (wp_computeDiff with "[$Hsl $Hmap]") as "%out (Hsl & Hmap & Hout & Houtcap)".
  iApply ("HΦ" $! _ _ (diff_model sv items)).
  iSplit; [done|].
  iSplit; [done|].
  iSplitR "Hmap Hout Houtcap".
  { iExists sl. iFrame. }
  iFrame.
  iPureIntro. split.
  - move=> u. exact (diff_model_covers sv items u).
  - exact (diff_model_subset sv items).
Qed.

(** Step2 / Update: no response; the document absorbs [upd] and its fragment
    advances. The fragment change is characterized both ways: every struct in
    [upd] is now covered by the doc's state vector (the update is delivered),
    and nothing already covered is lost (monotone). So the new fragment is
    exactly the old one plus [upd]. The [nowrap] hypothesis is the [2^64] seam
    (the coverage claim uses [clock + 1] in [w64]); it matches the no-wrap
    precondition of the store's [applyUpdate]. *)
Lemma wp_syncDoc__HandleSyncMessage_Apply (d : loc) (items : list yjs.updateItem.t)
    (msg : yjs.SyncMessage.t) (dq : dfrac) (upd : list yjs.updateItem.t) :
  msg.(yjs.SyncMessage.tag') ≠ W64 0 ->
  (∀ w, w ∈ items ++ upd -> (uint.Z (ui_clock w) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ own_syncDoc d items ∗ msg.(yjs.SyncMessage.update') ↦*{dq} upd }}}
    d @! (go.PointerType yjs.syncDoc) @! "HandleSyncMessage" #msg
  {{{ (resp : yjs.SyncMessage.t) (ok : bool), RET (#resp, #ok);
      ⌜ok = false⌝ ∗ own_syncDoc d (items ++ upd) ∗
      (* the update is now part of the document's delivered fragment *)
      ⌜∀ u, u ∈ upd -> sv_covers (state_vector_model (items ++ upd)) u⌝ ∗
      (* and nothing previously covered was lost *)
      ⌜∀ c, (uint.Z (sv_get (state_vector_model items) c)
               <= uint.Z (sv_get (state_vector_model (items ++ upd)) c))%Z⌝ ∗
      msg.(yjs.SyncMessage.update') ↦*{dq} upd }}}.
Proof.
  intros Htag Hnowrap. wp_start as "(Hdoc & Hupd)". iNamed "Hdoc".
  wp_auto.
  rewrite (bool_decide_eq_false_2 _ Htag).
  wp_auto.
  iDestruct (own_slice_len with "Hupd") as %[Hupdlen Hupdlen0].
  iAssert (∃ (i : w64) (sl : slice.t),
    "Hi" ∷ i_ptr ↦ i ∗ "Hd" ∷ d_ptr ↦ d ∗ "Hmsg" ∷ msg_ptr ↦ msg ∗
    "Hitems" ∷ (d .[(yjs.syncDoc.t), "items"]) ↦ sl ∗
    "Hsl" ∷ sl ↦* (items ++ take (uint.nat i) upd) ∗
    "Hcap" ∷ own_slice_cap yjs.updateItem.t sl (DfracOwn 1) ∗
    "Hupd" ∷ msg.(yjs.SyncMessage.update') ↦*{dq} upd ∗
    "%Hile" ∷ ⌜(uint.Z i <= Z.of_nat (length upd))%Z⌝)%I
    with "[i d msg Hitems Hsl Hcap Hupd]" as "IH".
  { iExists (W64 0), sl. iFrame. rewrite take_0 app_nil_r. iFrame. word. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - have Hilt : (uint.nat i < length upd)%nat by word.
    destruct (upd !! uint.nat i) as [u|] eqn:Hu; [| apply lookup_ge_None in Hu; lia].
    iDestruct (own_slice_elem_acc (sint.Z i) u msg.(yjs.SyncMessage.update') dq upd with "Hupd")
      as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hu. }
    wp_auto.
    rewrite decide_True; [| word].
    wp_auto.
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "%s1 [Hs1 _]".
    wp_auto.
    wp_apply (wp_slice_append with "[$Hsl $Hcap $Hs1]") as "%sl' (Hsl & Hcap & _)".
    have Hz0 : forall (z : yjs.updateItem.t), <[sint.nat (W64 0):=u]> [z] = [u].
    { intro z. have Hz : sint.nat (W64 0) = 0%nat by word. rewrite Hz //. }
    iEval (rewrite Hz0) in "Hsl".
    iDestruct ("Hgive" $! u with "Hel") as "Hupd".
    rewrite list_insert_id; [| replace (sint.nat i) with (uint.nat i) by word; exact Hu].
    wp_for_post.
    iFrame "HΦ".
    iExists (word.add i (W64 1)), sl'.
    iFrame "Hi Hd Hmsg Hitems Hcap Hupd".
    have Hi1 : uint.nat (word.add i (W64 1)) = S (uint.nat i) by word.
    rewrite Hi1 (take_S_r upd (uint.nat i) u Hu) app_assoc.
    iFrame "Hsl". word.
  - wp_auto.
    have Hieq : uint.nat i = length upd by word.
    rewrite Hieq take_ge; [| lia].
    iApply "HΦ".
    iSplit; [done |].
    iSplitL "Hitems Hsl Hcap".
    { iExists sl0. iFrame. }
    iSplit.
    { iPureIntro. move=> u Hu. exact (state_vector_model_app_covers items upd u Hnowrap Hu). }
    iSplit.
    { iPureIntro. move=> c. apply state_vector_model_app_grew. }
    iFrame "Hupd".
Qed.

End sync.
