(** WP proofs for the [Text] / [yText] methods: visible-index navigation
    ([yText.findPos]) and the top-level [Text.Insert].

    [Text.Insert] composes [findPos] (which walks to the straddling neighbours of
    a character index) with [Store.Integrate] (in [yjs_store]); [own_insert_doc]
    bundles the heap Text/Doc/store structs with the clock-counter invariant that
    makes each freshly generated id maximal, discharging the [maximalId] side
    condition of the integrate spec. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id yjs_item yjs_store.
From New.proof.sync_proof Require Import mutex.        (* is_Mutex / Lock / Unlock *)
From iris.algebra Require Import auth gmap.
(* [is_text_lb]'s subsequence RA needs [mra], absent from this iris pin — must be
   vendored (see the note in yjs_store.v). *)
(* From iris.algebra.lib Require Import mra. *)

Section text.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== Text.Insert: WP proof ============================================ *)

(** The document invariant seen by Text.Insert: the heap Text/Doc/store structs,
    the validity of the target sequence, and the counter invariant that makes
    each generated id maximal (every same-client clock in [arr] is below the
    Doc clock [k], so a fresh item at clock [k] satisfies [maximalId]). *)
Definition own_insert_doc (t : loc) (arr : list (YjsItem A)) (cl k : w64) : iProp Σ :=
  ∃ (tv : yjs.Text.t) (dv : yjs.Doc.t) (sv : yjs.store.t),
    "Ht" ∷ t ↦ tv ∗
    "Hdoc" ∷ tv.(yjs.Text.doc') ↦ dv ∗
    "Hstore" ∷ dv.(yjs.Doc.store') ↦ sv ∗
    "%Hcl" ∷ ⌜sv.(yjs.store.client') = cl⌝ ∗
    "%Hk" ∷ ⌜dv.(yjs.Doc.clock') = k⌝ ∗
    "Hvalid" ∷ is_valid_ytext (tv.(yjs.Text.inner')) arr ∗
    "%Hmax" ∷ ⌜forall x, ArrSet arr (itemPtr x) ->
                 clientId (item_id x) = uint.nat cl ->
                 (clock (item_id x) < uint.nat k)%nat⌝.

(** findPos on an empty sequence returns (null, null) without reading any flags
    (both loops have an empty list to walk). *)
Lemma wp_yText__findPos_empty (parent : loc) (idx : w64) :
  {{{ is_pkg_init yjs ∗ is_ytext parent [] [] }}}
    parent @! (go.PointerType yjs.yText) @! "findPos" #idx
  {{{ RET (#null, #null); is_ytext parent [] [] }}}.
Proof.
  wp_start as "Hyt". iNamed "Hyt".
  iDestruct "Hdll" as %[Hstart Htl].
  wp_auto. rewrite Hstart.
  (* skip-deleted loop: right = null, so the condition is false on entry *)
  iAssert (
    "Hp" ∷ parent ↦ yt ∗ "Hl" ∷ left_ptr ↦ null ∗
    "Hr" ∷ right_ptr ↦ null ∗ "Hidx" ∷ index_ptr ↦ idx
  )%I with "[Hparent left right index]" as "IH".
  { iFrame. }
  wp_for "IH".
  (* count loop: right = null, so the condition is false on entry *)
  iAssert (
    "Hp" ∷ parent ↦ yt ∗ "Hl" ∷ left_ptr ↦ null ∗
    "Hr" ∷ right_ptr ↦ null ∗ "Hrem" ∷ remaining_ptr ↦ idx
  )%I with "[Hp Hl Hr remaining]" as "IH".
  { iFrame. }
  wp_for "IH".
  wp_if_destruct.
  - wp_auto. iApply "HΦ". iExists yt, null. iFrame "Hp". simpl. iPureIntro.
    split_and!; [exact Hstart | reflexivity | exact Hlen | exact Hrepr].
  - iApply "HΦ". iExists yt, null. iFrame "Hp". simpl. iPureIntro.
    split_and!; [exact Hstart | reflexivity | exact Hlen | exact Hrepr].
Qed.

(** General [findPos]: walk to the visible character index [idx] (≤ number of
    nodes) and return the straddling neighbours. Since the goose model has no
    deletions (every cell is Countable / non-Deleted / [Len = 1], pinned by
    [cell_repr]), the skip-deleted loop is a no-op and the count loop advances
    one node per unit of [idx]; the result is the node just before / at position
    [idx]. The two returned locations are uniform via [node_loc] (which is [null]
    out of range), so [idx = 0] gives [left = null] and [idx = length] gives
    [right = null]. *)
Lemma wp_yText__findPos (parent : loc) (cells : list item_cell)
    (arr : list (YjsItem A)) (idx : w64) :
  (uint.nat idx <= length cells)%nat ->
  {{{ is_pkg_init yjs ∗ is_ytext parent cells arr }}}
    parent @! (go.PointerType yjs.yText) @! "findPos" #idx
  {{{ (lft rgt : loc), RET (#lft, #rgt);
      is_ytext parent cells arr ∗
      ⌜lft = node_loc cells (Z.of_nat (uint.nat idx) - 1)⌝ ∗
      ⌜rgt = node_loc cells (Z.of_nat (uint.nat idx))⌝ }}}.
Proof.
  iIntros (Hbound). wp_start as "Hyt". iNamed "Hyt".
  iDestruct (is_dll_head_node cells _ tl with "Hdll") as %Hhead.
  destruct cells as [|c0 cs].
  - (* empty document: both loops are no-ops, return (null, null) *)
    iDestruct "Hdll" as %[Hs Ht]. wp_auto. rewrite Hs.
    iAssert ("Hp" ∷ parent ↦ yt ∗ "Hl" ∷ left_ptr ↦ null ∗ "Hr" ∷ right_ptr ↦ null ∗ "Hidx" ∷ index_ptr ↦ idx)%I
      with "[Hparent left right index]" as "IH".
    { iFrame. }
    wp_for "IH".
    iAssert ("Hp" ∷ parent ↦ yt ∗ "Hl" ∷ left_ptr ↦ null ∗ "Hr" ∷ right_ptr ↦ null ∗ "Hrem" ∷ remaining_ptr ↦ idx)%I
      with "[Hp Hl Hr remaining]" as "IH".
    { iFrame. }
    wp_for "IH".
    wp_if_destruct.
    + wp_auto. iApply ("HΦ" $! null null). iSplitL "Hp".
      { iExists yt, null. iFrame "Hp". iPureIntro. split_and!; [exact Hs | reflexivity | exact Hlen | exact Hrepr]. }
      iPureIntro. split; rewrite /node_loc; case_decide; reflexivity.
    + iApply ("HΦ" $! null null). iSplitL "Hp".
      { iExists yt, null. iFrame "Hp". iPureIntro. split_and!; [exact Hs | reflexivity | exact Hlen | exact Hrepr]. }
      iPureIntro. split; rewrite /node_loc; case_decide; reflexivity.
  - (* non-empty: skip-deleted loop reads node 0 (not deleted), count loop walks idx nodes *)
    have Hc0 : (c0 :: cs) !! 0%nat = Some c0 by reflexivity.
    have Hposlen : (uint.nat idx <= length (c0 :: cs))%nat := Hbound.
    wp_auto.
    iDestruct (node_loc_lt_not_null (c0 :: cs) _ tl 0%nat ltac:(simpl; lia) with "Hdll") as "[%Hnn0 Hdll]".
    have Hstartnn : yt.(yjs.yText.start') ≠ null by (rewrite Hhead; exact Hnn0).
    iAssert ("Hp" ∷ parent ↦ yt ∗ "Hdll" ∷ is_dll yt.(yjs.yText.start') tl null null (c0 :: cs) ∗ "Hindex" ∷ index_ptr ↦ idx ∗ "Hleftp" ∷ left_ptr ↦ null ∗ "Hrightp" ∷ right_ptr ↦ yt.(yjs.yText.start'))%I
      with "[Hparent Hdll index left right]" as "IH".
    { iFrame. }
    wp_for "IH".
    rewrite (bool_decide_eq_false_2 (yt.(yjs.yText.start') = null) Hstartnn). simpl negb.
    have Hstart_c0 : yt.(yjs.yText.start') = ic_loc c0 by (rewrite Hhead /node_loc /=; reflexivity).
    have [yi0 [Hyi0 Hcr0]] := cells_repr_lookup arr (c0 :: cs) arr 0%nat c0 Hrepr Hc0.
    have Hflags0 : (ic_val c0).(yjs.item.flags') = W8 2 := proj1 (proj2 (proj2 (proj2 (proj2 Hcr0)))).
    iDestruct (is_dll_acc (c0 :: cs) yt.(yjs.yText.start') tl 0%nat c0 Hc0 with "Hdll") as "H". iNamed "H".
    iEval (rewrite Hstart_c0) in "Hrightp".
    wp_auto.
    wp_apply (wp_item__Deleted c0.(ic_loc) c0.(ic_val) Hflags0 with "[$Hcval]"). iIntros "Hcval".
    rewrite decide_False; [| done]. rewrite decide_True; [| done].
    iDestruct ("Hback" with "Hcval") as "Hdll".
    wp_auto.
    iAssert (∃ (j : nat) (lloc rloc : loc), "Hp" ∷ parent ↦ yt ∗ "Hdll" ∷ is_dll yt.(yjs.yText.start') tl null null (c0 :: cs) ∗ "Hleftp" ∷ left_ptr ↦ lloc ∗ "Hrightp" ∷ right_ptr ↦ rloc ∗ "Hrem" ∷ remaining_ptr ↦ W64 (uint.Z idx - Z.of_nat j) ∗ "%Hlloc" ∷ ⌜lloc = node_loc (c0 :: cs) (Z.of_nat j - 1)⌝ ∗ "%Hrloc" ∷ ⌜rloc = node_loc (c0 :: cs) (Z.of_nat j)⌝ ∗ "%Hj" ∷ ⌜(j <= uint.nat idx)%nat⌝)%I
      with "[Hp Hdll Hleftp Hrightp remaining]" as "IH".
    { iExists 0%nat, null, c0.(ic_loc). iFrame "Hp Hdll Hleftp Hrightp".
      replace (W64 (uint.Z idx - Z.of_nat 0)) with idx by word. iFrame "remaining".
      iPureIntro. split_and!.
      - rewrite /node_loc. case_decide; [lia | reflexivity].
      - rewrite Hcloc //.
      - lia. }
    wp_for "IH".
    have Hidxj : uint.Z (W64 (uint.Z idx - Z.of_nat j)) = uint.Z idx - Z.of_nat j by word.
    case_bool_decide as Hlt.
    + (* j < idx: read node j (indexable, len 1), advance left/right *)
      have Hjpos : (j < uint.nat idx)%nat by (rewrite Hidxj in Hlt; word).
      have Hjlt : (j < length (c0 :: cs))%nat by lia.
      destruct ((c0 :: cs) !! j) as [cj|] eqn:Hcj; [| apply lookup_ge_None in Hcj; lia].
      have [yij [Hyij Hcrj]] := cells_repr_lookup arr (c0 :: cs) arr j cj Hrepr Hcj.
      have Hflagsj : (ic_val cj).(yjs.item.flags') = W8 2 := proj1 (proj2 (proj2 (proj2 (proj2 Hcrj)))).
      have Hcontlenj : length ((ic_val cj).(yjs.item.content').(yjs.content.content')) = 1%nat := proj2 (proj2 (proj2 (proj2 (proj2 Hcrj)))).
      iDestruct (is_dll_acc (c0 :: cs) yt.(yjs.yText.start') tl j cj Hcj with "Hdll") as "Hacc".
      iDestruct "Hacc" as "(%Hcjloc & %Hcjl & %Hcjr & Hcjval & Hcjol & Hcjor & Hback)".
      have Hrlocj : rloc = cj.(ic_loc) by rewrite Hrloc Hcjloc.
      iDestruct (typed_pointsto_not_null with "Hcjval") as %Hcjnn.
      iEval (rewrite Hrlocj) in "Hrightp".
      wp_auto.
      rewrite (bool_decide_eq_false_2 (cj.(ic_loc) = null) Hcjnn). simpl negb.
      rewrite decide_True; [| done]. wp_auto.
      wp_apply (wp_item__Indexable cj.(ic_loc) cj.(ic_val) Hflagsj with "[$Hcjval]"). iIntros "Hcjval".
      wp_auto.
      wp_apply (wp_item__Len cj.(ic_loc) cj.(ic_val) with "[$Hcjval]"). iIntros "Hcjval".
      rewrite Hcontlenj. wp_auto.
      wp_for_post.
      iDestruct ("Hback" with "Hcjval") as "Hdll".
      iFrame "HΦ Hcol Hcor".
      iExists (S j), cj.(ic_loc), (cj.(ic_val).(yjs.item.right')).
      iFrame "Hp Hdll Hleftp Hrightp".
      replace (w64_word_instance.(word.sub) (W64 (uint.Z idx - Z.of_nat j)) (W64 1%nat)) with (W64 (uint.Z idx - Z.of_nat (S j))) by word.
      iFrame "Hrem".
      iPureIntro. split_and!.
      * rewrite Hcjloc. f_equal. lia.
      * rewrite Hcjr. f_equal. lia.
      * lia.
    + (* j = idx: loop exits, return (left, right) at positions idx-1, idx *)
      have Hjeq : j = uint.nat idx by (rewrite Hidxj in Hlt; word).
      wp_auto.
      rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
      iApply ("HΦ" $! lloc rloc).
      iSplitL "Hp Hdll".
      { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split; [exact Hlen | exact Hrepr]. }
      iPureIntro. split; [ rewrite Hlloc Hjeq // | rewrite Hrloc Hjeq // ].
Qed.

(** The item [Text.Insert] builds at the straddle point is valid. Repackages
    [item_valid_at] over the exact origin facts [findPos] yields (a left/right
    neighbour by id, or the [First]/[Last] boundary), so the WP proof discharges
    [IsItemValid] in one application. *)
Lemma insert_item_valid (arr : list (YjsItem A)) (p : nat) (newid : YjsId) (c : A)
    (o r : YjsPtr A) (oidL oidR : option YjsId) :
  YjsArrInvariant arr ->
  (oidL = None /\ o = First /\ p = 0%nat
     \/ ∃ li, (1 <= p)%nat /\ arr !! (p - 1)%nat = Some li /\ oidL = Some (item_id li) /\ o = itemPtr li) ->
  (oidR = None /\ r = Last /\ p = length arr
     \/ ∃ ri, arr !! p = Some ri /\ oidR = Some (item_id ri) /\ r = itemPtr ri) ->
  IsItemValid (Item o r newid c).
Proof.
  intros Hinv Hleft Hright.
  apply (item_valid_at arr p newid c o r Hinv).
  - destruct Hleft as [(_ & Ho & Hp0) | (li & Hge & Hla & _ & Ho)];
      [left; split; [exact Hp0 | exact Ho]
      | right; split; [exact Hge | exists li; split; [exact Hla | exact Ho]]].
  - destruct Hright as [(_ & Hr & Hpl) | (ri & Hria & _ & Hr)];
      [left; split; [exact Hpl | exact Hr]
      | right; exists ri; split; [exact Hria | exact Hr]].
Qed.

(** The fresh item is maximal among same-client items of [arr]: its clock [clk]
    exceeds every same-client clock already present. This is the [maximalId] side
    condition of [wp_Store__Integrate], read off the Doc clock-counter invariant. *)
Lemma insert_maximalId (arr : list (YjsItem A)) (o r : YjsPtr A) (client clk : nat) (c : A) :
  (∀ x, ArrSet arr (itemPtr x) -> clientId (item_id x) = client -> (clock (item_id x) < clk)%nat) ->
  maximalId (Item o r (MkYjsId client clk) c) arr.
Proof. intros Hctr x Hx Hc. exact (Hctr x Hx Hc). Qed.

(** Text.Insert at an arbitrary visible index preserves the document invariant.
    [findPos] locates the straddling neighbours; the per-character loop integrates
    one 1-char item per byte, chaining each new item's left origin to the previous
    one while sharing the fixed right origin. Validity of each integrate is
    [item_valid_at] (head / middle / tail / empty by which neighbours exist) and
    its placement is [insert_straddle], which keeps the inserted run between the
    neighbours so the loop's left/right tracking is maintained. *)
Lemma wp_Text__Insert (t : loc) (cl k idx : w64) (content : go_string) (arr0 : list (YjsItem A)) :
  (uint.Z k + Z.of_nat (length content) < 2 ^ 63)%Z ->
  {{{ is_pkg_init yjs ∗ own_insert_doc t arr0 cl k }}}
    t @! (go.PointerType yjs.Text) @! "Insert" #idx #content
  {{{ (arr' : list (YjsItem A)) (k' : w64), RET #(); own_insert_doc t arr' cl k' }}}.
Proof.
  intros Hovf.
  wp_start as "Hown". iNamed "Hown".
  iDestruct "Hvalid" as (cells0) "[Hyt %Hinv0]". iNamed "Hyt".
  iDestruct "Htext" as (yt0 tl0) "(Hparent & Hdll & %Hlen & %Hrepr)".
  wp_auto.
  case_bool_decide as Hcond.
  { wp_auto.
    iAssert (is_ytext tv.(yjs.Text.inner') cells0 arr0) with "[Hparent Hdll]" as "Hyt".
    { iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split; [exact Hlen | exact Hrepr]. }
    iAssert (is_valid_ytext tv.(yjs.Text.inner') arr0) with "[Hyt]" as "Hvalid".
    { iExists cells0. iFrame "Hyt". iPureIntro. exact Hinv0. }
    iApply ("HΦ" $! arr0 k). iExists tv, dv, sv. iFrame "Ht Hdoc Hstore Hvalid".
    iPureIntro. split_and!; [exact Hcl | exact Hk | exact Hmax]. }
  rewrite Hlen in Hcond.
  have Hposle : (uint.nat idx <= length cells0)%nat by word.
  wp_auto.
  iAssert (is_ytext tv.(yjs.Text.inner') cells0 arr0) with "[Hparent Hdll]" as "Htext".
  { iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split; [exact Hlen | exact Hrepr]. }
  wp_apply (wp_yText__findPos (tv.(yjs.Text.inner')) cells0 arr0 idx Hposle with "[$Htext]").
  iIntros (lft rgt) "(Htext & %Hlftloc & %Hrgtloc)".
  wp_auto.
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗ ∃ (oRptr : loc) (in_rO : option yjs.id.t),
      "HoR" ∷ originRightId_ptr ↦ oRptr ∗ "HisR" ∷ is_origin_id oRptr in_rO ∗
      "Htext" ∷ is_ytext tv.(yjs.Text.inner') cells0 arr0 ∗ "Hright" ∷ right_ptr ↦ rgt ∗
      "%Hrightinit" ∷ ⌜(in_rO = None ∧ (uint.nat idx = length cells0)%nat) ∨
        (∃ (ri : YjsItem A) (rid : yjs.id.t), arr0 !! (uint.nat idx) = Some ri ∧ in_rO = Some rid ∧ item_id ri = toYjsId rid)⌝)%I
      with "[right Htext originRightId]".
  { iDestruct "Htext" as (yt1 tl1) "(Hpar1 & Hdll1 & %Hlen1 & %Hrepr1)".
    iSplitR; [done|].
    destruct (decide (uint.nat idx = length cells0)%nat) as [Hpeq|Hne];
    [ iExists null, None; iFrame "originRightId right";
      (iSplitR "Hpar1 Hdll1"; [by rewrite /is_origin_id |]);
      (iSplitL "Hpar1 Hdll1"; [ iExists yt1, tl1; iFrame "Hpar1 Hdll1"; iPureIntro; split; [exact Hlen1 | exact Hrepr1] |]);
      iPureIntro; left; split; [reflexivity | exact Hpeq]
    | have Hlt : (uint.nat idx < length cells0)%nat by lia;
      iDestruct (node_loc_lt_not_null cells0 yt1.(yjs.yText.start') tl1 (uint.nat idx) Hlt with "Hdll1") as "[%Hnn _]";
      exfalso; exact (Hnn e) ].
    iDestruct (node_loc_lt_not_null cells0 yt1.(yjs.yText.start') tl1 (uint.nat idx) Hlt with "Hdll1") as "[%Hnn _]".
    exfalso; exact (Hnn e). }
  { iDestruct "Htext" as (yt1 tl1) "(Hpar1 & Hdll1 & %Hlen1 & %Hrepr1)".
    have Hposlt : (uint.nat idx < length cells0)%nat.
    { destruct (decide (uint.nat idx < length cells0)%nat) as [Hlt|Hge]; [exact Hlt|exfalso].
      apply n. rewrite /node_loc decide_True; [|lia].
      have Hpe : (uint.nat idx = length cells0)%nat by lia.
      rewrite Hpe Nat2Z.id lookup_ge_None_2; [done|lia]. }
    destruct (cells0 !! uint.nat idx) as [c0|] eqn:Hc0; [| apply lookup_ge_None in Hc0; lia].
    have [yi0 [Hyi0 Hcr0]] := cells_repr_lookup arr0 cells0 arr0 (uint.nat idx) c0 Hrepr1 Hc0.
    iDestruct (is_dll_acc cells0 yt1.(yjs.yText.start') tl1 (uint.nat idx) c0 Hc0 with "Hdll1") as "Hacc". iNamed "Hacc".
    iEval (rewrite Hcloc) in "Hcval".
    wp_load. wp_pures. wp_store.
    iDestruct (typed_pointsto_not_null with "rid") as %Hridnn.
    iPersist "rid".
    wp_auto.
    iEval (rewrite -Hcloc) in "Hcval".
    iDestruct ("Hback" with "Hcval") as "Hdll1".
    iSplitR; [done|].
    iExists rid_ptr, (Some c0.(ic_val).(yjs.item.id')).
    iFrame "originRightId right".
    iSplitR "Hpar1 Hdll1".
    { rewrite /is_origin_id. iSplit; [iPureIntro; exact Hridnn | iFrame "rid"]. }
    iSplitL "Hpar1 Hdll1".
    { iExists yt1, tl1. iFrame "Hpar1 Hdll1". iPureIntro. split; [exact Hlen1 | exact Hrepr1]. }
    iPureIntro. right. exists yi0, c0.(ic_val).(yjs.item.id'). split_and!; [exact Hyi0 | reflexivity | exact (proj1 Hcr0)]. }
  iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ". wp_auto.
  iEval (rewrite Hcl) in "client".
  iAssert (∃ (j : nat) (arr : list (YjsItem A)) (cells : list item_cell) (leftloc : loc) (dvj : yjs.Doc.t),
    "Hi" ∷ i_ptr ↦ W64 j ∗
    "Htptr0" ∷ t_ptr ↦ t ∗
    "Hcontent" ∷ content_ptr ↦ content ∗
    "Hclient" ∷ client_ptr ↦ cl ∗
    "HoRk" ∷ originRightId_ptr ↦ oRptr ∗
    "Hleftp" ∷ left_ptr ↦ leftloc ∗
    "Htv" ∷ t ↦ tv ∗
    "Hdocj" ∷ tv.(yjs.Text.doc') ↦ dvj ∗
    "Hstorej" ∷ dv.(yjs.Doc.store') ↦ sv ∗
    "Htextj" ∷ is_ytext tv.(yjs.Text.inner') cells arr ∗
    "%Hdvstore" ∷ ⌜dvj.(yjs.Doc.store') = dv.(yjs.Doc.store')⌝ ∗
    "%Hdvclock" ∷ ⌜dvj.(yjs.Doc.clock') = W64 (uint.Z k + j)⌝ ∗
    "%Hinvj" ∷ ⌜YjsArrInvariant arr⌝ ∗
    "%Hlenarr" ∷ ⌜length arr = (length arr0 + j)%nat⌝ ∗
    "%Hjle" ∷ ⌜(j <= length content)%nat⌝ ∗
    "%Hctr" ∷ ⌜∀ x : YjsItem A, ArrSet arr (itemPtr x) → clientId (item_id x) = uint.nat cl → (clock (item_id x) < uint.nat k + j)%nat⌝ ∗
    "%Hleftj" ∷ ⌜(leftloc = null ∧ (uint.nat idx + j = 0)%nat)
      ∨ (∃ (lc : item_cell) (li : YjsItem A),
           cells !! (uint.nat idx + j - 1)%nat = Some lc ∧ ic_loc lc = leftloc ∧
           arr !! (uint.nat idx + j - 1)%nat = Some li ∧
           item_id li = toYjsId (ic_val lc).(yjs.item.id') ∧
           length ((ic_val lc).(yjs.item.content').(yjs.content.content')) = 1%nat ∧ (1 <= uint.nat idx + j)%nat)⌝ ∗
    "%Hrightj" ∷ ⌜(in_rO = None ∧ (uint.nat idx + j = length arr)%nat)
      ∨ (∃ (ri : YjsItem A) (rid : yjs.id.t),
           arr !! (uint.nat idx + j)%nat = Some ri ∧ in_rO = Some rid ∧ item_id ri = toYjsId rid)⌝
    )%I with "[i t content client HoR left Ht Hdoc Hstore Htext]" as "IH".
  { iExists 0%nat, arr0, cells0, lft, dv.
    iFrame "i t content client HoR left Ht Hdoc Hstore Htext".
    iPureIntro. split_and!.
    - reflexivity.
    - rewrite Hk. word.
    - exact Hinv0.
    - lia.
    - lia.
    - intros x Hx Hc. have := Hmax x Hx Hc. lia.
    - destruct (decide (uint.nat idx = 0)%nat) as [Hidx0 | Hidxpos].
      + left. rewrite Hlftloc Hidx0. split; [rewrite /node_loc; case_decide as Hd; [exfalso; lia | reflexivity] | lia].
      + right.
        have Hidxm : (uint.nat idx - 1 < length cells0)%nat by lia.
        destruct (cells0 !! (uint.nat idx - 1)%nat) as [lc|] eqn:Hlc; [| apply lookup_ge_None in Hlc; lia].
        have [li [Hli Hcrlc]] := cells_repr_lookup arr0 cells0 arr0 (uint.nat idx - 1) lc Hrepr Hlc.
        exists lc, li. split_and!.
        * replace (uint.nat idx + 0 - 1)%nat with (uint.nat idx - 1)%nat by lia. exact Hlc.
        * rewrite Hlftloc /node_loc. case_decide as Hd; [| exfalso; lia].
          have -> : Z.to_nat (Z.of_nat (uint.nat idx) - 1) = (uint.nat idx - 1)%nat by lia.
          rewrite Hlc //.
        * replace (uint.nat idx + 0 - 1)%nat with (uint.nat idx - 1)%nat by lia. exact Hli.
        * exact (proj1 Hcrlc).
        * exact (proj2 (proj2 (proj2 (proj2 (proj2 Hcrlc))))).
        * lia.
    - destruct Hrightinit as [[Hrn Hpe] | (ri & rid & Hriarr & Hrosome & Hriid)].
      + left. split; [exact Hrn |]. rewrite Nat.add_0_r Hpe. exact (cells_repr_length _ _ _ Hrepr).
      + right. exists ri, rid. split_and!; [rewrite Nat.add_0_r; exact Hriarr | exact Hrosome | exact Hriid]. }
  wp_for "IH".
  wp_apply strings.wp_string_len. iIntros "%Hlcb". wp_auto. case_bool_decide as Hjlt.
  2:{ rewrite decide_False; [|done]. rewrite decide_True; [|done]. wp_auto.
      iApply ("HΦ" $! arr (W64 (uint.Z k + j))).
      rewrite /own_insert_doc. iExists tv, dvj, sv.
      rewrite Hdvstore. iFrame "Htv Hdocj Hstorej".
      iSplitR; [iPureIntro; exact Hcl|].
      iSplitR; [iPureIntro; exact Hdvclock|].
      iSplitL "Htextj"; [ iExists cells; iFrame "Htextj"; iPureIntro; exact Hinvj |].
      iPureIntro. intros x Hx Hc. have Hkj : uint.nat (W64 (uint.Z k + j)) = (uint.nat k + j)%nat by word. rewrite Hkj. exact (Hctr x Hx Hc). }
  rewrite decide_True; [|done]. wp_auto.
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗
    ∃ (oLptr : loc) (oL : option yjs.id.t),
      "HoL" ∷ originLeftId_ptr ↦ oLptr ∗
      "HisL" ∷ is_origin_id oLptr oL ∗
      "Htextj" ∷ is_ytext tv.(yjs.Text.inner') cells arr ∗
      "Hleftp" ∷ left_ptr ↦ leftloc ∗
      "%Hleftspec" ∷ ⌜(oL = None ∧ (uint.nat idx + j = 0)%nat) ∨
         (∃ (li : YjsItem A), (1 <= uint.nat idx + j)%nat ∧ arr !! (uint.nat idx + j - 1)%nat = Some li ∧ (toYjsId <$> oL) = Some (item_id li))⌝)%I
    with "[Hleftp Htextj originLeftId]".
  { destruct Hleftj as [[_ Hpe0] | (lc & li & Hlccells & Hlcloc & Hliarr & Hliid & Hlclen & Hge1)].
    - iSplitR; [done|]. iExists null, None. iFrame "originLeftId Htextj Hleftp".
      iSplit; [by rewrite /is_origin_id|]. iPureIntro. left. split; [reflexivity | exact Hpe0].
    - iDestruct "Htextj" as (yth tlh) "(Hpar & Hdll & %Hlenh & %Hreprh)".
      iDestruct (is_dll_acc cells yth.(yjs.yText.start') tlh (uint.nat idx + j - 1)%nat lc Hlccells with "Hdll") as "Hacc". iNamed "Hacc".
      iDestruct (typed_pointsto_not_null with "Hcval") as %Hlcnn.
      exfalso. exact (Hlcnn Hlcloc). }
  { destruct Hleftj as [[Hln _] | (lc & li & Hlccells & Hlcloc & Hliarr & Hliid & Hlclen & Hge1)].
    { exfalso; exact (n Hln). }
    iDestruct "Htextj" as (yth tlh) "(Hpar & Hdll & %Hlenh & %Hreprh)".
    iDestruct (is_dll_acc cells yth.(yjs.yText.start') tlh (uint.nat idx + j - 1)%nat lc Hlccells with "Hdll") as "Hacc". iNamed "Hacc".
    iEval (rewrite Hlcloc) in "Hcval".
    wp_method_call. wp_call. wp_auto.
    wp_method_call. wp_call. rewrite /yjs.item__LastIdⁱᵐᵖˡ. wp_auto.
    wp_alloc icopy as "Hic". wp_auto.
    wp_bind (icopy @! (go.PointerType yjs.item) @! "Len" (# ()))%E.
    wp_apply (wp_item__Len icopy lc.(ic_val) with "[$Hic]"). iIntros "Hic".
    rewrite Hlclen. wp_pures. wp_store.
    iDestruct (typed_pointsto_not_null with "lid") as %Hlidnn.
    iPersist "lid". wp_auto.
    iEval (rewrite -Hlcloc) in "Hcval".
    iDestruct ("Hback" with "Hcval") as "Hdll".
    iSplitR; [done|].
    iExists lid_ptr, (Some {| yjs.id.clientId' := lc.(ic_val).(yjs.item.id').(yjs.id.clientId'); yjs.id.clock' := w64_word_instance.(word.sub) (w64_word_instance.(word.add) lc.(ic_val).(yjs.item.id').(yjs.id.clock') (W64 1%nat)) (W64 1) |}).
    iFrame "originLeftId Hleftp".
    iSplitR "Hpar Hdll".
    { rewrite /is_origin_id. iSplit; [iPureIntro; exact Hlidnn | iFrame "lid"]. }
    iSplitL "Hpar Hdll".
    { iExists yth, tlh. iFrame "Hpar Hdll". iPureIntro. split; [exact Hlenh | exact Hreprh]. }
    iPureIntro. right. exists li. split_and!.
    - exact Hge1.
    - exact Hliarr.
    - rewrite Hliid /toYjsId /=. f_equal. f_equal. word. }
  iIntros (v) "[%Hv HQL]". subst v. iNamed "HQL". wp_auto.
  wp_func_call. wp_call. wp_auto.
  wp_alloc client_l as "Hcl2". wp_auto.
  destruct (content !! sint.nat (W64 j)) as [b|] eqn:Hb;
    [ wp_auto | exfalso; apply lookup_ge_None in Hb; revert Hb Hjlt Hlcb; word ].
  wp_func_call. wp_call.
  wp_alloc oR2 as "HoR2". wp_auto.
  wp_alloc newit_l as "Hnewit". wp_auto.
  have Hclocknit : uint.nat dvj.(yjs.Doc.clock') = (uint.nat k + j)%nat by (rewrite Hdvclock; word).
  have Horig : ∃ (o : YjsPtr A),
     (toYjsId <$> oL = None ∧ o = First ∧ (uint.nat idx + j)%nat = 0%nat) ∨
     (∃ li, (1 <= uint.nat idx + j)%nat ∧ arr !! (uint.nat idx + j - 1)%nat = Some li ∧ toYjsId <$> oL = Some (item_id li) ∧ o = itemPtr li).
  { destruct Hleftspec as [[Hon Hp0] | (li & Hge & Hla & Hom)].
    - exists First. left. subst oL. split_and!; [reflexivity | reflexivity | exact Hp0].
    - exists (itemPtr li). right. exists li. split_and!; [exact Hge | exact Hla | exact Hom | reflexivity]. }
  destruct Horig as [morigin Horig].
  have Hrorig : ∃ (r : YjsPtr A),
     (toYjsId <$> in_rO = None ∧ r = Last ∧ (uint.nat idx + j)%nat = length arr) ∨
     (∃ ri, arr !! (uint.nat idx + j)%nat = Some ri ∧ toYjsId <$> in_rO = Some (item_id ri) ∧ r = itemPtr ri).
  { destruct Hrightj as [[Hrn Hpl] | (ri & rid & Hria & Hros & Hrii)].
    - exists Last. left. subst in_rO. split_and!; [reflexivity | reflexivity | exact Hpl].
    - exists (itemPtr ri). right. exists ri. split_and!; [exact Hria | rewrite Hros /= Hrii // | reflexivity]. }
  destruct Hrorig as [mrightorigin Hrorig].
  set (in_id1 := MkYjsId (uint.nat cl) (uint.nat dvj.(yjs.Doc.clock'))).
  set (input := MkIntegrateInput (toYjsId <$> oL) (toYjsId <$> in_rO) ([b] : A) in_id1).
  set (nit := Item (A:=A) morigin mrightorigin in_id1 [b]).
  have Htoitem : toItem input arr = Some nit.
  { apply (toItem_at arr in_id1 [b] morigin mrightorigin (toYjsId <$> oL) (toYjsId <$> in_rO) Hinvj).
    - destruct Horig as [(Hon & Ho & _) | (li & _ & Hla & Hom & Ho)]; [left; split; [exact Hon | exact Ho] | right; exists li; split_and!; [exact Hom | exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hla) | exact Ho]].
    - destruct Hrorig as [(Hrn & Hr & _) | (ri & Hria & Hri & Hr)]; [left; split; [exact Hrn | exact Hr] | right; exists ri; split_and!; [exact Hri | exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hria) | exact Hr]]. }
  have Hvalid : IsItemValid nit :=
    insert_item_valid arr (uint.nat idx + j) in_id1 [b] morigin mrightorigin
      (toYjsId <$> oL) (toYjsId <$> in_rO) Hinvj Horig Hrorig.
  have Hmax' : maximalId nit arr.
  { rewrite /nit /in_id1. apply insert_maximalId.
    intros x Hx Hc. rewrite Hclocknit. exact (Hctr x Hx Hc). }
  iDestruct "HisR" as "#HisRp".
  iAssert (is_fresh_item newit_l input) with "[Hnewit HisL]" as "Hfresh".
  { iExists _, oL, in_rO. rewrite /is_fresh_item_raw /=. iFrame "Hnewit HisL HisRp". iPureIntro. split_and!; reflexivity. }
  wp_apply (wp_Store__Integrate (dvj.(yjs.Doc.store')) (tv.(yjs.Text.inner')) newit_l arr input nit Htoitem Hvalid Hmax' with "[$Hfresh Htextj]").
  { iExists cells. iFrame "Htextj". iPureIntro. exact Hinvj. }
  iIntros (arr' i cells' c) "(%Hile & %Harr'eq & %Hinv' & Htext' & %Hnode)".
  wp_auto. wp_for_post.
  have Hple : (uint.nat idx + j <= length arr)%nat.
  { have Hlc := cells_repr_length arr0 cells0 arr0 Hrepr. rewrite Hlenarr. lia. }
  have Hplace : arr' = take (uint.nat idx + j)%nat arr ++ nit :: drop (uint.nat idx + j)%nat arr.
  { rewrite Harr'eq. apply (insert_straddle arr nit i (uint.nat idx + j)%nat Hinvj ltac:(rewrite -Harr'eq; exact Hinv') Hile Hple).
    - destruct Horig as [(_ & Ho & Hp0) | (li & Hge & Hla & _ & Ho)]; [left; split; [exact Hp0 | rewrite /nit /=; exact Ho] | right; split; [exact Hge | exists li; split; [exact Hla | rewrite /nit /=; exact Ho]]].
    - destruct Hrorig as [(_ & Hr & Hpl) | (ri & Hria & _ & Hr)]; [left; split; [exact Hpl | rewrite /nit /=; exact Hr] | right; exists ri; split; [exact Hria | rewrite /nit /=; exact Hr]]. }
  have Hnitpos : arr' !! (uint.nat idx + j)%nat = Some nit.
  { rewrite Hplace. apply list_lookup_middle. symmetry. apply length_take_le. exact Hple. }
  have Hshift : arr' !! (uint.nat idx + j + 1)%nat = arr !! (uint.nat idx + j)%nat.
  { rewrite Hplace. rewrite lookup_app_r; last (rewrite length_take_le; [lia | exact Hple]).
    rewrite length_take_le; last exact Hple.
    replace (uint.nat idx + j + 1 - (uint.nat idx + j))%nat with 1%nat by lia.
    simpl. rewrite lookup_drop. f_equal. lia. }
  iDestruct "Htext'" as (yt3 tl3) "(Hp3 & Hdll3 & %Hlen3 & %Hrepr3)".
  destruct Hnode as [x (Hcx & Hcloc & Hcid & Hcclen)].
  destruct (cells_repr_lookup arr' cells' arr' x c Hrepr3 Hcx) as [yi [Hyi Hcr3]].
  have HnitIn : nit ∈ arr' by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hnitpos).
  have Hyinit : yi = nit.
  { have Hyiid : item_id yi = item_id nit by (destruct Hcr3 as (Hidr & _); rewrite Hidr Hcid; reflexivity).
    have HyiIn : yi ∈ arr' by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hyi).
    exact (id_unique (ArrSet arr') (yai_item_set_inv _ Hinv') yi nit Hyiid HyiIn HnitIn). }
  subst yi.
  have Hxpos : x = (uint.nat idx + j)%nat.
  { destruct (Nat.lt_trichotomy x (uint.nat idx + j)%nat) as [Hlt|[Heq|Hgt]]; [exfalso|exact Heq|exfalso].
    - have HH := invariant_yjsarray_idx.getElem_lt_YjsLt' arr' x (uint.nat idx + j)%nat nit nit Hinv' Hyi Hnitpos Hlt.
      exact (asymmetry.yjs_lt_asymm (yai_closed _ Hinv') (yai_item_set_inv _ Hinv') (itemPtr nit) (itemPtr nit) HnitIn HnitIn HH HH).
    - have HH := invariant_yjsarray_idx.getElem_lt_YjsLt' arr' (uint.nat idx + j)%nat x nit nit Hinv' Hnitpos Hyi Hgt.
      exact (asymmetry.yjs_lt_asymm (yai_closed _ Hinv') (yai_item_set_inv _ Hinv') (itemPtr nit) (itemPtr nit) HnitIn HnitIn HH HH). }
  subst x.
  iFrame "HΦ HisRp".
  iExists (S j), arr', cells', newit_l, (dvj <| yjs.Doc.clock' := w64_word_instance.(word.add) dvj.(yjs.Doc.clock') (W64 1) |>).
  have HiEq : w64_word_instance.(word.add) (W64 j) (W64 1) = W64 (S j) by word.
  iEval (rewrite HiEq) in "Hi".
  iFrame "Hi Htptr0 Hcontent Hclient HoRk Hleftp Htv Hdocj Hstorej".
  iSplitL "Hp3 Hdll3".
  { iExists yt3, tl3. iFrame "Hp3 Hdll3". iPureIntro. split; [exact Hlen3 | exact Hrepr3]. }
  iPureIntro. split_and!.
  - exact Hdvstore.
  - change (w64_word_instance.(word.add) dvj.(yjs.Doc.clock') (W64 1) = W64 (uint.Z k + S j)). rewrite Hdvclock. word.
  - exact Hinv'.
  - rewrite Hplace length_app length_take_le; [| exact Hple]. simpl. rewrite length_drop. lia.
  - have HH : (j < length content)%nat by word. lia.
  - intros y Hy Hc. rewrite Hplace in Hy.
    apply elem_of_app in Hy as [Hyt | Hyc].
    + have Hya : y ∈ arr by (rewrite -(take_drop (uint.nat idx + j)%nat arr); apply elem_of_app; left; exact Hyt).
      have := Hctr y Hya Hc. lia.
    + apply elem_of_cons in Hyc as [-> | Hyd].
      * rewrite /nit /in_id1 /=. rewrite Hclocknit. lia.
      * have Hya : y ∈ arr by (rewrite -(take_drop (uint.nat idx + j)%nat arr); apply elem_of_app; right; exact Hyd).
        have := Hctr y Hya Hc. lia.
  - right. exists c, nit. split_and!.
    + replace (uint.nat idx + S j - 1)%nat with (uint.nat idx + j)%nat by lia. exact Hcx.
    + exact Hcloc.
    + replace (uint.nat idx + S j - 1)%nat with (uint.nat idx + j)%nat by lia. exact Hnitpos.
    + rewrite /nit /=. symmetry. exact Hcid.
    + exact Hcclen.
    + lia.
  - destruct Hrightj as [[Hrn Hpl] | (ri & rid & Hria & Hros & Hrii)].
    + left. split; [exact Hrn |]. rewrite Hplace length_app length_take_le; [| exact Hple]. simpl. rewrite length_drop. lia.
    + right. exists ri, rid. split_and!.
      * replace (uint.nat idx + S j)%nat with (uint.nat idx + j + 1)%nat by lia. rewrite Hshift. exact Hria.
      * exact Hros.
      * exact Hrii.
Qed.

(* ======================================================================== *)
(* Doc / Text invariant predicates — DESIGN (definitions only, see PR).       *)
(*                                                                           *)
(* The per-type invariants for [Doc] and [Text] live here (alongside their    *)
(* WP proofs). [Context] is at the end of the section so it does NOT affect   *)
(* the verified proofs above. These delegate to the STORE invariants          *)
(* ([is_Store] / [is_text_lb] / [store_inv]) defined in [yjs_store]; this is  *)
(* what makes [is_Text] reference only Text's own fields. The target          *)
(* [wp_Text__Insert] (replacing the [own_insert_doc] version above) is shown  *)
(* as a comment to avoid a name clash during this definitions-only review.    *)
(* [seq_inG] duplicates yjs_store's Context here (a section-local assumption); *)
(* on implementation it folds into the global Σ class. *)
(* ======================================================================== *)

Context {sync_pkg : sync.Assumptions}.
Context {seq_inG : inG Σ (gmapUR loc (authR (mraUR (A := list (YjsItem A)) sublist)))}.

(** Doc handle (persistent): reads ONLY [Doc.store] (immutable ⇒ [↦□]) and
    delegates to [is_Store]. The store now owns the [types] registry, so there
    is nothing else of the Doc to own. *)
Definition is_Doc (dv s_loc : loc) (γ : gname) : iProp Σ :=
  ∃ (dvv : yjs.Doc.t),
    "Hdoc" ∷ dv ↦□ dvv ∗
    "%Hstore" ∷ ⌜dvv.(yjs.Doc.store') = s_loc⌝ ∗
    "His_store" ∷ is_Store s_loc γ.

(** Text handle (persistent), now parameterized by a known item sub-sequence
    [arr]: reads ONLY its OWN fields ([doc]/[inner]/[name], all immutable ⇒ [↦□])
    plus [is_text_lb], which both (a) witnesses the inner YType is registered and
    (b) records that [arr] is a [sublist] LOWER BOUND of the text's current
    content. Says NOTHING about store fields. Persistent ⇒ the [Insert] spec is
    pre/post in the same predicate (with [arr] growing). The user can read off
    [text_of arr] as a lower bound on the current string. *)
Definition is_Text (t : loc) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ (tv : yjs.Text.t) (dv s_loc parent : loc) (name : go_string) (γ : gname),
    "Ht" ∷ t ↦□ tv ∗
    "%Hdoc" ∷ ⌜tv.(yjs.Text.doc') = dv⌝ ∗
    "%Hinner" ∷ ⌜tv.(yjs.Text.inner') = parent⌝ ∗
    "%Hname" ∷ ⌜tv.(yjs.Text.name') = name⌝ ∗
    "His_doc" ∷ is_Doc dv s_loc γ ∗
    "His_lb" ∷ is_text_lb γ parent arr.

#[global] Instance is_Doc_persistent dv s_loc γ : Persistent (is_Doc dv s_loc γ).
Proof. apply _. Qed.
#[global] Instance is_Text_persistent t arr : Persistent (is_Text t arr).
Proof. apply _. Qed.

(** Target public spec (replaces the [own_insert_doc] [wp_Text__Insert] above).
    [is_Text] is persistent, so the precondition lower bound [arr] is kept; the
    postcondition exposes the new content [arr'] (a [sublist] super-sequence):

      {{{ is_pkg_init yjs ∗ is_Text t arr }}}
        t @! (go.PointerType yjs.Text) @! "Insert" #idx #content
      {{{ (arr' : list (YjsItem A)), RET #();
          is_Text t arr' ∗ ⌜sublist arr arr'⌝ }}}

    Sketch: peel [is_Text → is_Doc → is_Store] to reach [is_Mutex]; [Lock] yields
    [store_inv]; combine [is_text_lb] with [Hseq] (auth) to learn [parent ∈ dom
    texts] and extract THIS text's [text_state] / DLL from [Htexts]; run the
    existing findPos/Integrate loop (Integrate now also [AddNode]s into the global
    items map, re-establishing [is_item_map] via [maximalId]); update the auth to
    the grown sequence (mra update, [sublist] old new) and mint the new
    [is_text_lb] fragment; reinsert the [text_state], rebuild [store_inv];
    [Unlock]; return [is_Text t arr']. The old [uint.Z k + len < 2^63] overflow
    side condition is gone — [k] is hidden in the lock, so it moves to a Go-side
    overflow guard in [Text.Insert]. *)

End text.
