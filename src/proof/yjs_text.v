(** WP proofs for the [Text] / [yType] methods: visible-index navigation
    ([yType.findPos], proved) and the top-level [Text.Insert] (spec [Admitted] —
    the lock-based proof is the core remaining work; see the design below).

    [is_Text] is the Text-handle invariant, delegating to the store lock
    ([is_Store] / [is_text_lb] in [yjs_store]); the findPos proofs and the
    [insert_item_valid] / [insert_maximalId] helpers feed [wp_Text__Insert]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id yjs_item yjs_store.
(* Require (not Import) at top: Importing iris.algebra retunes the [<] scope and
   breaks the verified findPos word-arithmetic proofs. Imported inside the section
   just before the design block. *)
From New.proof.sync_proof Require mutex.               (* is_Mutex / Lock / Unlock *)
From iris.algebra Require auth gmap gset.              (* is_text_lb grow-only item-set RA *)
From stdpp Require sorting.                            (* StronglySorted / sublist *)

Section text.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.


(** findPos on an empty sequence returns (null, null) without reading any flags
    (both loops have an empty list to walk). *)
Lemma wp_yText__findPos_empty (parent : loc) (idx : w64) :
  {{{ is_pkg_init yjs ∗ is_ytext parent [] [] }}}
    parent @! (go.PointerType yjs.yType) @! "findPos" #idx
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
    parent @! (go.PointerType yjs.yType) @! "findPos" #idx
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
    have Hstartnn : yt.(yjs.yType.start') ≠ null by (rewrite Hhead; exact Hnn0).
    iAssert ("Hp" ∷ parent ↦ yt ∗ "Hdll" ∷ is_dll yt.(yjs.yType.start') tl null null (c0 :: cs) ∗ "Hindex" ∷ index_ptr ↦ idx ∗ "Hleftp" ∷ left_ptr ↦ null ∗ "Hrightp" ∷ right_ptr ↦ yt.(yjs.yType.start'))%I
      with "[Hparent Hdll index left right]" as "IH".
    { iFrame. }
    wp_for "IH".
    rewrite (bool_decide_eq_false_2 (yt.(yjs.yType.start') = null) Hstartnn). simpl negb.
    have Hstart_c0 : yt.(yjs.yType.start') = ic_loc c0 by (rewrite Hhead /node_loc /=; reflexivity).
    have [yi0 [Hyi0 Hcr0]] := cells_repr_lookup arr (c0 :: cs) arr 0%nat c0 Hrepr Hc0.
    have Hflags0 : (ic_val c0).(yjs.item.flags') = W8 2 := proj1 (proj2 (proj2 (proj2 (proj2 Hcr0)))).
    iDestruct (is_dll_acc (c0 :: cs) yt.(yjs.yType.start') tl 0%nat c0 Hc0 with "Hdll") as "H". iNamed "H".
    iEval (rewrite Hstart_c0) in "Hrightp".
    wp_auto.
    wp_apply (wp_item__Deleted c0.(ic_loc) c0.(ic_val) Hflags0 with "[$Hcval]"). iIntros "Hcval".
    rewrite decide_False; [| done]. rewrite decide_True; [| done].
    iDestruct ("Hback" with "Hcval") as "Hdll".
    wp_auto.
    iAssert (∃ (j : nat) (lloc rloc : loc), "Hp" ∷ parent ↦ yt ∗ "Hdll" ∷ is_dll yt.(yjs.yType.start') tl null null (c0 :: cs) ∗ "Hleftp" ∷ left_ptr ↦ lloc ∗ "Hrightp" ∷ right_ptr ↦ rloc ∗ "Hrem" ∷ remaining_ptr ↦ W64 (uint.Z idx - Z.of_nat j) ∗ "%Hlloc" ∷ ⌜lloc = node_loc (c0 :: cs) (Z.of_nat j - 1)⌝ ∗ "%Hrloc" ∷ ⌜rloc = node_loc (c0 :: cs) (Z.of_nat j)⌝ ∗ "%Hj" ∷ ⌜(j <= uint.nat idx)%nat⌝)%I
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
      iDestruct (is_dll_acc (c0 :: cs) yt.(yjs.yType.start') tl j cj Hcj with "Hdll") as "Hacc".
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


(* Bring the deferred imports into scope here (after the verified proofs). *)
Import New.proof.sync_proof.mutex.
Import iris.algebra.auth iris.algebra.gmap iris.algebra.gset.
Import stdpp.sorting.

(* ======================================================================== *)
(* Text invariant predicate + Text.Insert spec.                               *)
(*                                                                           *)
(* [is_Text] lives here; the Doc-layer predicate [is_Doc] lives in yjs_doc.v   *)
(* (mirrors doc.go). [is_Text] delegates straight to the STORE invariants      *)
(* ([is_Store] / [is_text_lb]) in yjs_store, so it references only Text's own   *)
(* fields. The [Context] is after the verified findPos proofs so the deferred   *)
(* Imports / assumptions do not perturb them. [wp_Text__Insert] below is        *)
(* [Admitted]: the lock-based proof (Lock → store_inv → findPos/Integrate loop  *)
(* → grow the gset auth → Unlock) is the core remaining work. [seq_inG]         *)
(* duplicates yjs_store's Context; on implementation it folds into global Σ. *)
(* ======================================================================== *)

Context {sync_pkg : sync.Assumptions}.
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR YjsId)))}.

(** Text handle (persistent), parameterized by a SORTED list [L] of known items:
    reads ONLY its OWN fields ([store]/[inner], immutable ⇒ [↦□]) and delegates
    straight to [is_Store] (no Doc hop — Text holds [store] directly). The ghost
    is fed the id-SET of [L] ([is_text_lb] over [gset YjsId], a subset lower bound
    — grow-only, no [mra] needed), while [L] is required [StronglySorted] by the
    document order [YjsLt'] (the order [YjsArrInvariant.yai_sorted] uses). So [L]
    is the CRDT-ordered sub-sequence of the current content on those items: a
    directly-readable lower bound on the string, with a trivial set-only ghost.
    Says NOTHING about store fields. Persistent ⇒ the [Insert] spec is pre/post in
    the same predicate (with [L] growing). *)
Definition is_Text (t : loc) (L : list (YjsItem A)) : iProp Σ :=
  ∃ (tv : yjs.Text.t) (s_loc parent : loc) (γ : gname),
    "Ht" ∷ t ↦□ tv ∗
    "%Hstore" ∷ ⌜tv.(yjs.Text.store') = s_loc⌝ ∗
    "%Hinner" ∷ ⌜tv.(yjs.Text.inner') = parent⌝ ∗
    "His_store" ∷ is_Store s_loc γ ∗
    "His_lb" ∷ is_text_lb γ parent (list_to_set (item_id <$> L)) ∗
    "%Hsorted" ∷ ⌜StronglySorted (λ x y : YjsItem A, YjsLt' (itemPtr x) (itemPtr y)) L⌝.

#[global] Instance is_Text_persistent t L : Persistent (is_Text t L).
Proof. apply _. Qed.

(** [Text.Insert] preserves the (persistent) document handle and grows the known
    content: [is_Text t L] in, [is_Text t L'] out with [L] a [sublist] of [L']
    (the item set grows, and both are [YjsLt']-sorted, so [L ⊑ L']).

    PROOF DEFERRED ([Admitted]) — this is the core remaining work. Sketch: peel
    [is_Text → is_Store] to reach [is_Mutex]; [Lock] yields [store_inv]; combine
    [is_text_lb] with [Hseq] (auth) to learn [parent ∈ dom texts] and extract THIS
    text's [text_state] / DLL from [Htexts]; run the findPos/Integrate loop (and,
    once re-added, Integrate's [AddNode], re-establishing [is_item_map] via
    [maximalId]); grow the auth id-set ([gset] local update, monotone under [⊆])
    and mint the new [is_text_lb]; read [L'] back from the updated DLL / [arr];
    reinsert the [text_state], rebuild [store_inv]; [Unlock]; return [is_Text t L'].
    The old [uint.Z k + len < 2^63] overflow side condition is gone ([k] hidden in
    the lock) — a Go-side overflow guard in [Text.Insert] replaces it. *)
Lemma wp_Text__Insert (t : loc) (idx : w64) (content : go_string) (L : list (YjsItem A)) :
  {{{ is_pkg_init yjs ∗ is_Text t L }}}
    t @! (go.PointerType yjs.Text) @! "Insert" #idx #content
  {{{ (L' : list (YjsItem A)), RET #(); is_Text t L' ∗ ⌜sublist L L'⌝ }}}.
Proof. Admitted.

End text.
