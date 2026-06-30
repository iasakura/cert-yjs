(** WP proofs for the [Text] / [yType] methods: visible-index navigation
    ([yType.findPos]) and the top-level [Text.Insert] (the lock-based per-byte
    Integrate loop), both proved.

    [is_Text] is the Text-handle invariant, delegating to the store lock
    ([is_Store] / [is_text_lb] in [yjs_store]); the findPos proofs and the
    [insert_item_valid] / [insert_maximalId] helpers feed [wp_Text__Insert]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id yjs_item yjs_store.
From New.proof.sync_proof Require Import mutex.        (* is_Mutex / Lock / Unlock *)
From iris.algebra Require Import auth gmap gset.        (* is_text_lb grow-only item-set RA *)
From stdpp Require Import sorting.                      (* StronglySorted / sublist *)

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤];
   the verified findPos word-arithmetic proofs write [Z] comparisons unannotated,
   so restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section text.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
(** Store lock = a [sync.Mutex]; the per-text item set lives in a grow-only auth
    (the same RA as [yjs_store], used by [is_text_lb]). *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

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
    iDestruct (is_dll_acc (c0 :: cs) yt.(yjs.yType.start') tl 0%nat c0 Hc0 with "Hdll") as "H". iNamed "H".
    iEval (rewrite Hstart_c0) in "Hrightp".
    wp_auto.
    wp_apply (wp_item__Deleted c0.(ic_loc) iv Hflags with "[$Hcval]"). iIntros "Hcval".
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
      iDestruct (is_dll_acc (c0 :: cs) yt.(yjs.yType.start') tl j cj Hcj with "Hdll") as "Hacc".
      iDestruct "Hacc" as (ivj olidj oridj) "(%Hcjloc & %Hcjl & %Hcjr & %Hcjid & %Hcjcont & %Hcjolid & %Hcjorid & %Hflagsj & %Hcontlenj & Hcjval & Hcjol & Hcjor & Hback)".
      have Hrlocj : rloc = cj.(ic_loc) by rewrite Hrloc Hcjloc.
      iDestruct (typed_pointsto_not_null with "Hcjval") as %Hcjnn.
      iEval (rewrite Hrlocj) in "Hrightp".
      wp_auto.
      rewrite (bool_decide_eq_false_2 (cj.(ic_loc) = null) Hcjnn). simpl negb.
      rewrite decide_True; [| done]. wp_auto.
      wp_apply (wp_item__Indexable cj.(ic_loc) ivj Hflagsj with "[$Hcjval]"). iIntros "Hcjval".
      wp_auto.
      wp_apply (wp_item__Len cj.(ic_loc) ivj with "[$Hcjval]"). iIntros "Hcjval".
      rewrite Hcontlenj. wp_auto.
      wp_for_post.
      iDestruct ("Hback" with "Hcjval") as "Hdll".
      iFrame "HΦ Hcol Hcor".
      iExists (S j), cj.(ic_loc), (ivj.(yjs.item.right')).
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


(** Two lists [StronglySorted] by the document order [YjsLt'], with [l1]'s
    elements ⊆ [l2]'s (as actual items) and [l2] a valid [YjsArrInvariant] list,
    force [l1] to be a [sublist] of [l2]. The order is a strict order on [l2]'s
    items ([yjs_lt_asymm], hence irreflexive + asymmetric), so the relative
    position of any shared item is forced; the [aux] form keeps the asymmetry
    fact about the FIXED valid set [S = (∈ l2)] as the induction peels [l2]. This
    is what upgrades the item-set lower bound ([list_to_set L ⊆ list_to_set L'])
    into the [sublist L L'] the [Text.Insert] post advertises. *)
Lemma sorted_subseteq_sublist_aux {B : Type} `{EqDecision B} (S : YjsItem B -> Prop)
    (Hasym : ∀ x y, S x -> S y -> YjsLt' (itemPtr x) (itemPtr y) -> YjsLt' (itemPtr y) (itemPtr x) -> False) :
  ∀ (l2 l1 : list (YjsItem B)),
  (∀ x, x ∈ l2 -> S x) ->
  StronglySorted (λ x y : YjsItem B, YjsLt' (itemPtr x) (itemPtr y)) l1 ->
  StronglySorted (λ x y : YjsItem B, YjsLt' (itemPtr x) (itemPtr y)) l2 ->
  (∀ x, x ∈ l1 -> x ∈ l2) ->
  sublist l1 l2.
Proof.
  intros l2. induction l2 as [|y l2' IH]; intros l1 HS Hss1 Hss2 Hsub.
  - destruct l1 as [|x l1']; [apply sublist_nil|].
    exfalso. have Hx : x ∈ ([] : list (YjsItem B)) by (apply Hsub; left). inversion Hx.
  - apply StronglySorted_inv in Hss2 as [Hss2' Hy].
    destruct l1 as [|x l1']; [apply sublist_nil_l|].
    apply StronglySorted_inv in Hss1 as [Hss1' Hx].
    destruct (decide (x = y)) as [->|Hne].
    + apply sublist_skip. apply (IH l1').
      * intros z Hz. apply HS. right. exact Hz.
      * exact Hss1'.
      * exact Hss2'.
      * intros z Hz.
        have Hzl2 : z ∈ (y :: l2') by (apply Hsub; right; exact Hz).
        apply elem_of_cons in Hzl2 as [-> | Hz']; [|exact Hz'].
        exfalso. rewrite Forall_forall in Hx.
        have Ryy : YjsLt' (itemPtr y) (itemPtr y) by (apply Hx; exact Hz).
        apply (Hasym y y); [apply HS; left; reflexivity | apply HS; left; reflexivity | exact Ryy | exact Ryy].
    + apply sublist_cons. apply (IH (x :: l1')).
      * intros z Hz. apply HS. right. exact Hz.
      * constructor; [exact Hss1' | exact Hx].
      * exact Hss2'.
      * intros z Hz.
        have Hzl2 : z ∈ (y :: l2') by (apply Hsub; exact Hz).
        apply elem_of_cons in Hzl2 as [-> | Hz']; [|exact Hz'].
        exfalso.
        apply elem_of_cons in Hz as [Hzx | Hzl1'].
        { apply Hne. symmetry. exact Hzx. }
        have Hxl2 : x ∈ (y :: l2') by (apply Hsub; left).
        apply elem_of_cons in Hxl2 as [Hxy | Hxl2'].
        { apply Hne. exact Hxy. }
        rewrite Forall_forall in Hx. rewrite Forall_forall in Hy.
        have Rxy : YjsLt' (itemPtr x) (itemPtr y) by (apply Hx; exact Hzl1').
        have Ryx : YjsLt' (itemPtr y) (itemPtr x) by (apply Hy; exact Hxl2').
        apply (Hasym x y); [apply HS; right; exact Hxl2' | apply HS; left; reflexivity | exact Rxy | exact Ryx].
Qed.

Lemma sorted_subseteq_sublist {B : Type} `{EqDecision B} (l1 l2 : list (YjsItem B)) :
  YjsArrInvariant l2 ->
  StronglySorted (λ x y : YjsItem B, YjsLt' (itemPtr x) (itemPtr y)) l1 ->
  StronglySorted (λ x y : YjsItem B, YjsLt' (itemPtr x) (itemPtr y)) l2 ->
  (∀ x, x ∈ l1 -> x ∈ l2) ->
  sublist l1 l2.
Proof.
  intros Hinv Hss1 Hss2 Hsub.
  apply (sorted_subseteq_sublist_aux (λ x, x ∈ l2)); [| intros x Hx; exact Hx | exact Hss1 | exact Hss2 | exact Hsub].
  intros x y Hx Hy Rxy Ryx.
  exact (asymmetry.yjs_lt_asymm (yai_closed _ Hinv) (yai_item_set_inv _ Hinv) (itemPtr x) (itemPtr y) Hx Hy Rxy Ryx).
Qed.

(* ----- Text invariant predicate + Text.Insert spec ----------------------
   [is_Text] lives here; the Doc-layer predicate [is_Doc] lives in yjs_doc.v
   (mirrors doc.go). [is_Text] delegates straight to the store invariants
   ([is_Store] / [is_text_lb]) in yjs_store, referencing only Text's own fields.
   [wp_Text__Insert] is proved (Lock → store_inv → findPos/Integrate loop → grow
   the item-set auth → Unlock). *)

(** Text handle (persistent), parameterized by a SORTED list [L] of known items:
    reads ONLY its OWN fields ([store]/[inner], immutable ⇒ [↦□]) and delegates
    straight to [is_Store] (no Doc hop — Text holds [store] directly). The ghost
    is fed the item-SET of [L] ([is_text_lb] over [gset (YjsItem A)], a subset
    lower bound — grow-only, no [mra] needed), while [L] is required
    [StronglySorted] by the document order [YjsLt'] (the order
    [YjsArrInvariant.yai_sorted] uses). Tracking full items (not just ids) pins
    each [x ∈ L] to a genuine document item, so [L] is a real CRDT-ordered
    sub-sequence of the current content (a directly-readable [sublist]/string
    lower bound). Says NOTHING about store fields. Persistent ⇒ the [Insert] spec
    is pre/post in the same predicate (with [L] growing). *)
Definition is_Text (t : loc) (L : list (YjsItem A)) : iProp Σ :=
  ∃ (tv : yjs.Text.t) (s_loc parent : loc) (γ : gname),
    "Ht" ∷ t ↦□ tv ∗
    "%Hstore" ∷ ⌜tv.(yjs.Text.store') = s_loc⌝ ∗
    "%Hinner" ∷ ⌜tv.(yjs.Text.inner') = parent⌝ ∗
    "His_store" ∷ is_Store s_loc γ ∗
    "His_lb" ∷ is_text_lb γ parent (list_to_set L) ∗
    "%Hsorted" ∷ ⌜StronglySorted (λ x y : YjsItem A, YjsLt' (itemPtr x) (itemPtr y)) L⌝.

#[global] Instance is_Text_persistent t L : Persistent (is_Text t L).
Proof. apply _. Qed.

(** [Text.Insert] preserves the (persistent) document handle, grows the known
    content ([L ⊑ L']), AND exposes the inserted run [ins]: one fresh item per
    byte of [content], each now known ([∈ L'], and [∉ L] since its id is fresh),
    carrying that byte as content, with a fresh id [(client, k0+i)] (one local
    [client], consecutive clocks from some [k0]), the run's shared right origin
    [oR], and its left origin chained (item 0 from [oL], item i+1 from item i).
    This says exactly "the characters you inserted are in [L'−L], with these
    content / id / left / right".

    Proof shape: peel [is_Text → is_Store] to reach [is_Mutex]; [Lock] yields
    [store_inv]; combine [is_text_lb] with [Hseq] (auth) via
    [auth_gmap_gset_lookup] to learn [parent ∈ dom texts] and extract THIS text's
    [text_state] / DLL from [Htexts]; run the findPos/Integrate loop, whose
    invariant accumulates [ins] with the per-byte facts (content/id/origins) plus
    [ts_arr ts ⊆ arr]; at exit grow the auth item-set ([ts_arr ts → arr]) with
    [auth_gmap_gset_grow] and mint the new [is_text_lb]; reinsert the grown text
    into [Htexts] ([big_sepM_insert_acc]); rebuild [store_inv] (clock bumped,
    counter [Hctr] preserved); [Unlock]; return with [L' = arr]. The post's
    [sublist L L'] follows from [sorted_subseteq_sublist] (both sorted, [L ⊆ L']
    as items via the item-set ghost), and [it ∉ L] from the fresh clocks vs the
    initial [Hctr]. Overflow is ruled out by a Go-side guard in [Text.Insert]
    (its early return takes the [ins = []] disjunct); [k] stays hidden in the
    lock. Axiom-clean ([Print Assumptions] shows only goose/Perennial axioms). *)
Lemma wp_Text__Insert (t : loc) (idx : w64) (cs : go_string) (L : list (YjsItem A)) :
  {{{ is_pkg_init yjs ∗ is_Text t L }}}
    t @! (go.PointerType yjs.Text) @! "Insert" #idx #cs
  {{{ (L' ins : list (YjsItem A)) (client k0 : nat) (oL oR : YjsPtr A), RET #();
      is_Text t L' ∗ ⌜sublist L L'⌝ ∗
      ⌜ins = [] ∨ length ins = length cs⌝ ∗
      ⌜∀ (i : nat) (it : YjsItem A) (b : w8),
         ins !! i = Some it → cs !! i = Some b →
           it ∈ L' ∧ it ∉ L ∧
           content it = [b] ∧
           item_id it = MkYjsId client (k0 + i)%nat ∧
           rightOrigin it = oR ∧
           (i = 0%nat → origin it = oL) ∧
           (∀ (j : nat) (itj : YjsItem A),
              i = S j → ins !! j = Some itj → origin it = itemPtr itj)⌝ }}}.
Proof.
  (* ---- Prologue: take the store lock, extract THIS text. ---- *)
  wp_start as "Hpre". iNamed "Hpre".
  iDestruct "His_store" as "#His_store".   (* keep is_Store (persistent) for the later Unlock *)
  wp_auto.
  subst s_loc.
  wp_apply (wp_Mutex__Lock with "[$His_store]"). iIntros "[Hlk Hinv]". iNamed "Hinv".
  iDestruct (auth_gmap_gset_lookup with "Hseq His_lb") as %(S' & HmS & HLsub).
  rewrite lookup_fmap in HmS.
  apply fmap_Some in HmS as (ts & Htsp & ->).
  iDestruct (big_sepM_insert_acc _ _ _ _ Htsp with "Htexts") as "[Hbody Hclose]".
  iDestruct "Hbody" as "[Htext %Hinvarr]".
  iDestruct "Htext" as (yt0 tl0) "(Hparent & Hdll & %Hlen & %Hrepr)".
  subst parent. wp_auto.
  case_bool_decide as Hbound.
  { (* ---- out-of-range: index past the visible length, nothing inserted. ---- *)
    wp_auto.
    iDestruct ("Hclose" $! ts with "[Hparent Hdll]") as "Htexts".
    { iSplitL "Hparent Hdll".
      - iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split; [exact Hlen | exact Hrepr].
      - iPureIntro. exact Hinvarr. }
    iEval (rewrite (insert_id texts (tv.(yjs.Text.inner')) ts Htsp)) in "Htexts".
    wp_apply (wp_Mutex__Unlock with "[$His_store $Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Hdset Hseq Htexts]").
    { iNext. iExists client, k, items_mref, types_mref, dset, texts. iFrame. iPureIntro. split; [exact Hctr | exact Hcellctr]. }
    iApply ("HΦ" $! L [] 0%nat 0%nat First Last).
    iSplit.
    { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner'), γ.
      iFrame "Ht His_store His_lb". iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted]. }
    iPureIntro. split_and!.
    - reflexivity.
    - left; reflexivity.
    - intros i it b Hii. rewrite lookup_nil in Hii. inversion Hii. }
  (* ---- in-range: insert one 1-char item per byte. ---- *)
  rewrite Hlen in Hbound.
  have Hposle : (uint.nat idx <= length ts.(ts_cells))%nat by word.
  wp_auto.
  wp_apply strings.wp_string_len. iIntros "%Hlcb".
  wp_auto.
  case_bool_decide as Hovf.
  { (* clock-overflow guard fired: nothing inserted (like OOB). *)
    wp_auto.
    iDestruct ("Hclose" $! ts with "[Hparent Hdll]") as "Htexts".
    { iSplitL "Hparent Hdll".
      - iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split; [exact Hlen | exact Hrepr].
      - iPureIntro. exact Hinvarr. }
    iEval (rewrite (insert_id texts (tv.(yjs.Text.inner')) ts Htsp)) in "Htexts".
    wp_apply (wp_Mutex__Unlock with "[$His_store $Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Hdset Hseq Htexts]").
    { iNext. iExists client, k, items_mref, types_mref, dset, texts. iFrame. iPureIntro. split; [exact Hctr | exact Hcellctr]. }
    iApply ("HΦ" $! L [] 0%nat 0%nat First Last).
    iSplit.
    { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner'), γ.
      iFrame "Ht His_store His_lb". iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted]. }
    iPureIntro. split_and!.
    - reflexivity.
    - left; reflexivity.
    - intros i it b Hii. rewrite lookup_nil in Hii. inversion Hii. }
  (* no overflow: the run fits. *)
  have Hnoof : (uint.Z k + Z.of_nat (length cs) < 2^64)%Z by word.
  wp_auto.
  iAssert (is_ytext (tv.(yjs.Text.inner')) ts.(ts_cells) ts.(ts_arr)) with "[Hparent Hdll]" as "Htext".
  { iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split; [exact Hlen | exact Hrepr]. }
  wp_apply (wp_yText__findPos (tv.(yjs.Text.inner')) ts.(ts_cells) ts.(ts_arr) idx Hposle with "[$Htext]").
  iIntros (lft rgt) "(Htext & %Hlftloc & %Hrgtloc)".
  wp_auto.
  (* shared right origin *)
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗ ∃ (oRptr : loc) (in_rO : option yjs.id.t),
      "HoR" ∷ originRightId_ptr ↦ oRptr ∗ "HisR" ∷ is_origin_id oRptr in_rO ∗
      "Htext" ∷ is_ytext (tv.(yjs.Text.inner')) ts.(ts_cells) ts.(ts_arr) ∗ "Hright" ∷ right_ptr ↦ rgt ∗
      "%Hrightinit" ∷ ⌜(in_rO = None ∧ (uint.nat idx = length ts.(ts_cells))%nat) ∨
        (∃ (ri : YjsItem A) (rid : yjs.id.t), ts.(ts_arr) !! (uint.nat idx) = Some ri ∧ in_rO = Some rid ∧ item_id ri = toYjsId rid)⌝)%I
      with "[right Htext originRightId]".
  { iSplitR; [done|].
    destruct (decide (uint.nat idx = length ts.(ts_cells))%nat) as [Hpeq|Hne].
    - iExists null, None. iFrame "originRightId right Htext".
      iSplit; [by rewrite /is_origin_id | iPureIntro; left; split; [reflexivity | exact Hpeq]].
    - iDestruct "Htext" as (yt1 tl1) "(Hpar1 & Hdll1 & %Hlen1 & %Hrepr1)".
      have Hlt : (uint.nat idx < length ts.(ts_cells))%nat by lia.
      iDestruct (node_loc_lt_not_null ts.(ts_cells) yt1.(yjs.yType.start') tl1 (uint.nat idx) Hlt with "Hdll1") as "[%Hnn _]".
      exfalso. exact (Hnn e). }
  { iDestruct "Htext" as (yt1 tl1) "(Hpar1 & Hdll1 & %Hlen1 & %Hrepr1)".
    have Hposlt : (uint.nat idx < length ts.(ts_cells))%nat.
    { destruct (decide (uint.nat idx < length ts.(ts_cells))%nat) as [Hlt|Hge]; [exact Hlt|exfalso].
      apply n. rewrite /node_loc decide_True; [|lia].
      have Hpe : (uint.nat idx = length ts.(ts_cells))%nat by lia.
      rewrite Hpe Nat2Z.id lookup_ge_None_2; [done|lia]. }
    destruct (ts.(ts_cells) !! uint.nat idx) as [c0|] eqn:Hc0; [| apply lookup_ge_None in Hc0; lia].
    have [yi0 [Hyi0 Hcr0]] := cells_repr_lookup ts.(ts_arr) ts.(ts_cells) ts.(ts_arr) (uint.nat idx) c0 Hrepr1 Hc0.
    rewrite /cell_repr in Hcr0.
    iDestruct (is_dll_acc ts.(ts_cells) yt1.(yjs.yType.start') tl1 (uint.nat idx) c0 Hc0 with "Hdll1") as "Hacc". iNamed "Hacc".
    iEval (rewrite Hcloc) in "Hcval".
    wp_load. wp_pures. wp_store.
    iDestruct (typed_pointsto_not_null with "rid") as %Hridnn.
    iPersist "rid".
    wp_auto.
    iEval (rewrite -Hcloc) in "Hcval".
    iDestruct ("Hback" with "Hcval") as "Hdll1".
    iSplitR; [done|].
    iExists rid_ptr, (Some iv.(yjs.item.id')).
    iFrame "originRightId right".
    iSplitR "Hpar1 Hdll1".
    { rewrite /is_origin_id. iSplit; [iPureIntro; exact Hridnn | iFrame "rid"]. }
    iSplitL "Hpar1 Hdll1".
    { iExists yt1, tl1. iFrame "Hpar1 Hdll1". iPureIntro. split; [exact Hlen1 | exact Hrepr1]. }
    iPureIntro. right. exists yi0, iv.(yjs.item.id'). split_and!; [exact Hyi0 | reflexivity | (rewrite Hcr0; exact Hid)]. }
  iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ". wp_auto.
  (* fix the run's shared right origin oR and the first item's left origin oL as values *)
  assert (∃ (oR : YjsPtr A),
     (in_rO = None ∧ oR = Last ∧ (uint.nat idx = length ts.(ts_arr))%nat) ∨
     (∃ (ri : YjsItem A) (rid : yjs.id.t), ts.(ts_arr) !! (uint.nat idx) = Some ri ∧ in_rO = Some rid ∧ item_id ri = toYjsId rid ∧ oR = itemPtr ri))
     as [oR HoRspec].
  { have Hcl := cells_repr_length ts.(ts_arr) ts.(ts_cells) ts.(ts_arr) Hrepr.
    destruct Hrightinit as [[Hn Hpe] | (ri & rid & Hria & Hrs & Hrid)].
    - exists Last. left. split_and!; [exact Hn | reflexivity | rewrite -Hcl; exact Hpe].
    - exists (itemPtr ri). right. exists ri, rid. split_and!; [exact Hria | exact Hrs | exact Hrid | reflexivity]. }
  assert (∃ (oL : YjsPtr A),
     (oL = First ∧ (uint.nat idx = 0)%nat) ∨
     (∃ li : YjsItem A, (1 <= uint.nat idx)%nat ∧ ts.(ts_arr) !! (uint.nat idx - 1)%nat = Some li ∧ oL = itemPtr li))
     as [oL HoLspec].
  { destruct (decide (uint.nat idx = 0)%nat) as [Hidx0 | Hidxpos].
    - exists First. left. split; [reflexivity | exact Hidx0].
    - have Hidxm : (uint.nat idx - 1 < length ts.(ts_cells))%nat by lia.
      destruct (ts.(ts_cells) !! (uint.nat idx - 1)%nat) as [lc|] eqn:Hlc; [| apply lookup_ge_None in Hlc; lia].
      have [li [Hli Hcrlc]] := cells_repr_lookup ts.(ts_arr) ts.(ts_cells) ts.(ts_arr) (uint.nat idx - 1) lc Hrepr Hlc.
      exists (itemPtr li). right. exists li. split_and!; [lia | exact Hli | reflexivity]. }
  (* loop invariant: [j] inserted so far, [arr]/[cells]/[leftloc] grow, [ins] is the run *)
  iAssert (∃ (j : nat) (arr : list (YjsItem A)) (cells : list item_cell) (leftloc : loc) (ins : list (YjsItem A)),
    "Hi" ∷ i_ptr ↦ W64 j ∗
    "Htptr" ∷ t_ptr ↦ t ∗
    "Hcontentp" ∷ content_ptr ↦ cs ∗
    "Hclientp" ∷ client_ptr ↦ client ∗
    "HoRp" ∷ originRightId_ptr ↦ oRptr ∗
    "Hleftp" ∷ left_ptr ↦ leftloc ∗
    "Hsp" ∷ s_ptr ↦ tv.(yjs.Text.store') ∗
    "Hclient" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "client"] ↦ client ∗
    "Hclock" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "clock"] ↦ W64 (uint.Z k + Z.of_nat j) ∗
    "Hitemsf" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "items"] ↦ items_mref ∗
    "Hitemmap" ∷ is_item_map items_mref (<[tv.(yjs.Text.inner') := MkTextState cells arr]> texts) ∗
    "Htypesf" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "types"] ↦ types_mref ∗
    "Hdset" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "deletedSet"] ↦ dset ∗
    "Hlk" ∷ own_Mutex ((tv.(yjs.Text.store')).[yjs.store.t, "mu"]) ∗
    "Hseq" ∷ own γ (● ((λ ts0 : text_state, (list_to_set ts0.(ts_arr) : gset (YjsItem A))) <$> texts) : authR (gmapUR loc (gsetUR (YjsItem A)))) ∗
    "Hclose" ∷ (∀ x' : text_state, is_ytext tv.(yjs.Text.inner') x'.(ts_cells) x'.(ts_arr) ∗ ⌜YjsArrInvariant x'.(ts_arr)⌝ -∗ [∗ map] kk↦y ∈ <[tv.(yjs.Text.inner'):=x']> texts, is_ytext kk y.(ts_cells) y.(ts_arr) ∗ ⌜YjsArrInvariant y.(ts_arr)⌝) ∗
    "Htextj" ∷ is_ytext (tv.(yjs.Text.inner')) cells arr ∗
    "%Hinvj" ∷ ⌜YjsArrInvariant arr⌝ ∗
    "%Hlenarr" ∷ ⌜length arr = (length ts.(ts_arr) + j)%nat⌝ ∗
    "%Hjle" ∷ ⌜(j <= length cs)%nat⌝ ∗
    "%Hctrj" ∷ ⌜∀ x : YjsItem A, ArrSet arr (itemPtr x) → clientId (item_id x) = uint.nat client → (clock (item_id x) < uint.nat k + j)%nat⌝ ∗
    "%Hleftj" ∷ ⌜(leftloc = null ∧ (uint.nat idx + j = 0)%nat)
      ∨ (∃ (lc : item_cell) (li : YjsItem A),
           cells !! (uint.nat idx + j - 1)%nat = Some lc ∧ ic_loc lc = leftloc ∧
           arr !! (uint.nat idx + j - 1)%nat = Some li ∧
           li = ic_item lc ∧ (1 <= uint.nat idx + j)%nat ∧
           (j = 0%nat → itemPtr li = oL) ∧ (∀ j', j = S j' → ins !! j' = Some li))⌝ ∗
    "%Hrightj" ∷ ⌜(in_rO = None ∧ oR = Last ∧ (uint.nat idx + j = length arr)%nat)
      ∨ (∃ (ri : YjsItem A) (rid : yjs.id.t),
           arr !! (uint.nat idx + j)%nat = Some ri ∧ in_rO = Some rid ∧ item_id ri = toYjsId rid ∧ oR = itemPtr ri)⌝ ∗
    "%Hinslen" ∷ ⌜length ins = j⌝ ∗
    "%Hins" ∷ ⌜∀ (i : nat) (it : YjsItem A), ins !! i = Some it →
       it ∈ arr ∧
       (∀ b : w8, cs !! i = Some b → content it = [b]) ∧
       item_id it = MkYjsId (uint.nat client) (uint.nat k + i)%nat ∧
       rightOrigin it = oR ∧
       (i = 0%nat → origin it = oL) ∧
       (∀ (j' : nat) (itj : YjsItem A), i = S j' → ins !! j' = Some itj → origin it = itemPtr itj)⌝ ∗
    "%Hsubold" ∷ ⌜∀ x : YjsItem A, x ∈ ts.(ts_arr) → x ∈ arr⌝ ∗
    "%Hcellbnd" ∷ ⌜∀ c0 : item_cell, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTextState cells arr]> texts) →
       cell_client c0 = client → (uint.Z (cell_clock c0) < uint.Z k + Z.of_nat j)%Z⌝
    )%I with "[i t content client HoR left s Hclient Hclock Hitemsf Hitemmap Htypesf Hdset Hlk Hseq Hclose Htext]" as "IH".
  { iExists 0%nat, ts.(ts_arr), ts.(ts_cells), lft, [].
    replace (W64 (uint.Z k + Z.of_nat 0)) with k by word.
    have Hts_eta : MkTextState ts.(ts_cells) ts.(ts_arr) = ts by (destruct ts; reflexivity).
    rewrite Hts_eta (insert_id texts (tv.(yjs.Text.inner')) ts Htsp).
    iFrame "i t content client HoR left s Hclient Hclock Hitemsf Hitemmap Htypesf Hdset Hlk Hseq Hclose Htext".
    iPureIntro. split_and!.
    - exact Hinvarr.
    - lia.
    - lia.
    - intros x Hx Hc. have := Hctr (tv.(yjs.Text.inner')) ts x Htsp Hx Hc. lia.
    - destruct HoLspec as [[HoLF Hidx0] | (li & Hge1 & Hli & HoLi)].
      + left. split; [| lia].
        rewrite Hlftloc /node_loc. case_decide as Hd; [exfalso; rewrite Hidx0 in Hd; simpl in Hd; lia | reflexivity].
      + right.
        have Hidxm : (uint.nat idx - 1 < length ts.(ts_cells))%nat by lia.
        destruct (ts.(ts_cells) !! (uint.nat idx - 1)%nat) as [lc|] eqn:Hlc; [| apply lookup_ge_None in Hlc; lia].
        have [li2 [Hli2 Hcrlc]] := cells_repr_lookup ts.(ts_arr) ts.(ts_cells) ts.(ts_arr) (uint.nat idx - 1) lc Hrepr Hlc.
        rewrite /cell_repr in Hcrlc.
        exists lc, li2. split_and!.
        * replace (uint.nat idx + 0 - 1)%nat with (uint.nat idx - 1)%nat by lia. exact Hlc.
        * rewrite Hlftloc /node_loc. case_decide as Hd; [| lia].
          have -> : Z.to_nat (Z.of_nat (uint.nat idx) - 1) = (uint.nat idx - 1)%nat by lia.
          rewrite Hlc //.
        * replace (uint.nat idx + 0 - 1)%nat with (uint.nat idx - 1)%nat by lia. exact Hli2.
        * exact Hcrlc.
        * lia.
        * intros _. rewrite HoLi. f_equal. rewrite Hli in Hli2. injection Hli2 as ->. reflexivity.
        * intros j' Hj'. lia.
    - destruct HoRspec as [(Hn & HoRl & Hidxlen) | (ri & rid & Hria & Hrs & Hrid & HoRi)].
      + left. split_and!; [exact Hn | exact HoRl | rewrite Nat.add_0_r; exact Hidxlen].
      + right. exists ri, rid. split_and!; [rewrite Nat.add_0_r; exact Hria | exact Hrs | exact Hrid | exact HoRi].
    - reflexivity.
    - intros i it Hii. rewrite lookup_nil in Hii. inversion Hii.
    - intros x Hx. exact Hx.
    - intros c0 Hc0 Hcc0. have := Hcellctr c0 Hc0 Hcc0. lia. }
  wp_for "IH".
  wp_apply strings.wp_string_len. iIntros "%Hlcb2". wp_auto. case_bool_decide as Hjlt.
  { (* loop body: integrate the [j]-th character *)
    have Hjpos : (j < length cs)%nat by word.
    rewrite decide_True; [| reflexivity].
    wp_auto.
    (* left origin = current [left] (the previously inserted item, or findPos's left) *)
    wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗
      ∃ (oLptr : loc) (olo : option yjs.id.t),
        "HoL" ∷ originLeftId_ptr ↦ oLptr ∗
        "HisL" ∷ is_origin_id oLptr olo ∗
        "Htextj" ∷ is_ytext tv.(yjs.Text.inner') cells arr ∗
        "Hleftp" ∷ left_ptr ↦ leftloc ∗
        "%Hleftspec" ∷ ⌜(olo = None ∧ (uint.nat idx + length ins = 0)%nat) ∨
           (∃ (li : YjsItem A), (1 <= uint.nat idx + length ins)%nat ∧ arr !! (uint.nat idx + length ins - 1)%nat = Some li ∧ (toYjsId <$> olo) = Some (item_id li))⌝)%I
      with "[Hleftp Htextj originLeftId]".
    { destruct Hleftj as [[Hln Hpe0] | (lc & li & Hlccells & Hlcloc & Hliarr & Hliitem & Hge1 & _)].
      - iSplitR; [done|]. iExists null, None. iFrame "originLeftId Htextj Hleftp".
        iSplit; [by rewrite /is_origin_id|]. iPureIntro. left. split; [reflexivity | exact Hpe0].
      - iDestruct "Htextj" as (yth tlh) "(Hpar & Hdll & %Hlenh & %Hreprh)".
        iDestruct (is_dll_acc cells yth.(yjs.yType.start') tlh (uint.nat idx + length ins - 1)%nat lc Hlccells with "Hdll") as "Hacc". iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hcval") as %Hlcnn.
        exfalso. exact (Hlcnn Hlcloc). }
    { destruct Hleftj as [[Hln _] | (lc & li & Hlccells & Hlcloc & Hliarr & Hliitem & Hge1 & _)].
      { exfalso; exact (n Hln). }
      iDestruct "Htextj" as (yth tlh) "(Hpar & Hdll & %Hlenh & %Hreprh)".
      iDestruct (is_dll_acc cells yth.(yjs.yType.start') tlh (uint.nat idx + length ins - 1)%nat lc Hlccells with "Hdll") as "Hacc". iNamed "Hacc".
      iEval (rewrite Hlcloc) in "Hcval".
      wp_method_call. wp_call. wp_auto.
      wp_method_call. wp_call. rewrite /yjs.item__LastIdⁱᵐᵖˡ. wp_auto.
      wp_alloc icopy as "Hic". wp_auto.
      wp_bind (icopy @! (go.PointerType yjs.item) @! "Len" (# ()))%E.
      wp_apply (wp_item__Len icopy iv with "[$Hic]"). iIntros "Hic".
      rewrite Hcontlen. wp_pures. wp_store.
      iDestruct (typed_pointsto_not_null with "lid") as %Hlidnn.
      iPersist "lid". wp_auto.
      iEval (rewrite -Hlcloc) in "Hcval".
      iDestruct ("Hback" with "Hcval") as "Hdll".
      iSplitR; [done|].
      iExists lid_ptr, (Some {| yjs.id.clientId' := iv.(yjs.item.id').(yjs.id.clientId'); yjs.id.clock' := w64_word_instance.(word.sub) (w64_word_instance.(word.add) iv.(yjs.item.id').(yjs.id.clock') (W64 1%nat)) (W64 1) |}).
      iFrame "originLeftId Hleftp".
      iSplitR "Hpar Hdll".
      { rewrite /is_origin_id. iSplit; [iPureIntro; exact Hlidnn | iFrame "lid"]. }
      iSplitL "Hpar Hdll".
      { iExists yth, tlh. iFrame "Hpar Hdll". iPureIntro. split; [exact Hlenh | exact Hreprh]. }
      have Hliid : item_id li = toYjsId iv.(yjs.item.id') by (rewrite Hliitem; exact Hid).
      iPureIntro. right. exists li. split_and!.
      - exact Hge1.
      - exact Hliarr.
      - rewrite Hliid /toYjsId /=. f_equal. f_equal. word. }
    iIntros (v) "[%Hv HQL]". subst v. iNamed "HQL". wp_auto.
    wp_func_call. wp_call.
    destruct (cs !! sint.nat (W64 j)) as [b|] eqn:Hb;
      [ wp_auto | exfalso; apply lookup_ge_None in Hb; revert Hb Hjlt Hlcb2; word ].
    wp_alloc client_l as "Hcl2". wp_auto.
    rewrite Hb. wp_auto. wp_func_call. wp_call.
    wp_alloc oR2 as "HoR2". wp_auto. wp_alloc oL2 as "HoL2". wp_auto.
    (* build the model item [nit] and integrate *)
    have Hclocknit : uint.nat (W64 (uint.Z k + j)) = (uint.nat k + j)%nat by word.
    rewrite Hinslen in Hleftspec.
    have Horig : ∃ (o : YjsPtr A),
       (toYjsId <$> olo = None ∧ o = First ∧ (uint.nat idx + j)%nat = 0%nat) ∨
       (∃ li, (1 <= uint.nat idx + j)%nat ∧ arr !! (uint.nat idx + j - 1)%nat = Some li ∧ toYjsId <$> olo = Some (item_id li) ∧ o = itemPtr li).
    { destruct Hleftspec as [[Hon Hp0] | (li & Hge & Hla & Hom)].
      - exists First. left. subst olo. split_and!; [reflexivity | reflexivity | exact Hp0].
      - exists (itemPtr li). right. exists li. split_and!; [exact Hge | exact Hla | exact Hom | reflexivity]. }
    destruct Horig as [morigin Horig].
    have Hrorig : ∃ (r : YjsPtr A),
       (toYjsId <$> in_rO = None ∧ r = Last ∧ (uint.nat idx + j)%nat = length arr) ∨
       (∃ ri, arr !! (uint.nat idx + j)%nat = Some ri ∧ toYjsId <$> in_rO = Some (item_id ri) ∧ r = itemPtr ri).
    { destruct Hrightj as [(Hrn & Hoeq & Hpl) | (ri & rid & Hria & Hros & Hrii & HoRi)].
      - exists Last. left. subst in_rO. split_and!; [reflexivity | reflexivity | exact Hpl].
      - exists (itemPtr ri). right. exists ri. split_and!; [exact Hria | rewrite Hros /= Hrii // | reflexivity]. }
    destruct Hrorig as [mrightorigin Hrorig].
    set (in_id1 := MkYjsId (uint.nat client) (uint.nat (W64 (uint.Z k + j)))).
    set (input := MkIntegrateInput (toYjsId <$> olo) (toYjsId <$> in_rO) ([b] : A) in_id1).
    set (nit := Item (A:=A) morigin mrightorigin in_id1 [b]).
    have Htoitem : toItem input arr = Some nit.
    { apply (toItem_at arr in_id1 [b] morigin mrightorigin (toYjsId <$> olo) (toYjsId <$> in_rO) Hinvj).
      - destruct Horig as [(Hon & Ho & _) | (li & _ & Hla & Hom & Ho)]; [left; split; [exact Hon | exact Ho] | right; exists li; split_and!; [exact Hom | exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hla) | exact Ho]].
      - destruct Hrorig as [(Hrn & Hr & _) | (ri & Hria & Hri & Hr)]; [left; split; [exact Hrn | exact Hr] | right; exists ri; split_and!; [exact Hri | exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hria) | exact Hr]]. }
    have Hvalid : IsItemValid nit :=
      insert_item_valid arr (uint.nat idx + j) in_id1 [b] morigin mrightorigin
        (toYjsId <$> olo) (toYjsId <$> in_rO) Hinvj Horig Hrorig.
    have Hmax' : maximalId nit arr.
    { apply (insert_maximalId arr morigin mrightorigin (uint.nat client) (uint.nat (W64 (uint.Z k + j))) [b]).
      intros x Hx Hc. rewrite Hclocknit. exact (Hctrj x Hx Hc). }
    iDestruct "HisR" as "#HisRp".
    iAssert (is_fresh_item oL2 input) with "[HoL2 HisL]" as "Hfresh".
    { iExists _, olo, in_rO. rewrite /is_fresh_item_raw /=. iFrame "HoL2 HisL HisRp". iPureIntro. split_and!; reflexivity. }
    have Hlookj : (<[tv.(yjs.Text.inner') := MkTextState cells arr]> texts) !! tv.(yjs.Text.inner')
                  = Some (MkTextState cells arr) by apply lookup_insert_eq.
    have Hgmaxj : ∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTextState cells arr]> texts) →
                    cell_client c0 = W64 (clientId (item_id nit)) →
                    (uint.Z (cell_clock c0) < uint.Z (W64 (clock (item_id nit))))%Z.
    { intros c0 Hc0 Hcc0.
      have Hcl0 : cell_client c0 = client by (rewrite Hcc0 /nit /in_id1 /=; word).
      have Hrhs : uint.Z (W64 (clock (item_id nit))) = uint.Z k + Z.of_nat j
        by (rewrite /nit /in_id1 /= Hclocknit; word).
      rewrite Hrhs. exact (Hcellbnd c0 Hc0 Hcl0). }
    wp_apply (wp_Store__Integrate (tv.(yjs.Text.store')) (tv.(yjs.Text.inner')) oL2 arr input nit cells
                (<[tv.(yjs.Text.inner') := MkTextState cells arr]> texts) items_mref
                Hinvj Htoitem Hvalid Hmax' Hlookj Hgmaxj with "[$Hfresh $Htextj $Hitemsf $Hitemmap]").
    iIntros (arr' iidx cells' c) "(%Hile & %Harr'eq & %Hinv' & Htext' & Hitemsf & Hitemmap & %Hpermc & %Hnode)".
    have Hinsins : <[tv.(yjs.Text.inner') := MkTextState cells' arr']>
                 (<[tv.(yjs.Text.inner') := MkTextState cells arr]> texts)
             = <[tv.(yjs.Text.inner') := MkTextState cells' arr']> texts.
    { rewrite insert_insert. case_decide as Hd; [reflexivity | congruence]. }
    iEval (rewrite Hinsins) in "Hitemmap".
    wp_auto.
    (* place the new item, identify its index *)
    have Hcllen0 := cells_repr_length ts.(ts_arr) ts.(ts_cells) ts.(ts_arr) Hrepr.
    have Hple : (uint.nat idx + j <= length arr)%nat by (rewrite Hlenarr; lia).
    have Hplace : arr' = take (uint.nat idx + j)%nat arr ++ nit :: drop (uint.nat idx + j)%nat arr.
    { rewrite Harr'eq. apply (insert_straddle arr nit iidx (uint.nat idx + j)%nat Hinvj ltac:(rewrite -Harr'eq; exact Hinv') Hile Hple).
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
    destruct Hnode as [x (Hcx & Hcloc & Hcid)].
    destruct (cells_repr_lookup arr' cells' arr' x c Hrepr3 Hcx) as [yi [Hyi Hcr3]].
    have HnitIn : nit ∈ arr' by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hnitpos).
    (* Integrate's post now pins the inserted cell directly: ic_item c = nit. *)
    have Hyinit : yi = nit.
    { have Hcr3eq : yi = ic_item c := Hcr3. rewrite Hcr3eq. exact Hcid. }
    subst yi.
    have Hxpos : x = (uint.nat idx + j)%nat.
    { destruct (Nat.lt_trichotomy x (uint.nat idx + j)%nat) as [Hlt|[Heq|Hgt]]; [exfalso|exact Heq|exfalso].
      - have HH := invariant_yjsarray_idx.getElem_lt_YjsLt' arr' x (uint.nat idx + j)%nat nit nit Hinv' Hyi Hnitpos Hlt.
        exact (asymmetry.yjs_lt_asymm (yai_closed _ Hinv') (yai_item_set_inv _ Hinv') (itemPtr nit) (itemPtr nit) HnitIn HnitIn HH HH).
      - have HH := invariant_yjsarray_idx.getElem_lt_YjsLt' arr' (uint.nat idx + j)%nat x nit nit Hinv' Hnitpos Hyi Hgt.
        exact (asymmetry.yjs_lt_asymm (yai_closed _ Hinv') (yai_item_set_inv _ Hinv') (itemPtr nit) (itemPtr nit) HnitIn HnitIn HH HH). }
    subst x.
    wp_for_post.
    (* re-establish the loop invariant for [S j] with [ins ++ [nit]] *)
    iFrame "Ht His_lb HΦ HisRp".
    iExists (S j), arr', cells', oL2, (ins ++ [nit]).
    replace (W64 (uint.Z k + Z.of_nat (S j))) with (w64_word_instance.(word.add) (W64 (uint.Z k + j)) (W64 1)) by word.
    replace (W64 (S j)) with (w64_word_instance.(word.add) (W64 j) (W64 1)) by word.
    iFrame "Hi Htptr Hcontentp Hclientp HoRp Hleftp Hsp Hclient Hclock Hitemsf Hitemmap Htypesf Hdset Hlk Hseq Hclose".
    iSplitL "Hp3 Hdll3".
    { iExists yt3, tl3. iFrame "Hp3 Hdll3". iPureIntro. split; [exact Hlen3 | exact Hrepr3]. }
    have HmroR : mrightorigin = oR.
    { destruct in_rO as [rid|] eqn:Hino.
      - destruct Hrorig as [(Hrn & _ & _) | (ri & Hria & _ & Hmr)]; [simpl in Hrn; discriminate |].
        destruct Hrightj as [(Hrn2 & _ & _) | (ri2 & rid2 & Hria2 & _ & _ & HoRi)]; [discriminate |].
        rewrite Hmr HoRi. rewrite Hria in Hria2. injection Hria2 as ->. reflexivity.
      - destruct Hrorig as [(_ & Hmr & _) | (ri & _ & Hri & _)]; [| simpl in Hri; discriminate].
        destruct Hrightj as [(_ & HoRl & _) | (ri2 & rid2 & _ & Hros2 & _ & _)]; [| discriminate].
        rewrite Hmr HoRl //. }
    iPureIntro. split_and!.
    - exact Hinv'.
    - rewrite Hplace length_app length_take_le; [| exact Hple]. simpl. rewrite length_drop. lia.
    - lia.
    - intros x Hx Hc. rewrite Hplace in Hx.
      apply elem_of_app in Hx as [Hxt | Hxc].
      + have Hxa : ArrSet arr x by (rewrite -(take_drop (uint.nat idx + j)%nat arr); apply elem_of_app; left; exact Hxt).
        have := Hctrj x Hxa Hc. lia.
      + apply elem_of_cons in Hxc as [-> | Hxd].
        * rewrite /nit /in_id1 /=. rewrite Hclocknit. lia.
        * have Hxa : ArrSet arr x by (rewrite -(take_drop (uint.nat idx + j)%nat arr); apply elem_of_app; right; exact Hxd).
          have := Hctrj x Hxa Hc. lia.
    - right. exists c, nit. split_and!.
      + replace (uint.nat idx + S j - 1)%nat with (uint.nat idx + j)%nat by lia. exact Hcx.
      + exact Hcloc.
      + replace (uint.nat idx + S j - 1)%nat with (uint.nat idx + j)%nat by lia. exact Hnitpos.
      + exact Hcr3.
      + lia.
      + intros Hsj. lia.
      + intros j' Hsj. injection Hsj as ->. rewrite lookup_app_r; [| rewrite Hinslen; lia]. rewrite Hinslen. rewrite Nat.sub_diag. reflexivity.
    - destruct Hrightj as [(Hrn & HoRl & Hpl) | (ri & rid & Hria & Hros & Hrii & HoRi)].
      + left. split_and!; [exact Hrn | exact HoRl |].
        rewrite Hplace length_app length_take_le; [| exact Hple]. simpl. rewrite length_drop. lia.
      + right. exists ri, rid. split_and!.
        * replace (uint.nat idx + S j)%nat with (uint.nat idx + j + 1)%nat by lia. rewrite Hshift. exact Hria.
        * exact Hros.
        * exact Hrii.
        * exact HoRi.
    - rewrite length_app Hinslen /=. lia.
    - intros i it Hii.
      destruct (decide (i < length ins)%nat) as [Hilt | Hige].
      + rewrite lookup_app_l in Hii; [| exact Hilt].
        have [Hitin [Hcont [Hid [Hror [Horg Hchain]]]]] := Hins i it Hii.
        split_and!.
        * rewrite Hplace. rewrite -(take_drop (uint.nat idx + j)%nat arr) in Hitin. apply elem_of_app in Hitin as [H1 | H2]; [apply elem_of_app; left; exact H1 | apply elem_of_app; right; apply elem_of_cons; right; exact H2].
        * exact Hcont.
        * exact Hid.
        * exact Hror.
        * exact Horg.
        * intros j' itj Hisj Hlookj'. rewrite lookup_app_l in Hlookj'; [| lia]. exact (Hchain j' itj Hisj Hlookj').
      + have Hieq : i = length ins.
        { apply lookup_lt_Some in Hii. rewrite length_app /= in Hii. lia. }
        rewrite Hieq lookup_app_r in Hii; [| lia]. rewrite Nat.sub_diag /= in Hii. injection Hii as <-.
        split_and!.
        * exact HnitIn.
        * intros b0 Hcsb. have Hsn : sint.nat (W64 j) = j by word. rewrite Hsn in Hb. rewrite Hieq Hinslen in Hcsb. rewrite Hb in Hcsb. injection Hcsb as Hbb. rewrite /nit /= Hbb //.
        * rewrite /nit /in_id1 /=. rewrite Hieq Hinslen Hclocknit. reflexivity.
        * rewrite /nit /=. exact HmroR.
        * intros Hi0. rewrite /nit /=. rewrite Hieq Hinslen in Hi0.
          destruct Horig as [(_ & Hmo & Hp0) | (li & Hge & Hla & _ & Hmo)].
          -- rewrite Hmo. destruct HoLspec as [[HoLF _] | (li2 & Hge2 & _ & _)]; [rewrite HoLF // | lia].
          -- rewrite Hmo. destruct Hleftj as [[_ Hp0] | (lc2 & li2 & _ & _ & Hla2 & _ & _ & Hlk0 & _)]; [lia |]. have -> : li = li2 by (rewrite Hla in Hla2; injection Hla2 as ->; reflexivity). exact (Hlk0 Hi0).
        * intros j' itj Hisj Hlookj'. rewrite /nit /=. rewrite Hieq Hinslen in Hisj. rewrite lookup_app_l in Hlookj'; [| rewrite Hinslen; lia].
          destruct Horig as [(_ & _ & Hp0) | (li & Hge & Hla & _ & Hmo)]; [lia |].
          rewrite Hmo. destruct Hleftj as [[_ Hp0] | (lc2 & li2 & _ & _ & Hla2 & _ & _ & _ & Hlk)]; [lia |]. have -> : li = li2 by (rewrite Hla in Hla2; injection Hla2 as ->; reflexivity). have Hli2 := Hlk j' Hisj. rewrite Hli2 in Hlookj'. injection Hlookj' as <-. reflexivity.
    - intros x Hx. have Hxa := Hsubold x Hx. rewrite Hplace. rewrite -(take_drop (uint.nat idx + j)%nat arr) in Hxa. apply elem_of_app in Hxa as [H1 | H2]; [apply elem_of_app; left; exact H1 | apply elem_of_app; right; apply elem_of_cons; right; exact H2].
    - intros c0 Hc0 Hcc0.
      have Hac_step : all_cells (<[tv.(yjs.Text.inner') := MkTextState cells' arr']> texts)
                    ≡ₚ all_cells (<[tv.(yjs.Text.inner') := MkTextState cells arr]> texts) ++ [c].
      { rewrite -Hinsins.
        apply (all_cells_insert_snoc (<[tv.(yjs.Text.inner') := MkTextState cells arr]> texts)
                 (tv.(yjs.Text.inner')) cells arr cells' arr' c Hlookj Hpermc). }
      rewrite Hac_step in Hc0. apply elem_of_app in Hc0 as [Hold | Hnew].
      + have := Hcellbnd c0 Hold Hcc0. lia.
      + apply list_elem_of_singleton in Hnew as ->.
        rewrite /cell_clock Hcid /nit /in_id1 /=. rewrite Hclocknit. word. }
  (* loop exit: the whole run is integrated; rebuild [store_inv] and return. *)
  have Hjend : (j = length cs)%nat by word.
  rewrite decide_False; [| done]. wp_auto.
  rewrite decide_True; [| reflexivity]. wp_auto.
  have Hk'val : uint.nat (W64 (uint.Z k + j)) = (uint.nat k + j)%nat by word.
  have Hsubarr : list_to_set (ts.(ts_arr)) ⊆ (list_to_set arr : gset (YjsItem A)).
  { intros y Hy. rewrite elem_of_list_to_set in Hy. rewrite elem_of_list_to_set. apply Hsubold. exact Hy. }
  have Hmk : ((λ ts0 : text_state, (list_to_set (ts_arr ts0) : gset (YjsItem A))) <$> texts) !! (tv.(yjs.Text.inner')) = Some (list_to_set ts.(ts_arr)).
  { rewrite lookup_fmap Htsp //. }
  iMod (auth_gmap_gset_grow γ _ (tv.(yjs.Text.inner')) (list_to_set ts.(ts_arr)) (list_to_set arr) Hmk Hsubarr with "Hseq") as "[Hseq Hfrag]".
  iDestruct ("Hclose" $! (MkTextState cells arr) with "[Htextj]") as "Htexts".
  { iFrame "Htextj". iPureIntro. exact Hinvj. }
  wp_apply (wp_Mutex__Unlock with "[$His_store $Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Hdset Hseq Htexts]").
  { iNext. iExists client, (W64 (uint.Z k + j)), items_mref, types_mref, dset, (<[tv.(yjs.Text.inner') := MkTextState cells arr]> texts).
    iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Hdset".
    rewrite fmap_insert /=. iFrame "Hseq Htexts".
    iPureIntro. split.
    - intros parent' ts' x Hlook Hxin Hxc. rewrite Hk'val.
      destruct (decide (parent' = tv.(yjs.Text.inner'))) as [-> | Hne].
      + rewrite lookup_insert in Hlook. rewrite decide_True in Hlook; [| reflexivity]. injection Hlook as <-. simpl in Hxin. exact (Hctrj x Hxin Hxc).
      + rewrite lookup_insert_ne in Hlook; last (intros HH; apply Hne; symmetry; exact HH).
        have := Hctr parent' ts' x Hlook Hxin Hxc. lia.
    - intros c0 Hc0 Hcc0.
      have Hkw : uint.Z (W64 (uint.Z k + Z.of_nat j)) = uint.Z k + Z.of_nat j by word.
      rewrite Hkw. exact (Hcellbnd c0 Hc0 Hcc0). }
  iApply ("HΦ" $! arr ins (uint.nat client) (uint.nat k) oL oR).
  iSplitL "Hfrag Ht".
  { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner'), γ. iFrame "Ht His_store Hfrag". iPureIntro. split_and!; [reflexivity | reflexivity | exact (yai_sorted _ Hinvj)]. }
  iSplit.
  { iPureIntro. apply (sorted_subseteq_sublist L arr Hinvj Hsorted (yai_sorted _ Hinvj)).
    intros x Hx. have Hxg : x ∈ (list_to_set arr : gset (YjsItem A)).
    { apply Hsubarr. apply HLsub. rewrite elem_of_list_to_set. exact Hx. }
    rewrite elem_of_list_to_set in Hxg. exact Hxg. }
  iSplit.
  { iPureIntro. right. rewrite Hinslen. exact Hjend. }
  iPureIntro. intros i it b Hii Hcsb.
  have [Hitin [Hcont [Hid [Hror [Horg Hchain]]]]] := Hins i it Hii.
  split_and!.
  - exact Hitin.
  - intros HinL. have HitTs : it ∈ ts.(ts_arr).
    { have Htg : it ∈ (list_to_set ts.(ts_arr) : gset (YjsItem A)).
      { apply HLsub. rewrite elem_of_list_to_set. exact HinL. }
      rewrite elem_of_list_to_set in Htg. exact Htg. }
    have Hclk := Hctr (tv.(yjs.Text.inner')) ts it Htsp HitTs. rewrite Hid in Hclk. simpl in Hclk. specialize (Hclk eq_refl). lia.
  - exact (Hcont b Hcsb).
  - exact Hid.
  - exact Hror.
  - exact Horg.
  - exact Hchain.
Qed.

End text.
