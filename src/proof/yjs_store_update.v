(** WP proofs for the [store] update path: [getNodeIndex] / [GetNode], the
    registry hit [getOrCreateYType], [store.repair], and the [applyUpdate]
    stack (the [ValidReplay] refinement [wp_store__applyUpdate], the internal
    certificate lemma, and the public [own_store]-level certificate spec
    [wp_store__applyUpdate_certs]), plus the [store_inv ⊣⊢ own_store] bridge.

    Split out of [yjs_store_base] / [yjs_store_integrate] so applyUpdate-side
    work recompiles only this file; downstream files see everything through
    the [yjs_store] facade. Same [Section] boilerplate; [Type*] footprints. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id yjs_item yjs_ytype.
From New.proof Require Import yjs_history.
From New.proof Require Import yjs_store_base yjs_store_integrate.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤].
   The verified WP proofs write [Z] comparisons (e.g. [sint.Z i < …]) unannotated
   and annotate [nat] ones with [%nat], so restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section store_update.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocM := (gmap TId (list (YjsItem A))).

(* the grow-only item-set RA (the certificate proofs grow the [sn_seq]
   authority and mint [is_type_lb] fragments) *)
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

(* [client_run]'s merge_sort instances are [#[local]] in [yjs_store_base];
   the run-list lemmas here need them again. *)
#[local] Instance cell_le_dec : RelDecision cell_le.
Proof. rewrite /cell_le. solve_decision. Defined.
#[local] Instance cell_le_trans : Transitive cell_le.
Proof. rewrite /cell_le. move=> x y z. lia. Qed.
#[local] Instance cell_le_total : Total cell_le.
Proof. rewrite /cell_le. move=> x y. lia. Qed.

(* [is_pool_rooted]'s instances are declared in [yjs_store_base] under its
   wider section context ([Proof using Type*] closes them over instances this
   file's section lacks), so re-declare them here (the [cell_le] pattern
   above); without them [iNamed] stalls at the persistent [#Hpendroot]
   conjunct of [store_inv_excl] / [own_store]. *)
#[local] Instance pool_item_rooted_persistent' γs ti :
  Persistent (pool_item_rooted γs ti).
Proof. rewrite /pool_item_rooted. destruct (decide _); apply _. Qed.
#[local] Instance is_pool_rooted_persistent' γs pool :
  Persistent (is_pool_rooted γs pool).
Proof. apply _. Qed.
#[local] Instance pool_item_rooted_timeless' γs ti :
  Timeless (pool_item_rooted γs ti).
Proof. rewrite /pool_item_rooted. destruct (decide _); apply _. Qed.
#[local] Instance is_pool_rooted_timeless' γs pool :
  Timeless (is_pool_rooted γs pool).
Proof. apply _. Qed.

(* ===== apply_update: store.applyUpdate (insert-only, decoded, causal-order ==
   subset). The integrate loop of y-octo's Doc::apply_update, refining a valid
   causal replay of the pure model. See issue #40 for the order-independent /
   ghost-global-history end state (which will also add the public entry). *)

(** A decoded parent name is either absent (Parent::None: borrow from a
    neighbour in [store.repair]) or a read-only string cell (Parent::String).
    Mirrors [is_origin_id]. *)
Lemma list_elem_of_concat {D : Type} (x : D) (ls : list (list D)) :
  x ∈ concat ls <-> ∃ l, x ∈ l ∧ l ∈ ls.
Proof.
  induction ls as [| l0 ls IH]; simpl.
  - rewrite elem_of_nil. split; [done | move=> [l [_ Hl]]; by rewrite elem_of_nil in Hl].
  - rewrite elem_of_app IH. split.
    + move=> [Hx | [l [Hx Hl]]].
      * exists l0. split; [exact Hx | apply elem_of_cons; by left].
      * exists l. split; [exact Hx | apply elem_of_cons; by right].
    + move=> [l [Hx Hl]]. apply elem_of_cons in Hl as [-> | Hl]; [by left | right; by exists l].
Qed.

(** Pool membership, decomposed to the owning type. *)
Lemma all_cells_elem_of (types : gmap loc type_state) (c : item_cell) :
  c ∈ all_cells types <-> ∃ p ts, types !! p = Some ts /\ c ∈ ty_cells ts.
Proof.
  rewrite /all_cells list_elem_of_concat.
  split.
  - move=> [l [Hcl Hl]].
    apply list_elem_of_fmap in Hl. destruct Hl as (ts & -> & Hts).
    apply list_elem_of_fmap in Hts. destruct Hts as ([p ts'] & -> & Hpts).
    simpl in *. exists p, ts'. split; [| exact Hcl].
    by apply elem_of_map_to_list.
  - move=> [p [ts [Hp Hcts]]].
    exists (ty_cells ts). split; [exact Hcts |].
    apply list_elem_of_fmap. exists ts. split; [done |].
    apply list_elem_of_fmap. exists (p, ts). split; [done |].
    by apply elem_of_map_to_list.
Qed.

(** A client run holds exactly the pool's cells with that client tag. *)
Lemma client_run_mem (types : gmap loc type_state) (kc : w64) (c : item_cell) :
  c ∈ client_run types kc <-> (c ∈ all_cells types /\ cell_client c = kc).
Proof.
  rewrite /client_run (merge_sort_Permutation cell_le _) list_elem_of_filter. tauto.
Qed.

(** The run is clock-sorted (definitional: [merge_sort]). *)
Lemma client_run_sorted (types : gmap loc type_state) (kc : w64) :
  StronglySorted cell_le (client_run types kc).
Proof. apply StronglySorted_merge_sort; apply _. Qed.

(** Sortedness, index form. *)
Lemma StronglySorted_lookup_le {D : Type} (R : D -> D -> Prop) (l : list D)
    (i j : nat) (x y : D) :
  StronglySorted R l -> l !! i = Some x -> l !! j = Some y -> (i < j)%nat -> R x y.
Proof.
  move=> Hss Hi Hj Hij.
  have Hss' : StronglySorted R (take (S i) l ++ drop (S i) l) by rewrite take_drop.
  apply (StronglySorted_app_1_elem_of _ (take (S i) l) (drop (S i) l) x y Hss').
  - apply (list_elem_of_lookup_2 _ i). rewrite lookup_take_lt; [exact Hi | lia].
  - apply (list_elem_of_lookup_2 _ (j - S i)%nat). rewrite lookup_drop.
    have -> : (S i + (j - S i))%nat = j by lia. exact Hj.
Qed.

(** Borrow one pool cell's heap struct out of the per-type DLL big-sep: its
    struct points-to plus the [own_dll]-pinned translation facts, and a wand
    restoring the big-sep. What [GetNode]'s binary search and [repair]'s
    parent borrow read through. *)
Lemma types_cell_acc (types : gmap loc type_state) (c : item_cell) :
  c ∈ all_cells types ->
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
      ⌜Forall cell_unit (ty_cells ts)⌝) -∗
    ∃ (iv : yjs.item.t),
      "%Hid" ∷ ⌜item_id (run_head c) = toYjsId iv.(yjs.item.id')⌝ ∗
      "%Hrun" ∷ ⌜length (iv.(yjs.item.content').(yjs.content.content')) = 1%nat⌝ ∗
      "%Hpar" ∷ ⌜iv.(yjs.item.parent') = ic_parent c⌝ ∗
      "Hval" ∷ ic_loc c ↦ iv ∗
      "Hback" ∷ (ic_loc c ↦ iv -∗
        ([∗ map] parent ↦ ts ∈ types,
            own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
            ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
            ⌜Forall cell_unit (ty_cells ts)⌝)).
Proof.
  move=> Hc. iIntros "Htypes".
  apply all_cells_elem_of in Hc. destruct Hc as (p & ts & Hp & Hcts).
  apply list_elem_of_lookup_1 in Hcts. destruct Hcts as [k Hk].
  iDestruct (big_sepM_lookup_acc _ _ p ts Hp with "Htypes") as "[(Hyt & %Hinvp & %Hunitp) Hrest]".
  iDestruct "Hyt" as (yt tl) "(Hparent & Hdll & %Hlen & %Hrepr & %Hcpar)".
  iDestruct (own_dll_acc (DfracOwn 1) (ty_cells ts) yt.(yjs.yType.start') tl k c Hk with "Hdll") as "Hacc".
  iNamed "Hacc".
  (* the 1-char length is no longer a DLL pin (issue #28); derive it from the
     all-singleton invariant through the content coupling *)
  have Hlen1 : length (iv.(yjs.item.content').(yjs.content.content')) = 1%nat.
  { have Hu : cell_unit c := Forall_lookup_1 _ _ _ _ Hunitp Hk.
    rewrite /cell_unit in Hu.
    have Hleq := f_equal length Hcontent.
    rewrite length_fmap explode_length /toContent in Hleq. lia. }
  iExists iv.
  iFrame "Hcval".
  iSplitR; [iPureIntro; exact Hid |].
  iSplitR; [iPureIntro; exact Hlen1 |].
  iSplitR; [iPureIntro; exact Hpar |].
  iIntros "Hval".
  iDestruct ("Hback" with "Hval") as "Hdll".
  iApply "Hrest". iSplitL; [| iPureIntro; split; [exact Hinvp | exact Hunitp]].
  iExists yt, tl. iFrame "Hparent Hdll". iPureIntro.
  split_and!; [exact Hlen | exact Hrepr | exact Hcpar].
Qed.

(** The general, run-aware sibling of [types_cell_acc]: borrows one pool cell's
    heap struct out of the 2-conjunct per-type DLL big-sep (no [cell_unit]) and
    exposes the full [own_dll_acc] translation facts (id / parent / content
    coupling / origins / flags / [run_wf]) rather than the [cell_unit]-derived
    1-char length. What [getNodeIndex] (over runs) and [splitNode] read. *)
Lemma types_cell_acc_gen (types : gmap loc type_state) (c : item_cell) :
  c ∈ all_cells types ->
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
    ∃ (iv : yjs.item.t) (olid orid : option yjs.id.t),
      "%Hid" ∷ ⌜item_id (run_head c) = toYjsId iv.(yjs.item.id')⌝ ∗
      "%Hpar" ∷ ⌜iv.(yjs.item.parent') = ic_parent c⌝ ∗
      "%Hcontent" ∷ ⌜content <$> ic_run c = explode (toContent iv.(yjs.item.content'))⌝ ∗
      "%Holid" ∷ ⌜origin_id (origin (run_head c)) = toYjsId <$> olid⌝ ∗
      "%Horid" ∷ ⌜origin_id (rightOrigin (run_head c)) = toYjsId <$> orid⌝ ∗
      "%Hflags" ∷ ⌜iv.(yjs.item.flags') = (if ic_deleted c then W8 6 else W8 2)⌝ ∗
      "%Hrun" ∷ ⌜run_wf (ic_run c)⌝ ∗
      "Hval" ∷ ic_loc c ↦ iv ∗
      "Hcol" ∷ is_origin_id iv.(yjs.item.originLeftId') olid ∗
      "Hcor" ∷ is_origin_id iv.(yjs.item.originRightId') orid ∗
      "Hback" ∷ (ic_loc c ↦ iv -∗
        ([∗ map] parent ↦ ts ∈ types,
            own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
            ⌜YjsArrInvariant (ty_arr ts)⌝)).
Proof using Type*.
  move=> Hc. iIntros "Htypes".
  apply all_cells_elem_of in Hc. destruct Hc as (p & ts & Hp & Hcts).
  apply list_elem_of_lookup_1 in Hcts. destruct Hcts as [k Hk].
  iDestruct (big_sepM_lookup_acc _ _ p ts Hp with "Htypes") as "[(Hyt & %Hinvp) Hrest]".
  iDestruct "Hyt" as (yt tl) "(Hparent & Hdll & %Hlen & %Hrepr & %Hcpar)".
  iDestruct (own_dll_acc (DfracOwn 1) (ty_cells ts) yt.(yjs.yType.start') tl k c Hk with "Hdll") as "Hacc".
  iNamed "Hacc".
  iExists iv, olid, orid.
  iSplitR; [iPureIntro; exact Hid |].
  iSplitR; [iPureIntro; exact Hpar |].
  iSplitR; [iPureIntro; exact Hcontent |].
  iSplitR; [iPureIntro; exact Holid |].
  iSplitR; [iPureIntro; exact Horid |].
  iSplitR; [iPureIntro; exact Hflags |].
  iSplitR; [iPureIntro; exact Hrun |].
  iFrame "Hcval Hcol Hcor".
  iIntros "Hval".
  iDestruct ("Hback" with "Hval") as "Hdll".
  iApply "Hrest". iSplitL; [| iPureIntro; exact Hinvp].
  iExists yt, tl. iFrame "Hparent Hdll". iPureIntro.
  split_and!; [exact Hlen | exact Hrepr | exact Hcpar].
Qed.

(** Every pool cell's id components round-trip through [w64] heap fields
    ([own_dll_id_bounds], lifted over the big-sep) — the certificate spec's
    glue from nat-level replay facts to W64 comparisons. *)
Lemma types_cells_id_bounds (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
      ⌜Forall cell_unit (ty_cells ts)⌝) -∗
  ⌜∀ c, c ∈ all_cells types ->
     (Z.of_nat (clientId (item_id (run_head c))) < 2^64)%Z ∧
     (Z.of_nat (clock (item_id (run_head c))) < 2^64)%Z⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types,
      ⌜∀ c, c ∈ ty_cells ts ->
         (Z.of_nat (clientId (item_id (run_head c))) < 2^64)%Z ∧
         (Z.of_nat (clock (item_id (run_head c))) < 2^64)%Z⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "[Hyt _]".
    iDestruct "Hyt" as (yt tl) "(Hparent & Hdll & %Hlen & %Hrepr & %Hcpar)".
    iApply (own_dll_id_bounds with "Hdll"). }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> c Hc.
  apply all_cells_elem_of in Hc. destruct Hc as (p & ts & Hp & Hcts).
  exact (Hall p ts Hp c Hcts).
Qed.

(** The per-entry document invariant, extracted from the big-sep. *)
Lemma types_arr_inv (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
      ⌜Forall cell_unit (ty_cells ts)⌝) -∗
  ⌜∀ p ts, types !! p = Some ts -> YjsArrInvariant (ty_arr ts)⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types, ⌜YjsArrInvariant (ty_arr ts)⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "(_ & %Hinv & _)". by iPureIntro. }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> p ts Hp. exact (Hall p ts Hp).
Qed.

(** The per-entry all-singleton invariant, extracted from the big-sep
    (issue #28, M1). *)
Lemma types_unit_all (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
      ⌜Forall cell_unit (ty_cells ts)⌝) -∗
  ⌜∀ p ts, types !! p = Some ts -> Forall cell_unit (ty_cells ts)⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types, ⌜Forall cell_unit (ty_cells ts)⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "(_ & _ & %Hu)". by iPureIntro. }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> p ts Hp. exact (Hall p ts Hp).
Qed.

(** [getNodeIndex] (binary search over a clock-sorted run), specified for the
    hit path only: the verified update path always resolves (a [ValidReplay]
    input's origins exist), witnessed by [k0]/[c0], so the not-found return is
    dead code (the loop cannot exhaust a window that provably contains a hit).
    The probed cells are read through the per-type DLL big-sep ([types_cell_acc]);
    their 1-char pin makes [Len() = 1], so a run covers [clk] iff some cell's
    clock IS [clk]. [Hnowrap] rules out [middleClock + 1] wrap-around (the
    [middleEnd] compare would otherwise skip a max-clock hit). *)
Lemma wp_getNodeIndex (sl : slice.t) (dq : dfrac) (types : gmap loc type_state)
    (run : list item_cell) (clk : w64) (k0 : nat) (c0 : item_cell) :
  StronglySorted cell_le run ->
  (∀ c, c ∈ run -> c ∈ all_cells types) ->
  (∀ c, c ∈ run -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  run !! k0 = Some c0 ->
  cell_clock c0 = clk ->
  {{{ is_pkg_init yjs ∗ sl ↦*{dq} (ic_loc <$> run) ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    @! yjs.getNodeIndex #sl #clk
  {{{ (i : w64), RET (#i, #true);
      sl ↦*{dq} (ic_loc <$> run) ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ∃ c, ⌜run !! uint.nat i = Some c ∧
             (uint.Z (cell_clock c) <= uint.Z clk)%Z ∧
             (uint.Z clk < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z⌝ }}}.
Proof using Type*.
  move=> Hsort Hmem Hrunfits Hk0 Hclk0.
  wp_start as "(Hsl & Htypes)".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  rewrite length_fmap in Hsllen Hsllen0.
  wp_auto.
  (* loop invariant: the window [lo, hi) contains every hit (a cell whose head
     clock IS [clk]); the returned cell only COVERS [clk] (run-aware) *)
  iAssert (∃ (lo hi : w64),
    "Hleft" ∷ left_ptr ↦ lo ∗ "Hright" ∷ right_ptr ↦ hi ∗
    "Hnodes" ∷ nodes_ptr ↦ sl ∗ "Hclock" ∷ clock_ptr ↦ clk ∗
    "Hsl" ∷ sl ↦*{dq} (ic_loc <$> run) ∗
    "Htypes" ∷ ([∗ map] parent ↦ ts ∈ types,
        own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
        ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
    "%Hbnd" ∷ ⌜(0 <= uint.Z lo /\ uint.Z hi <= Z.of_nat (length run))%Z⌝ ∗
    "%Hwin" ∷ ⌜∀ (k : nat) (c : item_cell), run !! k = Some c -> cell_clock c = clk ->
                (uint.Z lo <= Z.of_nat k < uint.Z hi)%Z⌝)%I
    with "[left right nodes clock Hsl Htypes]" as "IH".
  { iExists (W64 0), sl.(slice.len).
    iFrame "left right nodes clock Hsl Htypes".
    iPureIntro. split; [word |].
    move=> k c Hk Hc. have Hklt := lookup_lt_Some _ _ _ Hk. word. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - (* probe the middle *)
    set (mid := word.add lo (word.divu (word.sub hi lo) (W64 2))).
    have Hmid : (uint.Z lo <= uint.Z mid < uint.Z hi)%Z.
    { rewrite /mid. destruct Hbnd as [Hb1 Hb2]. word. }
    wp_auto.
    rewrite decide_True; last word.
    have Hmidlt : (uint.nat mid < length run)%nat by word.
    destruct (run !! uint.nat mid) as [cmid|] eqn:Hcmid;
      last by (apply lookup_ge_None in Hcmid; lia).
    have Hlocmid : (ic_loc <$> run) !! uint.nat mid = Some cmid.(ic_loc)
      by rewrite list_lookup_fmap Hcmid //.
    iDestruct (own_slice_elem_acc (sint.Z mid) (ic_loc cmid) sl dq (ic_loc <$> run) with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z mid)) with (uint.nat mid) by word. exact Hlocmid. }
    wp_auto.
    iDestruct ("Hgive" $! cmid.(ic_loc) with "Hel") as "Hsl".
    have Hinsid : (<[sint.nat mid := cmid.(ic_loc)]> (ic_loc <$> run)) = (ic_loc <$> run).
    { apply list_insert_id. replace (sint.nat mid) with (uint.nat mid) by word. exact Hlocmid. }
    iEval (rewrite Hinsid) in "Hsl".
    have Hcmemall : cmid ∈ all_cells types
      by (apply Hmem; exact (list_elem_of_lookup_2 _ _ _ Hcmid)).
    iDestruct (types_cell_acc_gen types cmid Hcmemall with "Htypes") as "Hacc".
    iNamed "Hacc".
    wp_auto.
    have Hmcv : cell_clock cmid = iv.(yjs.item.id').(yjs.id.clock')
      by (rewrite /cell_clock Hid /toYjsId /=; word).
    (* the run length is what [Len()] reads (the content byte length couples to
       the run via [Hcontent]), replacing the pre-#28 unit-length reasoning *)
    have HlenEq : length (iv.(yjs.item.content').(yjs.content.content')) = length (ic_run cmid).
    { have H := f_equal length Hcontent.
      rewrite length_fmap explode_length /toContent in H. lia. }
    have Hlenpos : (1 <= Z.of_nat (length (ic_run cmid)))%Z.
    { have [Hne _] := Hrun. destruct (ic_run cmid) as [|? ?]; [done | simpl; lia]. }
    wp_apply (wp_item__Len cmid.(ic_loc) (DfracOwn 1) iv with "[$Hval]"). iIntros "Hval".
    rewrite HlenEq.
    iDestruct ("Hback" with "Hval") as "Htypes".
    wp_auto.
    destruct (bool_decide (uint.Z clk < uint.Z iv.(yjs.item.id').(yjs.id.clock'))) eqn:Hcmp1.
    + (* clk < middleClock: shrink [right] to [mid] *)
      apply bool_decide_eq_true_1 in Hcmp1.
      wp_auto. wp_for_post.
      iFrame "HΦ". iExists lo, mid.
      iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
      iPureIntro. split.
      { lia. }
      move=> k c Hk Hc.
      have [Hlo Hhi] := Hwin k c Hk Hc.
      split; [exact Hlo |].
      destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
      * lia.
      * exfalso. subst k. rewrite Hcmid in Hk. injection Hk as <-.
        rewrite -Hmcv Hc in Hcmp1. lia.
      * exfalso.
        have Hle := StronglySorted_lookup_le cell_le run (uint.nat mid) k cmid c Hsort Hcmid Hk Hgt.
        rewrite /cell_le Hc Hmcv in Hle. lia.
    + (* clk >= middleClock *)
      apply bool_decide_eq_false_1 in Hcmp1.
      have Hnw : (uint.Z (cell_clock cmid) + Z.of_nat (length (ic_run cmid)) < 2^64)%Z
        by (apply Hrunfits; exact (list_elem_of_lookup_2 _ _ _ Hcmid)).
      rewrite Hmcv in Hnw.
      wp_auto.
      case_bool_decide as Hcmp2.
      * (* clk >= middleEnd: move [left] past [mid] *)
        have Hgtm : (uint.Z iv.(yjs.item.id').(yjs.id.clock') < uint.Z clk)%Z by word.
        wp_auto. wp_for_post.
        iFrame "HΦ". iExists (word.add mid (W64 1)), hi.
        iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
        iPureIntro. split.
        { word. }
        move=> k c Hk Hc.
        have [Hlo Hhi] := Hwin k c Hk Hc.
        split; [| exact Hhi].
        destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
        { exfalso.
          have Hle := StronglySorted_lookup_le cell_le run k (uint.nat mid) c cmid Hsort Hk Hcmid Hlt.
          rewrite /cell_le Hc Hmcv in Hle. lia. }
        { exfalso. subst k. rewrite Hcmid in Hk. injection Hk as <-.
          rewrite -Hmcv Hc in Hgtm. lia. }
        word.
      * (* middleClock <= clk < middleEnd = middleClock + Len: the probe COVERS clk *)
        wp_auto. wp_for_post.
        iApply ("HΦ" $! mid). iFrame "Hsl Htypes".
        iExists cmid. iPureIntro. split; [exact Hcmid |].
        split; rewrite Hmcv; word.
  - (* [left >= right] never happens: the witness pins a nonempty window *)
    exfalso. have [Hf1 Hf2] := Hwin k0 c0 Hk0 Hclk0. lia.
Qed.

(** [store.GetNode], specified for the hit path against a caller-supplied
    witness cell [cw] (the verified update path knows its origins resolve):
    the per-client run lookup succeeds ([own_item_map]'s completeness), the
    binary search returns a cell with [cw]'s (client, clock) — and clock
    determines loc per client ([Hclkloc]), so the returned node IS [cw]'s.
    Only reads: any [own_item_map] fraction works, and everything is handed
    back. *)
Lemma wp_store__GetNode (s mref : loc) (dq : dfrac) (idv : yjs.id.t)
    (types : gmap loc type_state) (cw : item_cell) :
  cw ∈ all_cells types ->
  item_id (run_head cw) = toYjsId idv ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "GetNode" #idv
  {{{ RET (#(ic_loc cw), #true);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}.
Proof using Type*.
  move=> Hcw Hcwid Hnowrap.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  (* GetNode is read-only and holds the [cell_unit] invariant, so [getNodeIndex]'s
     2-conjunct big-sep is [Htypes] minus the [cell_unit] conjunct (saved pure and
     re-attached afterward), and the run-aware COVERING return collapses to an
     exact-clock hit via the 1-char pin. *)
  iDestruct (types_unit_all with "Htypes") as %Hunitsaved.
  set (kc := idv.(yjs.id.clientId')).
  have Hcwcc : cell_client cw = kc by (rewrite /cell_client Hcwid /toYjsId /=; word).
  iNamed "Hitemmap".
  have Hkcin : kc ∈ (cell_client <$> all_cells types).
  { rewrite -Hcwcc. apply list_elem_of_fmap_2. exact Hcw. }
  destruct (Hcomplete kc Hkcin) as [slk Hslk].
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Hmap"). iIntros "Hmap".
  rewrite Hslk /=.
  wp_auto.
  iDestruct (big_sepM_lookup_acc _ _ kc slk Hslk with "Hruns") as "[Hrun Hrunsback]".
  iNamed "Hrun".
  have Hcwrun : cw ∈ client_run types kc by (apply client_run_mem; split; [exact Hcw | exact Hcwcc]).
  apply list_elem_of_lookup_1 in Hcwrun. destruct Hcwrun as [kw Hkw].
  have Hclkw : cell_clock cw = idv.(yjs.id.clock')
    by (rewrite /cell_clock Hcwid /toYjsId /=; word).
  (* run-fits from the unit invariant: every run is 1-char, so [clock + Len = clock + 1] *)
  have Hrunfits : ∀ c, c ∈ client_run types kc ->
      (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z.
  { move=> c Hc.
    have Hcall : c ∈ all_cells types := proj1 (proj1 (client_run_mem types kc c) Hc).
    apply all_cells_elem_of in Hcall as (p & ts & Hp & Hcts).
    have Hu : cell_unit c := proj1 (Forall_forall _ _) (Hunitsaved p ts Hp) c Hcts.
    rewrite /cell_unit in Hu. rewrite Hu.
    have H1 := Hnowrap c (proj1 (proj1 (client_run_mem types kc c) Hc)). lia. }
  iAssert ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝)%I with "[Htypes]" as "Htypes2".
  { iApply (big_sepM_impl with "Htypes"). iIntros "!#" (p ts Hp) "($ & $ & _)". }
  wp_apply (wp_getNodeIndex slk dq types (client_run types kc) idv.(yjs.id.clock') kw cw
              (client_run_sorted types kc)
              (fun c Hc => proj1 (proj1 (client_run_mem types kc c) Hc))
              Hrunfits
              Hkw Hclkw
              with "[$Hslice $Htypes2]").
  iIntros (i) "(Hslice & Htypes2 & %Hires)".
  destruct Hires as (cres & Hcres & Hcresle & Hcreslt).
  wp_auto.
  iDestruct (own_slice_len with "Hslice") as %[Hsllen Hsllen0].
  rewrite length_fmap in Hsllen Hsllen0.
  have Hilt : (uint.nat i < length (client_run types kc))%nat by (apply lookup_lt_Some in Hcres; lia).
  rewrite decide_True; last word.
  have Hlocres : (ic_loc <$> client_run types kc) !! uint.nat i = Some cres.(ic_loc)
    by rewrite list_lookup_fmap Hcres //.
  iDestruct (own_slice_elem_acc (sint.Z i) (ic_loc cres) slk dq (ic_loc <$> client_run types kc) with "Hslice") as "[Hel Hgive]".
  { word. }
  { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hlocres. }
  wp_auto.
  iDestruct ("Hgive" $! cres.(ic_loc) with "Hel") as "Hslice".
  have Hinsid : (<[sint.nat i := cres.(ic_loc)]> (ic_loc <$> client_run types kc)) = (ic_loc <$> client_run types kc).
  { apply list_insert_id. replace (sint.nat i) with (uint.nat i) by word. exact Hlocres. }
  iEval (rewrite Hinsid) in "Hslice".
  (* clock determines loc per client: the found cell IS the witness's node *)
  have Hcresmem : cres ∈ all_cells types /\ cell_client cres = kc.
  { apply client_run_mem. exact (list_elem_of_lookup_2 _ _ _ Hcres). }
  (* the covering cell is 1-char (unit invariant), so it starts exactly at [clk] *)
  have Hcresunit : length (ic_run cres) = 1%nat.
  { have Hcm := proj1 Hcresmem. apply all_cells_elem_of in Hcm as (p & ts & Hp & Hcts).
    exact (proj1 (Forall_forall _ _) (Hunitsaved p ts Hp) cres Hcts). }
  have Hcrespr : (uint.Z (cell_clock cres) = uint.Z idv.(yjs.id.clock'))%Z.
  { rewrite Hcresunit /= in Hcreslt. lia. }
  have Hloceq : cres.(ic_loc) = cw.(ic_loc).
  { apply (Hclkloc cres cw (proj1 Hcresmem) Hcw).
    - rewrite (proj2 Hcresmem) Hcwcc //.
    - rewrite /cell_pr /= Hcrespr Hclkw //. }
  rewrite Hloceq.
  iApply "HΦ".
  iFrame "Hitemsf".
  iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
  iSplitL "Hmap Hruns".
  { iExists gm. iFrame "Hmap Hruns". iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
  (* re-attach the [cell_unit] conjunct to restore the 3-conjunct GetNode post *)
  iApply (big_sepM_impl with "Htypes2"). iIntros "!#" (p ts Hp) "($ & $)".
  iPureIntro. exact (Hunitsaved p ts Hp).
Qed.

(** [store.splitNode n diff] (issue #28 M4): split the run cell [cw] (at DLL
    index [k] of type [parent]) at offset [diff] into a truncated left half (same
    node loc) and a fresh right half ([rloc]), updating both the per-type DLL and
    the per-client run list. The pure cell effect is [split_cells cells k
    (uint.nat diff) rloc], invisible to the flattened document.

    Standalone M4 infrastructure (not yet wired into repair / the update path).

    NOTE (spec deviations from the issue-28 M2 plan sketch, reported):
    - The no-wrap hypothesis is strengthened from [cell_clock c + 1 < 2^64] to
      the run-aware [cell_clock c + length (ic_run c) < 2^64] for every cell,
      because [getNodeIndex] (now run-aware) computes [middleClock + Len()] with
      [Len()] the RUN length, so the +1 bound no longer rules out overflow at a
      multi-char probe. It subsumes the separate [+ length (ic_run cw)] bound.
    - The non-overlap hypothesis is corrected to genuine range-disjointness
      ([c.clock + length (ic_run c) <= cw.clock ∨ cw.clock + length (ic_run cw)
      <= c.clock] for [ic_loc c ≠ ic_loc cw]). The sketch's [c.clock <= cw.clock]
      left half does NOT prevent a left cell from overlapping [cw]'s clock range,
      so the covering cell [getNodeIndex] returns would not be uniquely pinned to
      [cw]'s position. Disjointness is the true store invariant. *)

Lemma wp_store__splitNode (s mref : loc) (types : gmap loc type_state)
    (parent : loc) (cells arr : list _) (k : nat) (cw : item_cell) (diff : w64) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  (0 < uint.nat diff < length (ic_run cw))%nat ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  (∀ c, c ∈ all_cells types -> cell_client c = cell_client cw -> ic_loc c ≠ ic_loc cw ->
     (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z (cell_clock cw))%Z ∨
     (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) <= uint.Z (cell_clock c))%Z) ->
  (* the client run has room for one more node: [make(len+1)] must not sign-wrap
     (the run list is a [signed] slice length; analogous to the clock no-wraps) *)
  (Z.of_nat (length (client_run types (cell_client cw))) + 1 < 2^63)%Z ->
  {{{ is_pkg_init yjs ∗ (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      ([∗ map] p ↦ ts ∈ types, own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗ ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "splitNode" #(ic_loc cw) #diff
  {{{ (rloc : loc), RET (#(ic_loc cw), #rloc);
      ⌜rloc ≠ null⌝ ∗ (s .[(yjs.store.t), "items"]) ↦ mref ∗
      own_item_map mref (DfracOwn 1) (<[parent := MkTypeState (split_cells cells k (uint.nat diff) rloc) arr]> types) ∗
      ([∗ map] p ↦ ts ∈ (<[parent := MkTypeState (split_cells cells k (uint.nat diff) rloc) arr]> types),
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗ ⌜YjsArrInvariant (ty_arr ts)⌝) }}}.
Proof using Type*.
  move=> Htypes Hcellk Hdiff Hrunfits Hnodup Hdisj Hrunlen.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  (* open [parent]'s [own_ytype_cells], peel node [k] out of the DLL *)
  iDestruct (big_sepM_insert_acc _ _ parent _ Htypes with "Htypes") as "[(Hpc & %Harrinv) Hclose]".
  simpl.
  iDestruct "Hpc" as (yt tl0) "(Hparent & Hdll & %Hlen0 & %Hrepr0 & %Hcpar0)".
  pose proof (take_drop_middle cells k cw Hcellk) as Hsplit.
  set (pre := take k cells) in Hsplit.
  set (suf := drop (S k) cells) in Hsplit.
  iEval (rewrite -Hsplit) in "Hdll".
  iEval (rewrite own_dll_app) in "Hdll".
  iDestruct "Hdll" as (ml mf) "[Hseg1 Hseg2]".
  iDestruct "Hseg2" as (iv olidcw oridcw) "Hcons".
  iNamed "Hcons".
  destruct Hloc as [Hmfeq Hmfnn]. subst mf.
  iDestruct (typed_pointsto_not_null with "Hval") as %Hcwnn.
  wp_method_call. wp_call. wp_call. wp_auto.
  (* olid := newId(client, clock+diff-1) *)
  wp_apply wp_NewId.
  (* cb := []byte(n.content.content) via the byte round-trip *)
  wp_apply wp_string_to_bytes. iIntros (cbs) "[Hcb Hcbcap]". wp_auto.
  (* the right cell's id := newId(client, clock+diff) *)
  wp_apply wp_NewId.
  have Hsclen : length (iv.(yjs.item.content').(yjs.content.content')) = length cw.(ic_run).
  { have H := f_equal length Hcontent. rewrite length_fmap explode_length /toContent in H. lia. }
  iDestruct (own_slice_len with "Hcb") as %Hcbwf.
  iDestruct (own_slice_wf with "Hcb") as %Hcapwf.
  destruct Hcbwf as [Hcbwf1 Hcbwf2].
  have Hdiffb : 0 ≤ sint.Z diff ≤ sint.Z cbs.(slice.len) by word.
  (* right.content := string(cb[diff:]) *)
  rewrite decide_True; last (split; [word | word]).
  have Hslbound : 0 ≤ sint.Z diff ≤ sint.Z cbs.(slice.len) ≤ sint.Z cbs.(slice.len) by word.
  iDestruct (own_slice_slice diff cbs.(slice.len) cbs (DfracOwn 1) _ Hslbound with "Hcb") as "(Hcb_lo & Hcb_mid & Hcb_hi)".
  wp_apply (wp_bytes_to_string with "Hcb_mid"). iIntros "Hcb_mid".
  wp_auto.
  wp_alloc rs as "Hrs". wp_auto.
  (* n.content := string(cb[:diff]) *)
  rewrite decide_True; last word.
  wp_apply (wp_bytes_to_string with "Hcb_lo"). iIntros "Hcb_lo".
  wp_auto.
  (* ===== branch-agnostic pure run-telescoping facts (the split's model core) *)
  iDestruct (typed_pointsto_not_null with "Hrs") as %Hrsnn.
  set (o := uint.nat diff).
  have Hcwmem : cw ∈ all_cells types.
  { apply all_cells_elem_of. exists parent, (MkTypeState cells arr).
    split; [exact Htypes | exact (list_elem_of_lookup_2 _ _ _ Hcellk)]. }
  have Hnowrapcw := Hrunfits cw Hcwmem.
  have Hcwck : cell_clock cw = iv.(yjs.item.id').(yjs.id.clock').
  { rewrite /cell_clock Hid /toYjsId /=. word. }
  have Hsintlen : sint.nat cbs.(slice.len) = length cw.(ic_run).
  { rewrite -Hsclen. symmetry. exact Hcbwf1. }
  have Hsintdiff : sint.nat diff = o.
  { rewrite /o. word. }
  have Hoinrun : (o < length cw.(ic_run))%nat by (rewrite /o; lia).
  have Hrun0 : cw.(ic_run) !! 0%nat = Some (run_head cw).
  { rewrite /run_head. destruct Hrun as [Hne _]. destruct (ic_run cw) as [|a r']; [done | reflexivity]. }
  destruct (cw.(ic_run) !! o) as [yo|] eqn:Hyo; [| apply lookup_ge_None in Hyo; lia].
  have Hyoid := run_wf_lookup_clock cw.(ic_run) o (run_head cw) yo Hrun Hrun0 Hyo.
  have Hyoro := run_wf_lookup_rightOrigin cw.(ic_run) o (run_head cw) yo Hrun Hrun0 Hyo.
  iDestruct (typed_pointsto_not_null with "olid") as %Holidnn.
  iPersist "olid".
  have Hrhcl : run_head (split_cell_left cw o) = run_head cw.
  { rewrite /run_head /split_cell_left /=. apply hd_inhabitant_take. rewrite /o; lia. }
  have Hrhcr : run_head (split_cell_right cw o rs) = yo.
  { rewrite /run_head /split_cell_right /=. exact (hd_inhabitant_drop _ o yo Hyo). }
  have Hcontl : content <$> take o cw.(ic_run) = explode (take (sint.nat diff) iv.(yjs.item.content').(yjs.content.content')).
  { rewrite Hsintdiff fmap_take Hcontent /toContent /explode fmap_take //. }
  have Hsubdrop : subslice (sint.nat diff) (sint.nat cbs.(slice.len)) iv.(yjs.item.content').(yjs.content.content')
                = drop o iv.(yjs.item.content').(yjs.content.content').
  { rewrite Hsintdiff Hsintlen -Hsclen /subslice. rewrite take_ge; [reflexivity | lia]. }
  have Hcontr : content <$> drop o cw.(ic_run) = explode (drop o iv.(yjs.item.content').(yjs.content.content')).
  { rewrite fmap_drop Hcontent /toContent /explode fmap_drop //. }
  (* [if n.right != nil] branches on whether [cw] is the run's last cell (suf) *)
  destruct suf as [|d0 drest] eqn:Hsufeq.
  - (* cw is last: no downstream relink. Remaining: own_dll_split (cs2=[]),
       own_ytype_cells rebuild over split_cells, and the item-map surgery
       (getNodeIndex over the split run + client_run_loc_insert). *)
    (* ----- guard + n.right := rs ----- *)
    iDestruct "Hrest" as %[Hrnull Htl0eq].
    rewrite (bool_decide_eq_true_2 (iv.(yjs.item.right') = null) Hrnull).
    wp_auto.
    (* ----- branch-agnostic split-cell pure facts (origin telescoping) ----- *)
    set (cl := split_cell_left cw o).
    set (cr := split_cell_right cw o rs).
    set (oid := {| yjs.id.clientId' := iv.(yjs.item.id').(yjs.id.clientId');
                   yjs.id.clock' := word.sub (word.add iv.(yjs.item.id').(yjs.id.clock') diff) (W64 1) |}).
    have Hopos : (0 < o)%nat by (rewrite /o; lia).
    have Hnowrap_add : (uint.Z iv.(yjs.item.id').(yjs.id.clock') + uint.Z diff < 2^64)%Z.
    { rewrite -Hcwck. have H1 := Hnowrapcw. have H2 := Hdiff. word. }
    have Hadd_eq : (uint.nat iv.(yjs.item.id').(yjs.id.clock') + o)%nat = uint.nat (word.add iv.(yjs.item.id').(yjs.id.clock') diff).
    { rewrite /o. clear -Hnowrap_add. word. }
    have [xprev Hxprev] : is_Some (cw.(ic_run) !! (o - 1)%nat).
    { apply lookup_lt_is_Some. rewrite /o. lia. }
    have Hyo2 : cw.(ic_run) !! S (o - 1)%nat = Some yo.
    { replace (S (o - 1))%nat with o by (rewrite /o; lia). exact Hyo. }
    have Hstep := proj2 Hrun (o - 1)%nat xprev yo Hxprev Hyo2.
    have Horig : origin yo = itemPtr xprev by (destruct Hstep as [_ [Hh _]]; exact Hh).
    have Hxpid := run_wf_lookup_clock cw.(ic_run) (o - 1)%nat (run_head cw) xprev Hrun Hrun0 Hxprev.
    have Hcrorig : origin_id (origin (run_head cr)) = toYjsId <$> Some oid.
    { rewrite /cr Hrhcr Horig /origin_id /=. f_equal.
      rewrite Hxpid Hid /toYjsId /oid /=. f_equal. clear -Hnowrap_add Hdiff. word. }
    have Hrhck : clock (item_id (run_head cw)) = uint.nat iv.(yjs.item.id').(yjs.id.clock') by (rewrite Hid /toYjsId /=).
    have Hclcl : cell_clock cl = cell_clock cw by (rewrite /cl /cell_clock Hrhcl).
    have Hcccl : cell_client cl = cell_client cw by (rewrite /cl /cell_client Hrhcl).
    have Hcccr : cell_client cr = cell_client cw by (rewrite /cr /cell_client Hrhcr Hyoid /=).
    have Hccr_clock : uint.Z (cell_clock cr) = (uint.Z (cell_clock cw) + Z.of_nat o)%Z.
    { rewrite /cr /cell_clock Hrhcr Hyoid /= Hrhck. clear -Hnowrap_add Hdiff. rewrite /o. word. }
    have Hsc : split_cells cells k o rs = pre ++ cl :: cr :: [].
    { rewrite /split_cells Hcellk. rewrite -/suf Hsufeq. rewrite app_nil_r. reflexivity. }
    (* the split-cell struct values [ivl] (truncated cw) / [ivr] (right half) *)
    set (ivl := iv <| yjs.item.content' := {| yjs.content.content' := take (sint.nat diff) iv.(yjs.item.content').(yjs.content.content') |} |> <| yjs.item.right' := rs |>).
    set (ivr := {| yjs.item.id' := {| yjs.id.clientId' := iv.(yjs.item.id').(yjs.id.clientId'); yjs.id.clock' := word.add iv.(yjs.item.id').(yjs.id.clock') diff |};
                   yjs.item.originLeftId' := olid_ptr;
                   yjs.item.originRightId' := iv.(yjs.item.originRightId');
                   yjs.item.left' := cw.(ic_loc);
                   yjs.item.right' := iv.(yjs.item.right');
                   yjs.item.parent' := iv.(yjs.item.parent');
                   yjs.item.content' := {| yjs.content.content' := subslice (sint.nat diff) (sint.nat cbs.(slice.len)) iv.(yjs.item.content').(yjs.content.content') |};
                   yjs.item.flags' := iv.(yjs.item.flags') |}).
    have Hivl_ol : ivl.(yjs.item.originLeftId') = iv.(yjs.item.originLeftId') by (rewrite /ivl /=).
    have Hivl_or : ivl.(yjs.item.originRightId') = iv.(yjs.item.originRightId') by (rewrite /ivl /=).
    have Hivl_left : ivl.(yjs.item.left') = ml by (rewrite /ivl /=; exact Hprev).
    have Hivr_r : ivr.(yjs.item.right') = null by (rewrite /ivr /=; exact Hrnull).
    have Hrhcl' : run_head cl = run_head cw by (rewrite /cl; exact Hrhcl).
    have Hrhcr' : run_head cr = yo by (rewrite /cr; exact Hrhcr).
    have Hrhcli : clientId (item_id (run_head cw)) = uint.nat iv.(yjs.item.id').(yjs.id.clientId') by (rewrite Hid /toYjsId /=).
    have Hclloc : ic_loc cl = cw.(ic_loc) by (rewrite /cl /=).
    have Hcrloc : ic_loc cr = rs by (rewrite /cr /=).
    have Hivr_ol : ivr.(yjs.item.originLeftId') = olid_ptr by (rewrite /ivr /=).
    have Hivr_or : ivr.(yjs.item.originRightId') = iv.(yjs.item.originRightId') by (rewrite /ivr /=).
    have Hp1 : ic_loc cl ≠ null by (rewrite /cl /=; exact Hmfnn).
    have Hp2 : ic_loc cr ≠ null by (rewrite /cr /=; exact Hrsnn).
    have Hp4 : ivl.(yjs.item.right') = ic_loc cr by (rewrite /ivl /cr /=).
    have Hp5 : ivl.(yjs.item.parent') = ic_parent cl by (rewrite /ivl /cl /=; exact Hpar).
    have Hp6 : item_id (run_head cl) = toYjsId ivl.(yjs.item.id'). { rewrite Hrhcl' /ivl /=. exact Hid. }
    have Hp7 : content <$> ic_run cl = explode (toContent ivl.(yjs.item.content')). { rewrite /cl /ivl /toContent /=. exact Hcontl. }
    have Hp8 : origin_id (origin (run_head cl)) = toYjsId <$> olidcw. { rewrite Hrhcl'. exact Holid. }
    have Hp9 : origin_id (rightOrigin (run_head cl)) = toYjsId <$> oridcw. { rewrite Hrhcl'. exact Horid. }
    have Hp10 : ivl.(yjs.item.flags') = (if ic_deleted cl then W8 6 else W8 2). { rewrite /ivl /cl /=. exact Hflags. }
    have Hp11 : run_wf (ic_run cl). { rewrite /cl /=. exact (run_wf_take cw.(ic_run) o Hopos Hrun). }
    have Hp12 : ivr.(yjs.item.left') = ic_loc cl. { rewrite /ivr /cl /=. reflexivity. }
    have Hp13 : ivr.(yjs.item.parent') = ic_parent cr. { rewrite /ivr /cr /=. exact Hpar. }
    have Hp14 : item_id (run_head cr) = toYjsId ivr.(yjs.item.id'). { rewrite Hrhcr' Hyoid /ivr /toYjsId /=. rewrite Hrhck Hrhcli Hadd_eq. reflexivity. }
    have Hp15 : content <$> ic_run cr = explode (toContent ivr.(yjs.item.content')). { rewrite /cr /ivr /toContent /= Hsubdrop. exact Hcontr. }
    have Hp17 : origin_id (rightOrigin (run_head cr)) = toYjsId <$> oridcw. { rewrite Hrhcr' Hyoro. exact Horid. }
    have Hp18 : ivr.(yjs.item.flags') = (if ic_deleted cr then W8 6 else W8 2). { rewrite /ivr /cr /=. exact Hflags. }
    have Hp19 : run_wf (ic_run cr). { rewrite /cr /=. exact (run_wf_drop cw.(ic_run) o Hoinrun Hrun). }
    (* ----- read the client run slice (map.lookup1), BEFORE Phase A locks cw ----- *)
    iNamed "Hitemmap".
    set (kc := iv.(yjs.item.id').(yjs.id.clientId')).
    have Hcwcc : cell_client cw = kc by (rewrite /cell_client Hrhcli /kc; word).
    have Hkcin : kc ∈ (cell_client <$> all_cells types).
    { rewrite -Hcwcc. apply list_elem_of_fmap_2. exact Hcwmem. }
    have Hcwrun : cw ∈ client_run types kc.
    { apply client_run_mem. split; [exact Hcwmem | exact Hcwcc]. }
    apply list_elem_of_lookup_1 in Hcwrun. destruct Hcwrun as [kw Hkw].
    destruct (Hcomplete kc Hkcin) as [slk Hslk].
    iDestruct (big_sepM_lookup_acc _ _ kc slk Hslk with "Hruns") as "[Hrunslk Hrunsback]".
    iNamed "Hrunslk".
    wp_apply (wp_map_lookup1 with "Hmap"). iIntros "Hmap".
    rewrite Hslk /=.
    wp_auto.
    (* ----- Phase A: own_dll_split, own_ytype_cells rebuild, close over types2 ----- *)
    iAssert (own_dll (DfracOwn 1) yt.(yjs.yType.start') rs null null (split_cells cells k o rs))
      with "[Hseg1 Hval Holeft Horight Hrs]" as "Hdll2".
    { rewrite Hsc.
      iApply (own_dll_split (DfracOwn 1) pre (@nil item_cell) cl cr ivl ivr olidcw oridcw (Some oid) oridcw yt.(yjs.yType.start') rs ml Hp1 Hp2 Hivl_left Hp4 Hp5 Hp6 Hp7 Hp8 Hp9 Hp10 Hp11 Hp12 Hp13 Hp14 Hp15 Hcrorig Hp17 Hp18 Hp19).
      rewrite Hclloc Hcrloc Hivl_ol Hivl_or Hivr_ol Hivr_or Hivr_r.
      iDestruct "Horight" as "#HorightP".
      iFrame "Hseg1 Hval Hrs Holeft HorightP".
      iSplit.
      - simpl. iFrame "olid". iPureIntro. exact Holidnn.
      - simpl. iPureIntro. done. }
    have Hcparcw : ic_parent cw = parent by (apply Hcpar0; apply (list_elem_of_lookup_2 _ _ _ Hcellk)).
    have Hcpar_split : ∀ c, c ∈ split_cells cells k o rs -> ic_parent c = parent.
    { rewrite Hsc. move=> c Hc. apply elem_of_app in Hc as [Hc | Hc].
      - apply Hcpar0. rewrite -Hsplit. apply elem_of_app; by left.
      - apply elem_of_cons in Hc as [-> | Hc]; [rewrite /cl /=; exact Hcparcw |].
        apply elem_of_cons in Hc as [-> | Hc]; [rewrite /cr /=; exact Hcparcw | by apply elem_of_nil in Hc]. }
    iAssert (own_ytype_cells parent (DfracOwn 1) (split_cells cells k o rs) arr) with "[Hparent Hdll2]" as "Hyt2".
    { iExists yt, rs. iFrame "Hparent Hdll2". iPureIntro. split_and!.
      - rewrite (split_cells_num_visible cells k o rs cw Hcellk). exact Hlen0.
      - rewrite /cells_repr (split_cells_flatten cells k o rs cw Hcellk). exact Hrepr0.
      - exact Hcpar_split. }
    iDestruct ("Hclose" $! {| ty_cells := split_cells cells k o rs; ty_arr := arr |} with "[Hyt2]") as "Htypes2".
    { iFrame "Hyt2". iPureIntro. exact Harrinv. }
    (* ----- getNodeIndex over the split run [run_half] = client_run with cw -> cl ----- *)
    have Hss_replace : ∀ (ll : list item_cell) (i : nat) (a b : item_cell),
        StronglySorted cell_le ll → ll !! i = Some a → cell_clock b = cell_clock a →
        StronglySorted cell_le (<[i:=b]> ll).
    { elim => [| c ll IH] i a b Hss Hi Hclk.
      - by rewrite /=.
      - apply StronglySorted_inv in Hss as [Hssll Hfa].
        destruct i as [|i']; simpl.
        + simpl in Hi. injection Hi as Hca. rewrite Hca in Hfa.
          apply SSorted_cons; [exact Hssll |].
          apply Forall_forall => x Hx. rewrite /cell_le Hclk.
          exact (proj1 (Forall_forall _ _) Hfa x Hx).
        + apply SSorted_cons; [exact (IH i' a b Hssll Hi Hclk) |].
          apply Forall_insert; [exact Hfa |].
          rewrite /cell_le Hclk.
          exact (proj1 (Forall_forall _ _) Hfa a (list_elem_of_lookup_2 ll i' a Hi)). }
    have Hss_half : StronglySorted cell_le (<[kw := cl]> (client_run types kc)) := Hss_replace (client_run types kc) kw cw cl (client_run_sorted types kc) Hkw Hclcl.
    set (run_half := <[kw := cl]> (client_run types kc)).
    have HndAll : NoDup (all_cells types) := NoDup_fmap_1 ic_loc _ Hnodup.
    have Hndrun : NoDup (client_run types kc).
    { rewrite /client_run (merge_sort_Permutation cell_le _). apply NoDup_filter. exact HndAll. }
    have Hkwlt : (kw < length (client_run types kc))%nat by (apply lookup_lt_Some in Hkw; exact Hkw).
    have Hlockw : (ic_loc <$> client_run types kc) !! kw = Some (ic_loc cl).
    { rewrite list_lookup_fmap Hkw /=. done. }
    have Hlocs : ic_loc <$> run_half = ic_loc <$> client_run types kc.
    { rewrite /run_half list_fmap_insert (list_insert_id _ _ _ Hlockw) //. }
    have Hkw_half : run_half !! kw = Some cl.
    { rewrite /run_half. apply list_lookup_insert_Some. left. split_and!; [reflexivity | reflexivity | exact Hkwlt]. }
    have Hclk_half : cell_clock cl = iv.(yjs.item.id').(yjs.id.clock') by (rewrite Hclcl Hcwck).
    have Hsub : ∀ c, c ∈ run_half → c = cl ∨ c ∈ client_run types kc.
    { move=> c Hc. apply list_elem_of_lookup_1 in Hc as [j Hj]. rewrite /run_half in Hj.
      apply list_lookup_insert_Some in Hj as [(_ & <- & _) | (_ & Hj)]; [by left | right; exact (list_elem_of_lookup_2 _ _ _ Hj)]. }
    have Hfits_half : ∀ c, c ∈ run_half → (uint.Z (cell_clock c) + length (ic_run c) < 2^64)%Z.
    { move=> c Hc. destruct (Hsub c Hc) as [-> | HcL].
      - rewrite Hclcl /cl /= length_take. have H := Hnowrapcw. lia.
      - exact (Hrunfits c (proj1 (proj1 (client_run_mem types kc c) HcL))). }
    have Hmem_half : ∀ c, c ∈ run_half → c ∈ all_cells (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types).
    { move=> c Hc. apply list_elem_of_lookup_1 in Hc as [j Hj]. rewrite /run_half in Hj.
      apply list_lookup_insert_Some in Hj as [(_ & <- & _) | (Hne & Hj)].
      - apply all_cells_elem_of. exists parent, {| ty_cells := split_cells cells k o rs; ty_arr := arr |}.
        split; [apply lookup_insert_eq |]. rewrite /= Hsc. apply elem_of_app; right. apply list_elem_of_here.
      - have HcL : c ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hj.
        have Hcne : c ≠ cw. { move=> Heq. rewrite Heq in Hj. exact (Hne (NoDup_lookup _ _ _ _ Hndrun Hkw Hj)). }
        have Hcall : c ∈ all_cells types := proj1 (proj1 (client_run_mem types kc c) HcL).
        apply all_cells_elem_of in Hcall as (p & ts & Hp & Hcts).
        destruct (decide (p = parent)) as [-> | Hpne].
        + rewrite Htypes in Hp. injection Hp as <-. simpl in Hcts.
          rewrite -Hsplit in Hcts. apply elem_of_app in Hcts as [Hcpre | Hcw].
          * apply all_cells_elem_of. exists parent, {| ty_cells := split_cells cells k o rs; ty_arr := arr |}.
            split; [apply lookup_insert_eq |]. rewrite /= Hsc. apply elem_of_app; by left.
          * apply list_elem_of_singleton in Hcw. done.
        + apply all_cells_elem_of. exists p, ts.
          split; [rewrite lookup_insert_ne; [exact Hp | congruence] | exact Hcts]. }
    iEval (rewrite -Hlocs) in "Hslice".
    wp_apply (wp_getNodeIndex slk (DfracOwn 1) (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) run_half (iv.(yjs.item.id').(yjs.id.clock')) kw cl Hss_half Hmem_half Hfits_half Hkw_half Hclk_half with "[$Hslice $Htypes2]").
    iIntros (idx) "(Hslice & Htypes2 & %Hires)".
    destruct Hires as (cres & Hcres & Hcresle & Hcreslt).
    (* pin [uint.nat idx = kw]: the covering cell in [run_half] is [cl] (NoDup locs) *)
    have Hinj : ∀ x y, x ∈ client_run types kc → y ∈ client_run types kc → ic_loc x = ic_loc y → x = y.
    { move=> x y Hx Hy Hxy.
      have Hxa : x ∈ all_cells types := proj1 (proj1 (client_run_mem types kc x) Hx).
      have Hya : y ∈ all_cells types := proj1 (proj1 (client_run_mem types kc y) Hy).
      apply list_elem_of_lookup_1 in Hxa as [ix Hix]. apply list_elem_of_lookup_1 in Hya as [iy Hiy].
      have Hlix : (ic_loc <$> all_cells types) !! ix = Some (ic_loc y) by (rewrite list_lookup_fmap Hix /= Hxy //).
      have Hliy : (ic_loc <$> all_cells types) !! iy = Some (ic_loc y) by (rewrite list_lookup_fmap Hiy //).
      have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnodup Hlix Hliy.
      congruence. }
    have HndLocRun : NoDup (ic_loc <$> client_run types kc).
    { apply NoDup_fmap_inj_on; [exact Hinj | exact Hndrun]. }
    have Hcresmem : cres ∈ run_half := list_elem_of_lookup_2 _ _ _ Hcres.
    have Hcresloc : ic_loc cres = ic_loc cl.
    { destruct (Hsub cres Hcresmem) as [-> | HcresL]; [reflexivity |].
      have Hcresall : cres ∈ all_cells types := proj1 (proj1 (client_run_mem types kc cres) HcresL).
      have Hcrescc : cell_client cres = cell_client cw.
      { rewrite (proj2 (proj1 (client_run_mem types kc cres) HcresL)) -Hcwcc //. }
      destruct (decide (ic_loc cres = ic_loc cw)) as [Heq | Hne].
      - rewrite Heq Hclloc //.
      - exfalso. rewrite -Hcwck in Hcresle Hcreslt.
        destruct (Hdisj cres Hcresall Hcrescc Hne) as [Hd | Hd]; lia. }
    have Hidxloc : (ic_loc <$> run_half) !! (uint.nat idx) = Some (ic_loc cl) by (rewrite list_lookup_fmap Hcres /= Hcresloc //).
    have Hkwloc : (ic_loc <$> run_half) !! kw = Some (ic_loc cl) by (rewrite list_lookup_fmap Hkw_half //).
    have HndLocRunHalf : NoDup (ic_loc <$> run_half) by (rewrite Hlocs; exact HndLocRun).
    have Hidxkw : uint.nat idx = kw := NoDup_lookup _ _ _ _ HndLocRunHalf Hidxloc Hkwloc.
    have Hcrescl : cres = cl.
    { have Htmp : run_half !! kw = Some cres by (rewrite -Hidxkw; exact Hcres). congruence. }
    iEval (rewrite Hlocs) in "Hslice".
    (* ----- the make+copy item-map surgery ----- *)
    iDestruct (own_slice_len with "Hslice") as %[Hslklen Hslklen0].
    rewrite length_fmap in Hslklen Hslklen0.
    have Hnbound : (Z.of_nat (length (client_run types kc)) + 1 < 2^63)%Z by (rewrite -Hcwcc; lia).
    have Hkwlt2 : (kw < length (client_run types kc))%nat by (apply lookup_lt_Some in Hkw).
    have Hidxsint : sint.Z idx = Z.of_nat kw by (move: Hnbound Hkwlt2; rewrite -Hidxkw => ? ?; word).
    wp_auto.
    iDestruct (own_slice_wf with "Hslice") as %Hslkwf.
    (* prefix := nodes[:index+1] *)
    rewrite decide_True; last word.
    wp_auto.
    (* suffix := nodes[index+1:] *)
    rewrite decide_True; last word.
    wp_auto.
    (* newNodes := make([]*item, uint64(len(nodes))+1) *)
    wp_apply wp_slice_make2.
    { iPureIntro. word. }
    iIntros (newSl) "[HnewNodes HnewCap]".
    wp_auto.
    (* copy(newNodes, prefix): split the client slice, copy the disjoint prefix *)
    have Hsplitbnd : (0 ≤ sint.Z (w64_word_instance.(word.add) idx (W64 1)) ≤ sint.Z slk.(slice.len) ≤ sint.Z slk.(slice.len))%Z by word.
    iDestruct (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) (ic_loc <$> client_run types kc) Hsplitbnd with "Hslice") as "(Hsl_pre & Hsl_suf & Hsl_tail)".
    wp_apply (wp_slice_copy with "[$HnewNodes $Hsl_pre]").
    iIntros (nc1) "(%Hnc1 & HnewNodes & Hsl_pre)".
    wp_auto.
    have HnkA : sint.nat (w64_word_instance.(word.add) slk.(slice.len) (W64 1)) = (length (client_run types kc) + 1)%nat by word.
    have HB : (sint.Z (w64_word_instance.(word.add) idx (W64 1)) = Z.of_nat kw + 1)%Z by word.
    have HnkB : sint.nat (w64_word_instance.(word.add) idx (W64 1)) = (kw + 1)%nat by rewrite HB; lia.
    have HnewEq : take (length (replicate (sint.nat (w64_word_instance.(word.add) slk.(slice.len) (W64 1))) (zero_val loc))) (take (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (ic_loc <$> client_run types kc)) ++ drop (length (take (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (ic_loc <$> client_run types kc))) (replicate (sint.nat (w64_word_instance.(word.add) slk.(slice.len) (W64 1))) (zero_val loc)) = take (kw + 1) (ic_loc <$> client_run types kc) ++ replicate (length (client_run types kc) - kw) (zero_val loc).
    { rewrite HnkA HnkB length_replicate take_ge; last first.
      { rewrite length_take length_fmap. lia. }
      rewrite length_take length_fmap Nat.min_l; last lia.
      rewrite drop_replicate. f_equal. f_equal. lia. }
    iEval (rewrite HnewEq) in "HnewNodes".
    iDestruct (own_slice_len with "HnewNodes") as %[HnewLen HnewLen0].
    have HnewLenN : (length (client_run types kc) + 1)%nat = sint.nat newSl.(slice.len).
    { rewrite -HnewLen length_app length_take length_fmap length_replicate.
      clear -Hkwlt2. lia. }
    have HnewLenZ : (sint.Z newSl.(slice.len) = Z.of_nat (length (client_run types kc)) + 1)%Z by (clear -HnewLenN HnewLen0; lia).
    (* newNodes[index+1] = right *)
    rewrite decide_True; last (clear -HB HnewLenZ Hkwlt2; rewrite HB HnewLenZ; lia).
    wp_auto.
    wp_apply (wp_store_slice_index with "[$HnewNodes]").
    { iPureIntro. rewrite length_app length_take length_fmap length_replicate HB.
      clear -Hkwlt2. lia. }
    iIntros "HnewNodes".
    have HinsEq : <[sint.nat (w64_word_instance.(word.add) idx (W64 1)) := rs]> (take (kw + 1) (ic_loc <$> client_run types kc) ++ replicate (length (client_run types kc) - kw) (zero_val loc)) = take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: replicate (length (client_run types kc) - kw - 1) (zero_val loc).
    { rewrite HnkB insert_app_r_alt; last (rewrite length_take length_fmap; clear -Hkwlt2; lia).
      rewrite length_take length_fmap Nat.min_l; last (clear -Hkwlt2; lia).
      have -> : ((kw + 1) - (kw + 1))%nat = 0%nat by lia.
      have -> : (length (client_run types kc) - kw)%nat = S (length (client_run types kc) - kw - 1) by (clear -Hkwlt2; lia).
      simpl. f_equal. f_equal. f_equal. clear -k. lia. }
    iEval (rewrite HinsEq) in "HnewNodes".
    wp_auto.
    (* copy(newNodes[index+2:], suffix) *)
    have HC : (sint.Z (w64_word_instance.(word.add) idx (W64 2)) = Z.of_nat kw + 2)%Z by word.
    iDestruct (own_slice_wf with "HnewNodes") as %HnewWf.
    rewrite decide_True; last (clear -HC HnewLenZ HnewWf Hkwlt2; lia).
    wp_auto.
    have Hsplitbnd2 : (0 ≤ sint.Z (w64_word_instance.(word.add) idx (W64 2)) ≤ sint.Z newSl.(slice.len) ≤ sint.Z newSl.(slice.len))%Z by (clear -HC HnewLenZ Hkwlt2; lia).
    iDestruct (own_slice_slice (w64_word_instance.(word.add) idx (W64 2)) newSl.(slice.len) newSl (DfracOwn 1) _ Hsplitbnd2 with "HnewNodes") as "(Hnn_pre & Hnn_mid & Hnn_tail)".
    wp_apply (wp_slice_copy with "[$Hnn_mid $Hsl_suf]").
    iIntros (nc2) "(%Hnc2 & Hnn_mid & Hsl_suf)".
    have HnkC : sint.nat (w64_word_instance.(word.add) idx (W64 2)) = (kw + 2)%nat by (rewrite HC; clear -k; lia).
    have Esrc : subslice (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (sint.nat slk.(slice.len)) (ic_loc <$> client_run types kc) = drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite HnkB -Hslklen /subslice take_ge; [reflexivity | rewrite length_fmap; clear -Hkwlt2; lia]. }
    have Edst : subslice (sint.nat (w64_word_instance.(word.add) idx (W64 2))) (sint.nat newSl.(slice.len)) (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: replicate (length (client_run types kc) - kw - 1) (zero_val loc)) = replicate (length (client_run types kc) - kw - 1) (zero_val loc).
    { rewrite HnkC -HnewLenN /subslice.
      rewrite take_ge; last (rewrite length_app length_take length_fmap /= length_replicate; clear -Hkwlt2; lia).
      rewrite drop_app_ge; last (rewrite length_take length_fmap; clear -Hkwlt2; lia).
      rewrite length_take length_fmap Nat.min_l; last (clear -Hkwlt2; lia).
      have -> : ((kw + 2) - (kw + 1))%nat = 1%nat by (clear -k; lia).
      simpl. reflexivity. }
    iEval (rewrite Esrc Edst) in "Hnn_mid".
    have Emid : take (length (replicate (length (client_run types kc) - kw - 1) (zero_val loc))) (drop (kw + 1) (ic_loc <$> client_run types kc)) ++ drop (length (drop (kw + 1) (ic_loc <$> client_run types kc))) (replicate (length (client_run types kc) - kw - 1) (zero_val loc)) = drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite length_replicate length_drop length_fmap.
      rewrite take_ge; last (rewrite length_drop length_fmap; clear -Hkwlt2; lia).
      rewrite (drop_ge (replicate (length (client_run types kc) - kw - 1) (zero_val loc))); last (rewrite length_replicate; clear -Hkwlt2; lia).
      apply app_nil_r. }
    iEval (rewrite Emid) in "Hnn_mid".
    (* reassemble newNodes = take (kw+1) ++ rs :: drop (kw+1), and the untouched slk *)
    have Epre : take (sint.nat (w64_word_instance.(word.add) idx (W64 2))) (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: replicate (length (client_run types kc) - kw - 1) (zero_val loc)) = take (kw + 1) (ic_loc <$> client_run types kc) ++ [rs].
    { rewrite HnkC take_app_ge; last (rewrite length_take length_fmap; clear -Hkwlt2; lia).
      rewrite length_take length_fmap Nat.min_l; last (clear -Hkwlt2; lia).
      have -> : ((kw + 2) - (kw + 1))%nat = 1%nat by (clear -k; lia).
      simpl. reflexivity. }
    have Etailcur : drop (sint.nat newSl.(slice.len)) (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: replicate (length (client_run types kc) - kw - 1) (zero_val loc)) = [].
    { rewrite -HnewLenN. apply drop_ge.
      rewrite length_app length_take length_fmap /= length_replicate.
      clear -Hkwlt2. lia. }
    have Efl_take : take (sint.nat (w64_word_instance.(word.add) idx (W64 2))) (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: drop (kw + 1) (ic_loc <$> client_run types kc)) = take (kw + 1) (ic_loc <$> client_run types kc) ++ [rs].
    { rewrite HnkC take_app_ge; last (rewrite length_take length_fmap; clear -Hkwlt2; lia).
      rewrite length_take length_fmap Nat.min_l; last (clear -Hkwlt2; lia).
      have -> : ((kw + 2) - (kw + 1))%nat = 1%nat by (clear -k; lia).
      simpl. reflexivity. }
    have Efl_mid : subslice (sint.nat (w64_word_instance.(word.add) idx (W64 2))) (sint.nat newSl.(slice.len)) (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: drop (kw + 1) (ic_loc <$> client_run types kc)) = drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite HnkC -HnewLenN /subslice.
      rewrite take_ge; last (rewrite length_app length_take length_fmap /= length_drop length_fmap; clear -Hkwlt2; lia).
      rewrite drop_app_ge; last (rewrite length_take length_fmap; clear -Hkwlt2; lia).
      rewrite length_take length_fmap Nat.min_l; last (clear -Hkwlt2; lia).
      have -> : ((kw + 2) - (kw + 1))%nat = 1%nat by (clear -k; lia).
      simpl. reflexivity. }
    have Efl_tail : drop (sint.nat newSl.(slice.len)) (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: drop (kw + 1) (ic_loc <$> client_run types kc)) = [].
    { rewrite -HnewLenN. apply drop_ge.
      rewrite length_app length_take length_fmap /= length_drop length_fmap.
      clear -Hkwlt2. lia. }
    iAssert (newSl ↦* (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: drop (kw + 1) (ic_loc <$> client_run types kc)))%I with "[Hnn_pre Hnn_mid Hnn_tail]" as "HnewNodes".
    { rewrite (own_slice_slice (w64_word_instance.(word.add) idx (W64 2)) newSl.(slice.len) newSl (DfracOwn 1) _ Hsplitbnd2).
      rewrite Efl_take Efl_mid Efl_tail Epre Etailcur.
      iFrame. }
    iAssert (slk ↦* (ic_loc <$> client_run types kc))%I with "[Hsl_pre Hsl_suf Hsl_tail]" as "Hslice".
    { rewrite (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) (ic_loc <$> client_run types kc) Hsplitbnd). iFrame. }
    (* s.items[client] = newNodes: the key read borrows cl's node back from types2 *)
    have Hklt : (k < length cells)%nat by (apply lookup_lt_Some in Hcellk).
    have Hsck : split_cells cells k o rs !! k = Some cl.
    { rewrite Hsc /pre lookup_app_r; last (rewrite length_take; clear -Hklt; lia).
      rewrite length_take Nat.min_l; last (clear -Hklt; lia).
      have -> : (k - k)%nat = 0%nat by (clear -k; lia).
      reflexivity. }
    have Hlk2 : (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) !! parent = Some {| ty_cells := split_cells cells k o rs; ty_arr := arr |} by apply lookup_insert_eq.
    iDestruct (big_sepM_lookup_acc _ _ parent {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Hlk2 with "Htypes2") as "[(Hpc2 & %Harrinv2) Hclose2]".
    iDestruct "Hpc2" as (yt2 tl2) "(Hparent2 & Hdll2 & %Hlen2 & %Hrepr2 & %Hcpar2)".
    iDestruct (own_dll_acc (DfracOwn 1) (split_cells cells k o rs) yt2.(yjs.yType.start') tl2 k cl Hsck with "Hdll2") as (iv2 olid2 orid2) "(%Hcloc2 & %Hcl2 & %Hcr2 & %Hid2 & %Hcontent2 & %Holid2 & %Horid2 & %Hflags2 & %Hrun2 & %Hpar2 & Hcval2 & Hcol2 & Hcor2 & Hback2)".
    iEval (rewrite Hclloc) in "Hcval2".
    have Hkey : iv2.(yjs.item.id').(yjs.id.clientId') = kc.
    { move: Hid2. rewrite Hrhcl' Hid /toYjsId /=. move=> Heq.
      have Hc1 := f_equal clientId Heq. simpl in Hc1. rewrite /kc.
      clear -Hc1. word. }
    wp_auto.
    wp_apply (wp_map_insert with "Hmap").
    iIntros "Hmap".
    iEval (rewrite Hkey) in "Hmap".
    iEval (rewrite -Hclloc) in "Hcval2".
    iDestruct ("Hback2" with "Hcval2") as "Hdll2".
    iAssert (own_ytype_cells parent (DfracOwn 1) (split_cells cells k o rs) arr) with "[Hparent2 Hdll2]" as "Hyt2b".
    { iExists yt2, tl2. iFrame "Hparent2 Hdll2". iPureIntro.
      split_and!; [exact Hlen2 | exact Hrepr2 | exact Hcpar2]. }
    iDestruct ("Hclose2" with "[Hyt2b]") as "Htypes2"; first (iFrame "Hyt2b"; iPureIntro; exact Harrinv2).
    (* the item-map model surgery: the right half's loc lands at position kw+1 *)
    have Hkpcl : cell_kp cl = cell_kp cw.
    { rewrite /cell_kp /cell_pr Hcccl Hclcl Hclloc. reflexivity. }
    have Hkp : cell_kp <$> all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp cr].
    { etransitivity.
      { apply Permutation_map.
        exact (all_cells_insert types parent {| ty_cells := cells; ty_arr := arr |} {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Htypes). }
      simpl. rewrite Hsc.
      etransitivity; last first.
      { apply Permutation_app_tail. apply Permutation_map. symmetry.
        exact (all_cells_lookup types parent {| ty_cells := cells; ty_arr := arr |} Htypes). }
      simpl. rewrite -Hsplit !map_app /= Hkpcl -!app_assoc /=.
      apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    have Hbef : forall y, y ∈ take (kw + 1) (client_run types (cell_client cr)) -> ((cell_pr y).1 < (cell_pr cr).1)%Z.
    { move=> y Hy.
      rewrite Hcccr Hcwcc in Hy.
      apply list_elem_of_lookup_1 in Hy as [j Hj].
      apply lookup_take_Some in Hj as [Hj Hjlt].
      have Hple : (uint.Z (cell_clock y) <= uint.Z (cell_clock cw))%Z.
      { destruct (decide (j = kw)) as [-> | Hne].
        - rewrite Hkw in Hj. injection Hj as <-. lia.
        - exact (StronglySorted_lookup_le cell_le (client_run types kc) j kw y cw (client_run_sorted types kc) Hj Hkw ltac:(clear -Hjlt Hne; lia)). }
      rewrite /cell_pr /= Hccr_clock. clear -Hple Hopos. lia. }
    have Haft : forall y, y ∈ drop (kw + 1) (client_run types (cell_client cr)) -> ((cell_pr cr).1 < (cell_pr y).1)%Z.
    { move=> y Hy.
      rewrite Hcccr Hcwcc in Hy.
      apply list_elem_of_lookup_1 in Hy as [j Hj].
      rewrite lookup_drop in Hj.
      have HyCR : y ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hj.
      have Hyall : y ∈ all_cells types := proj1 (proj1 (client_run_mem types kc y) HyCR).
      have Hycc : cell_client y = cell_client cw.
      { rewrite (proj2 (proj1 (client_run_mem types kc y) HyCR)) Hcwcc //. }
      have Hyne : y ≠ cw.
      { move=> Heq. rewrite Heq in Hj.
        have := NoDup_lookup _ _ _ _ Hndrun Hkw Hj. clear -k. lia. }
      have Hylocne : y.(ic_loc) ≠ cw.(ic_loc).
      { move=> Heq. apply Hyne. exact (Hinj y cw HyCR (list_elem_of_lookup_2 _ _ _ Hkw) Heq). }
      have Hle : (uint.Z (cell_clock cw) <= uint.Z (cell_clock y))%Z.
      { exact (StronglySorted_lookup_le cell_le (client_run types kc) kw (kw + 1 + j) cw y (client_run_sorted types kc) Hkw Hj ltac:(clear -k; lia)). }
      rewrite /cell_pr /= Hccr_clock.
      destruct (Hdisj y Hyall Hycc Hylocne) as [Hd | Hd].
      - exfalso.
        have Hyeq : uint.Z (cell_clock y) = uint.Z (cell_clock cw) by (clear -Hd Hle; lia).
        apply Hylocne. apply (Hclkloc y cw Hyall Hcwmem Hycc).
        rewrite /cell_pr /=. exact Hyeq.
      - clear -Hd Hoinrun. lia. }
    have Hrun_eq := client_run_loc_insert types (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) cr (kw + 1) Hkp Hclkloc Hbef Haft.
    rewrite Hcccr Hcwcc Hcrloc in Hrun_eq.
    iEval (rewrite -Hrun_eq) in "HnewNodes".
    (* re-establish the own_item_map side conditions over types2 *)
    have HinjAll : forall x y, x ∈ all_cells types -> y ∈ all_cells types -> x.(ic_loc) = y.(ic_loc) -> x = y.
    { move=> x y Hx Hy Hxy.
      apply list_elem_of_lookup_1 in Hx as [ix Hix]. apply list_elem_of_lookup_1 in Hy as [iy Hiy].
      have Hlix : (ic_loc <$> all_cells types) !! ix = Some (y.(ic_loc)) by (rewrite list_lookup_fmap Hix /= Hxy //).
      have Hliy : (ic_loc <$> all_cells types) !! iy = Some (y.(ic_loc)) by (rewrite list_lookup_fmap Hiy //).
      have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnodup Hlix Hliy.
      congruence. }
    have Hdecomp : forall c0, c0 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> c0 ∈ all_cells types \/ c0 = cl \/ c0 = cr.
    { move=> c0 Hc0.
      have Hp := all_cells_insert types parent {| ty_cells := cells; ty_arr := arr |} {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Htypes.
      rewrite Hp /= Hsc in Hc0.
      apply elem_of_app in Hc0 as [Hc0 | Hc0].
      - apply elem_of_app in Hc0 as [Hc0 | Hc0].
        + left. apply all_cells_elem_of. exists parent, {| ty_cells := cells; ty_arr := arr |}.
          split; [exact Htypes |]. simpl. rewrite -Hsplit. apply elem_of_app. by left.
        + apply elem_of_cons in Hc0 as [-> | Hc0]; [by right; left |].
          apply elem_of_cons in Hc0 as [-> | Hc0]; [by right; right | by apply elem_of_nil in Hc0].
      - left.
        have Hq := all_cells_lookup types parent {| ty_cells := cells; ty_arr := arr |} Htypes.
        rewrite Hq /=. apply elem_of_app. by right. }
    have Hcomplete2 : forall c0 : w64, c0 ∈ cell_client <$> all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> is_Some (<[kc := newSl]> gm !! c0).
    { move=> c0 Hc0. apply list_elem_of_fmap in Hc0 as (cc & -> & Hcc0).
      destruct (Hdecomp cc Hcc0) as [Hin | [-> | ->]].
      - destruct (decide (cell_client cc = kc)) as [He | Hne].
        + rewrite He lookup_insert_eq. eauto.
        + rewrite lookup_insert_ne; [| congruence]. apply Hcomplete. apply list_elem_of_fmap_2. exact Hin.
      - rewrite Hcccl Hcwcc lookup_insert_eq. eauto.
      - rewrite Hcccr Hcwcc lookup_insert_eq. eauto. }
    have HF2 : forall c, c ∈ all_cells types -> cell_client c = cell_client cw -> (cell_pr c).1 = (cell_pr cr).1 -> False.
    { move=> c Hc Hcc Hpr.
      rewrite /cell_pr /= Hccr_clock in Hpr.
      destruct (decide (c.(ic_loc) = cw.(ic_loc))) as [He | Hne].
      - have Heq : c = cw := HinjAll c cw Hc Hcwmem He.
        rewrite Heq in Hpr. clear -Hpr Hopos. lia.
      - destruct (Hdisj c Hc Hcc Hne) as [Hd | Hd].
        + clear -Hd Hpr Hopos. lia.
        + clear -Hd Hpr Hoinrun. lia. }
    have Hprcl : (cell_pr cl).1 = (cell_pr cw).1 by (rewrite /cell_pr /= Hclcl //).
    have Hclkloc2 : forall c1 c2, c1 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> c2 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> cell_client c1 = cell_client c2 -> (cell_pr c1).1 = (cell_pr c2).1 -> c1.(ic_loc) = c2.(ic_loc).
    { move=> c1 c2 Hc1 Hc2 Hcc Hpr.
      destruct (Hdecomp c1 Hc1) as [Hin1 | [-> | ->]]; destruct (Hdecomp c2 Hc2) as [Hin2 | [-> | ->]].
      - exact (Hclkloc c1 c2 Hin1 Hin2 Hcc Hpr).
      - rewrite Hclloc.
        apply (Hclkloc c1 cw Hin1 Hcwmem); [rewrite Hcc Hcccl // | rewrite Hpr Hprcl //].
      - exfalso. apply (HF2 c1 Hin1); [rewrite Hcc Hcccr // | exact Hpr].
      - rewrite Hclloc. symmetry.
        apply (Hclkloc c2 cw Hin2 Hcwmem); [rewrite -Hcc Hcccl // | rewrite -Hpr Hprcl //].
      - reflexivity.
      - exfalso. rewrite /cell_pr /= Hclcl Hccr_clock in Hpr. clear -Hpr Hopos. lia.
      - exfalso. apply (HF2 c2 Hin2); [rewrite -Hcc Hcccr // | rewrite -Hpr //].
      - exfalso. rewrite /cell_pr /= Hclcl Hccr_clock in Hpr. clear -Hpr Hopos. lia.
      - reflexivity. }
    iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
    iAssert (own_item_map mref (DfracOwn 1) (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types)) with "[Hmap HnewNodes HnewCap Hruns]" as "Hitemmap2".
    { iExists (<[kc := newSl]> gm). iFrame "Hmap".
      iSplitL "HnewNodes HnewCap Hruns".
      - rewrite big_sepM_insert_delete. iSplitL "HnewNodes HnewCap"; [iFrame |].
        iDestruct (big_sepM_delete _ _ kc slk Hslk with "Hruns") as "[_ Hrest]".
        iApply (big_sepM_impl with "Hrest").
        iIntros "!#" (client s0 Hcs) "H". iNamed "H".
        have Hne2 : client ≠ cell_client cr.
        { rewrite Hcccr Hcwcc. move=> Heqc. rewrite Heqc lookup_delete_eq in Hcs. discriminate. }
        rewrite (client_run_loc_other types (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) cr client Hkp Hclkloc Hne2). iFrame.
      - iPureIntro. split; [exact Hcomplete2 | exact Hclkloc2]. }
    wp_auto.
    iApply ("HΦ" $! rs).
    iFrame "Hitemsf Hitemmap2 Htypes2".
    iPureIntro. exact Hrsnn.
  - (* cw has a right neighbour d0: relink d0.left := right, then the same DLL
       split, ytype rebuild, getNodeIndex pin, and item-map surgery as the
       last-cell branch (suf = d0 :: drest threads through own_dll_split's cs2
       and the split_cells shape; the item-map tail is otherwise identical). *)
    iDestruct "Hrest" as (ivd olidd oridd) "(%Hlocd & %Hprevd & %Hpard & %Hidd & %Hcontentd & %Holidd & %Horidd & %Hflagsd & %Hrund & Hvald & Holeftd & Horightd & Hrestd)".
    destruct Hlocd as [Hlocd1 Hlocdnn].
    (* ----- guard (n.right ≠ nil): relink d0.left := right, then n.right := rs ----- *)
    rewrite (bool_decide_eq_false_2 (iv.(yjs.item.right') = null) Hlocdnn).
    iEval (rewrite -Hlocd1) in "Hvald".
    wp_auto.
    iEval (rewrite Hlocd1) in "Hvald".
    set (ivd2 := ivd <| yjs.item.left' := rs |>).
    have Hd2l : ivd2.(yjs.item.left') = rs by reflexivity.
    have Hd2r : ivd2.(yjs.item.right') = ivd.(yjs.item.right') by reflexivity.
    have Hd2p : ivd2.(yjs.item.parent') = ivd.(yjs.item.parent') by reflexivity.
    have Hd2id : ivd2.(yjs.item.id') = ivd.(yjs.item.id') by reflexivity.
    have Hd2c : ivd2.(yjs.item.content') = ivd.(yjs.item.content') by reflexivity.
    have Hd2ol : ivd2.(yjs.item.originLeftId') = ivd.(yjs.item.originLeftId') by reflexivity.
    have Hd2or : ivd2.(yjs.item.originRightId') = ivd.(yjs.item.originRightId') by reflexivity.
    have Hd2f : ivd2.(yjs.item.flags') = ivd.(yjs.item.flags') by reflexivity.
    (* ----- branch-agnostic split-cell pure facts (origin telescoping) ----- *)
    set (cl := split_cell_left cw o).
    set (cr := split_cell_right cw o rs).
    set (oid := {| yjs.id.clientId' := iv.(yjs.item.id').(yjs.id.clientId');
                   yjs.id.clock' := word.sub (word.add iv.(yjs.item.id').(yjs.id.clock') diff) (W64 1) |}).
    have Hopos : (0 < o)%nat by (rewrite /o; lia).
    have Hnowrap_add : (uint.Z iv.(yjs.item.id').(yjs.id.clock') + uint.Z diff < 2^64)%Z.
    { rewrite -Hcwck. have H1 := Hnowrapcw. have H2 := Hdiff. word. }
    have Hadd_eq : (uint.nat iv.(yjs.item.id').(yjs.id.clock') + o)%nat = uint.nat (word.add iv.(yjs.item.id').(yjs.id.clock') diff).
    { rewrite /o. clear -Hnowrap_add. word. }
    have [xprev Hxprev] : is_Some (cw.(ic_run) !! (o - 1)%nat).
    { apply lookup_lt_is_Some. rewrite /o. lia. }
    have Hyo2 : cw.(ic_run) !! S (o - 1)%nat = Some yo.
    { replace (S (o - 1))%nat with o by (rewrite /o; lia). exact Hyo. }
    have Hstep := proj2 Hrun (o - 1)%nat xprev yo Hxprev Hyo2.
    have Horig : origin yo = itemPtr xprev by (destruct Hstep as [_ [Hh _]]; exact Hh).
    have Hxpid := run_wf_lookup_clock cw.(ic_run) (o - 1)%nat (run_head cw) xprev Hrun Hrun0 Hxprev.
    have Hcrorig : origin_id (origin (run_head cr)) = toYjsId <$> Some oid.
    { rewrite /cr Hrhcr Horig /origin_id /=. f_equal.
      rewrite Hxpid Hid /toYjsId /oid /=. f_equal. clear -Hnowrap_add Hdiff. word. }
    have Hrhck : clock (item_id (run_head cw)) = uint.nat iv.(yjs.item.id').(yjs.id.clock') by (rewrite Hid /toYjsId /=).
    have Hclcl : cell_clock cl = cell_clock cw by (rewrite /cl /cell_clock Hrhcl).
    have Hcccl : cell_client cl = cell_client cw by (rewrite /cl /cell_client Hrhcl).
    have Hcccr : cell_client cr = cell_client cw by (rewrite /cr /cell_client Hrhcr Hyoid /=).
    have Hccr_clock : uint.Z (cell_clock cr) = (uint.Z (cell_clock cw) + Z.of_nat o)%Z.
    { rewrite /cr /cell_clock Hrhcr Hyoid /= Hrhck. clear -Hnowrap_add Hdiff. rewrite /o. word. }
    have Hsc : split_cells cells k o rs = pre ++ cl :: cr :: d0 :: drest.
    { rewrite /split_cells Hcellk. rewrite -/suf Hsufeq. reflexivity. }
    (* the split-cell struct values [ivl] (truncated cw) / [ivr] (right half) *)
    set (ivl := iv <| yjs.item.content' := {| yjs.content.content' := take (sint.nat diff) iv.(yjs.item.content').(yjs.content.content') |} |> <| yjs.item.right' := rs |>).
    set (ivr := {| yjs.item.id' := {| yjs.id.clientId' := iv.(yjs.item.id').(yjs.id.clientId'); yjs.id.clock' := word.add iv.(yjs.item.id').(yjs.id.clock') diff |};
                   yjs.item.originLeftId' := olid_ptr;
                   yjs.item.originRightId' := iv.(yjs.item.originRightId');
                   yjs.item.left' := cw.(ic_loc);
                   yjs.item.right' := iv.(yjs.item.right');
                   yjs.item.parent' := iv.(yjs.item.parent');
                   yjs.item.content' := {| yjs.content.content' := subslice (sint.nat diff) (sint.nat cbs.(slice.len)) iv.(yjs.item.content').(yjs.content.content') |};
                   yjs.item.flags' := iv.(yjs.item.flags') |}).
    have Hivl_ol : ivl.(yjs.item.originLeftId') = iv.(yjs.item.originLeftId') by (rewrite /ivl /=).
    have Hivl_or : ivl.(yjs.item.originRightId') = iv.(yjs.item.originRightId') by (rewrite /ivl /=).
    have Hivl_left : ivl.(yjs.item.left') = ml by (rewrite /ivl /=; exact Hprev).
    have Hivr_r : ivr.(yjs.item.right') = iv.(yjs.item.right') by reflexivity.
    have Hrhcl' : run_head cl = run_head cw by (rewrite /cl; exact Hrhcl).
    have Hrhcr' : run_head cr = yo by (rewrite /cr; exact Hrhcr).
    have Hrhcli : clientId (item_id (run_head cw)) = uint.nat iv.(yjs.item.id').(yjs.id.clientId') by (rewrite Hid /toYjsId /=).
    have Hclloc : ic_loc cl = cw.(ic_loc) by (rewrite /cl /=).
    have Hcrloc : ic_loc cr = rs by (rewrite /cr /=).
    have Hivr_ol : ivr.(yjs.item.originLeftId') = olid_ptr by (rewrite /ivr /=).
    have Hivr_or : ivr.(yjs.item.originRightId') = iv.(yjs.item.originRightId') by (rewrite /ivr /=).
    have Hp1 : ic_loc cl ≠ null by (rewrite /cl /=; exact Hmfnn).
    have Hp2 : ic_loc cr ≠ null by (rewrite /cr /=; exact Hrsnn).
    have Hp4 : ivl.(yjs.item.right') = ic_loc cr by (rewrite /ivl /cr /=).
    have Hp5 : ivl.(yjs.item.parent') = ic_parent cl by (rewrite /ivl /cl /=; exact Hpar).
    have Hp6 : item_id (run_head cl) = toYjsId ivl.(yjs.item.id'). { rewrite Hrhcl' /ivl /=. exact Hid. }
    have Hp7 : content <$> ic_run cl = explode (toContent ivl.(yjs.item.content')). { rewrite /cl /ivl /toContent /=. exact Hcontl. }
    have Hp8 : origin_id (origin (run_head cl)) = toYjsId <$> olidcw. { rewrite Hrhcl'. exact Holid. }
    have Hp9 : origin_id (rightOrigin (run_head cl)) = toYjsId <$> oridcw. { rewrite Hrhcl'. exact Horid. }
    have Hp10 : ivl.(yjs.item.flags') = (if ic_deleted cl then W8 6 else W8 2). { rewrite /ivl /cl /=. exact Hflags. }
    have Hp11 : run_wf (ic_run cl). { rewrite /cl /=. exact (run_wf_take cw.(ic_run) o Hopos Hrun). }
    have Hp12 : ivr.(yjs.item.left') = ic_loc cl. { rewrite /ivr /cl /=. reflexivity. }
    have Hp13 : ivr.(yjs.item.parent') = ic_parent cr. { rewrite /ivr /cr /=. exact Hpar. }
    have Hp14 : item_id (run_head cr) = toYjsId ivr.(yjs.item.id'). { rewrite Hrhcr' Hyoid /ivr /toYjsId /=. rewrite Hrhck Hrhcli Hadd_eq. reflexivity. }
    have Hp15 : content <$> ic_run cr = explode (toContent ivr.(yjs.item.content')). { rewrite /cr /ivr /toContent /= Hsubdrop. exact Hcontr. }
    have Hp17 : origin_id (rightOrigin (run_head cr)) = toYjsId <$> oridcw. { rewrite Hrhcr' Hyoro. exact Horid. }
    have Hp18 : ivr.(yjs.item.flags') = (if ic_deleted cr then W8 6 else W8 2). { rewrite /ivr /cr /=. exact Hflags. }
    have Hp19 : run_wf (ic_run cr). { rewrite /cr /=. exact (run_wf_drop cw.(ic_run) o Hoinrun Hrun). }
    (* ----- read the client run slice (map.lookup1), BEFORE Phase A locks cw ----- *)
    iNamed "Hitemmap".
    set (kc := iv.(yjs.item.id').(yjs.id.clientId')).
    have Hcwcc : cell_client cw = kc by (rewrite /cell_client Hrhcli /kc; word).
    have Hkcin : kc ∈ (cell_client <$> all_cells types).
    { rewrite -Hcwcc. apply list_elem_of_fmap_2. exact Hcwmem. }
    have Hcwrun : cw ∈ client_run types kc.
    { apply client_run_mem. split; [exact Hcwmem | exact Hcwcc]. }
    apply list_elem_of_lookup_1 in Hcwrun. destruct Hcwrun as [kw Hkw].
    destruct (Hcomplete kc Hkcin) as [slk Hslk].
    iDestruct (big_sepM_lookup_acc _ _ kc slk Hslk with "Hruns") as "[Hrunslk Hrunsback]".
    iNamed "Hrunslk".
    wp_apply (wp_map_lookup1 with "Hmap"). iIntros "Hmap".
    rewrite Hslk /=.
    wp_auto.
    (* ----- Phase A: reassemble the suffix DLL behind [cr], own_dll_split, close ----- *)
    iAssert (own_dll (DfracOwn 1) iv.(yjs.item.right') tl0 rs null (d0 :: drest))
      with "[Hvald Holeftd Horightd Hrestd]" as "Hsufdll".
    { simpl. iExists ivd2, olidd, oridd.
      rewrite Hd2ol Hd2or Hd2r.
      iFrame "Hvald Holeftd Horightd Hrestd".
      iPureIntro. split_and!;
        [ exact Hlocd1 | exact Hlocdnn | exact Hd2l
        | rewrite Hd2p; exact Hpard
        | rewrite Hd2id; exact Hidd
        | rewrite Hd2c; exact Hcontentd
        | exact Holidd | exact Horidd
        | rewrite Hd2f; exact Hflagsd | exact Hrund ]. }
    iAssert (own_dll (DfracOwn 1) yt.(yjs.yType.start') tl0 null null (split_cells cells k o rs))
      with "[Hseg1 Hval Holeft Horight Hrs Hsufdll]" as "Hdll2".
    { rewrite Hsc.
      iApply (own_dll_split (DfracOwn 1) pre (d0 :: drest) cl cr ivl ivr olidcw oridcw (Some oid) oridcw yt.(yjs.yType.start') tl0 ml Hp1 Hp2 Hivl_left Hp4 Hp5 Hp6 Hp7 Hp8 Hp9 Hp10 Hp11 Hp12 Hp13 Hp14 Hp15 Hcrorig Hp17 Hp18 Hp19).
      rewrite Hclloc Hcrloc Hivl_ol Hivl_or Hivr_ol Hivr_or Hivr_r.
      iDestruct "Horight" as "#HorightP".
      (* [iFrame "HorightP"] would leak into the cons segment's existentials
         (the fix unfolds on [d0 :: drest]); split the conjuncts off by hand. *)
      iFrame "Hseg1 Hval Hrs Holeft".
      iSplitR; first iExact "HorightP".
      iSplitR.
      { simpl. iFrame "olid". iPureIntro. exact Holidnn. }
      iSplitR; first iExact "HorightP".
      iExact "Hsufdll". }
    have Hcparcw : ic_parent cw = parent by (apply Hcpar0; apply (list_elem_of_lookup_2 _ _ _ Hcellk)).
    have Hcpar_split : ∀ c, c ∈ split_cells cells k o rs -> ic_parent c = parent.
    { rewrite Hsc. move=> c Hc. apply elem_of_app in Hc as [Hc | Hc].
      - apply Hcpar0. rewrite -Hsplit. apply elem_of_app; by left.
      - apply elem_of_cons in Hc as [-> | Hc]; [rewrite /cl /=; exact Hcparcw |].
        apply elem_of_cons in Hc as [-> | Hc]; [rewrite /cr /=; exact Hcparcw |].
        apply Hcpar0. rewrite -Hsplit. apply elem_of_app; right.
        apply elem_of_cons; right. exact Hc. }
    iAssert (own_ytype_cells parent (DfracOwn 1) (split_cells cells k o rs) arr) with "[Hparent Hdll2]" as "Hyt2".
    { iExists yt, tl0. iFrame "Hparent Hdll2". iPureIntro. split_and!.
      - rewrite (split_cells_num_visible cells k o rs cw Hcellk). exact Hlen0.
      - rewrite /cells_repr (split_cells_flatten cells k o rs cw Hcellk). exact Hrepr0.
      - exact Hcpar_split. }
    iDestruct ("Hclose" $! {| ty_cells := split_cells cells k o rs; ty_arr := arr |} with "[Hyt2]") as "Htypes2".
    { iFrame "Hyt2". iPureIntro. exact Harrinv. }
    (* ----- getNodeIndex over the split run [run_half] = client_run with cw -> cl ----- *)
    have Hss_replace : ∀ (ll : list item_cell) (i : nat) (a b : item_cell),
        StronglySorted cell_le ll → ll !! i = Some a → cell_clock b = cell_clock a →
        StronglySorted cell_le (<[i:=b]> ll).
    { elim => [| c ll IH] i a b Hss Hi Hclk.
      - by rewrite /=.
      - apply StronglySorted_inv in Hss as [Hssll Hfa].
        destruct i as [|i']; simpl.
        + simpl in Hi. injection Hi as Hca. rewrite Hca in Hfa.
          apply SSorted_cons; [exact Hssll |].
          apply Forall_forall => x Hx. rewrite /cell_le Hclk.
          exact (proj1 (Forall_forall _ _) Hfa x Hx).
        + apply SSorted_cons; [exact (IH i' a b Hssll Hi Hclk) |].
          apply Forall_insert; [exact Hfa |].
          rewrite /cell_le Hclk.
          exact (proj1 (Forall_forall _ _) Hfa a (list_elem_of_lookup_2 ll i' a Hi)). }
    have Hss_half : StronglySorted cell_le (<[kw := cl]> (client_run types kc)) := Hss_replace (client_run types kc) kw cw cl (client_run_sorted types kc) Hkw Hclcl.
    set (run_half := <[kw := cl]> (client_run types kc)).
    have HndAll : NoDup (all_cells types) := NoDup_fmap_1 ic_loc _ Hnodup.
    have Hndrun : NoDup (client_run types kc).
    { rewrite /client_run (merge_sort_Permutation cell_le _). apply NoDup_filter. exact HndAll. }
    have Hkwlt : (kw < length (client_run types kc))%nat by (apply lookup_lt_Some in Hkw; exact Hkw).
    have Hlockw : (ic_loc <$> client_run types kc) !! kw = Some (ic_loc cl).
    { rewrite list_lookup_fmap Hkw /=. done. }
    have Hlocs : ic_loc <$> run_half = ic_loc <$> client_run types kc.
    { rewrite /run_half list_fmap_insert (list_insert_id _ _ _ Hlockw) //. }
    have Hkw_half : run_half !! kw = Some cl.
    { rewrite /run_half. apply list_lookup_insert_Some. left. split_and!; [reflexivity | reflexivity | exact Hkwlt]. }
    have Hclk_half : cell_clock cl = iv.(yjs.item.id').(yjs.id.clock') by (rewrite Hclcl Hcwck).
    have Hsub : ∀ c, c ∈ run_half → c = cl ∨ c ∈ client_run types kc.
    { move=> c Hc. apply list_elem_of_lookup_1 in Hc as [j Hj]. rewrite /run_half in Hj.
      apply list_lookup_insert_Some in Hj as [(_ & <- & _) | (_ & Hj)]; [by left | right; exact (list_elem_of_lookup_2 _ _ _ Hj)]. }
    have Hfits_half : ∀ c, c ∈ run_half → (uint.Z (cell_clock c) + length (ic_run c) < 2^64)%Z.
    { move=> c Hc. destruct (Hsub c Hc) as [-> | HcL].
      - rewrite Hclcl /cl /= length_take. have H := Hnowrapcw. lia.
      - exact (Hrunfits c (proj1 (proj1 (client_run_mem types kc c) HcL))). }
    have Hmem_half : ∀ c, c ∈ run_half → c ∈ all_cells (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types).
    { move=> c Hc. apply list_elem_of_lookup_1 in Hc as [j Hj]. rewrite /run_half in Hj.
      apply list_lookup_insert_Some in Hj as [(_ & <- & _) | (Hne & Hj)].
      - apply all_cells_elem_of. exists parent, {| ty_cells := split_cells cells k o rs; ty_arr := arr |}.
        split; [apply lookup_insert_eq |]. rewrite /= Hsc. apply elem_of_app; right. apply list_elem_of_here.
      - have HcL : c ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hj.
        have Hcne : c ≠ cw. { move=> Heq. rewrite Heq in Hj. exact (Hne (NoDup_lookup _ _ _ _ Hndrun Hkw Hj)). }
        have Hcall : c ∈ all_cells types := proj1 (proj1 (client_run_mem types kc c) HcL).
        apply all_cells_elem_of in Hcall as (p & ts & Hp & Hcts).
        destruct (decide (p = parent)) as [-> | Hpne].
        + rewrite Htypes in Hp. injection Hp as <-. simpl in Hcts.
          rewrite -Hsplit in Hcts. apply elem_of_app in Hcts as [Hcpre | Hcw].
          * apply all_cells_elem_of. exists parent, {| ty_cells := split_cells cells k o rs; ty_arr := arr |}.
            split; [apply lookup_insert_eq |]. rewrite /= Hsc. apply elem_of_app; by left.
          * apply elem_of_cons in Hcw as [-> | Hcsuf]; [done |].
            apply all_cells_elem_of. exists parent, {| ty_cells := split_cells cells k o rs; ty_arr := arr |}.
            split; [apply lookup_insert_eq |]. rewrite /= Hsc. apply elem_of_app; right.
            apply elem_of_cons; right. apply elem_of_cons; right. exact Hcsuf.
        + apply all_cells_elem_of. exists p, ts.
          split; [rewrite lookup_insert_ne; [exact Hp | congruence] | exact Hcts]. }
    iEval (rewrite -Hlocs) in "Hslice".
    wp_apply (wp_getNodeIndex slk (DfracOwn 1) (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) run_half (iv.(yjs.item.id').(yjs.id.clock')) kw cl Hss_half Hmem_half Hfits_half Hkw_half Hclk_half with "[$Hslice $Htypes2]").
    iIntros (idx) "(Hslice & Htypes2 & %Hires)".
    destruct Hires as (cres & Hcres & Hcresle & Hcreslt).
    (* pin [uint.nat idx = kw]: the covering cell in [run_half] is [cl] (NoDup locs) *)
    have Hinj : ∀ x y, x ∈ client_run types kc → y ∈ client_run types kc → ic_loc x = ic_loc y → x = y.
    { move=> x y Hx Hy Hxy.
      have Hxa : x ∈ all_cells types := proj1 (proj1 (client_run_mem types kc x) Hx).
      have Hya : y ∈ all_cells types := proj1 (proj1 (client_run_mem types kc y) Hy).
      apply list_elem_of_lookup_1 in Hxa as [ix Hix]. apply list_elem_of_lookup_1 in Hya as [iy Hiy].
      have Hlix : (ic_loc <$> all_cells types) !! ix = Some (ic_loc y) by (rewrite list_lookup_fmap Hix /= Hxy //).
      have Hliy : (ic_loc <$> all_cells types) !! iy = Some (ic_loc y) by (rewrite list_lookup_fmap Hiy //).
      have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnodup Hlix Hliy.
      congruence. }
    have HndLocRun : NoDup (ic_loc <$> client_run types kc).
    { apply NoDup_fmap_inj_on; [exact Hinj | exact Hndrun]. }
    have Hcresmem : cres ∈ run_half := list_elem_of_lookup_2 _ _ _ Hcres.
    have Hcresloc : ic_loc cres = ic_loc cl.
    { destruct (Hsub cres Hcresmem) as [-> | HcresL]; [reflexivity |].
      have Hcresall : cres ∈ all_cells types := proj1 (proj1 (client_run_mem types kc cres) HcresL).
      have Hcrescc : cell_client cres = cell_client cw.
      { rewrite (proj2 (proj1 (client_run_mem types kc cres) HcresL)) -Hcwcc //. }
      destruct (decide (ic_loc cres = ic_loc cw)) as [Heq | Hne].
      - rewrite Heq Hclloc //.
      - exfalso. rewrite -Hcwck in Hcresle Hcreslt.
        destruct (Hdisj cres Hcresall Hcrescc Hne) as [Hd | Hd]; lia. }
    have Hidxloc : (ic_loc <$> run_half) !! (uint.nat idx) = Some (ic_loc cl) by (rewrite list_lookup_fmap Hcres /= Hcresloc //).
    have Hkwloc : (ic_loc <$> run_half) !! kw = Some (ic_loc cl) by (rewrite list_lookup_fmap Hkw_half //).
    have HndLocRunHalf : NoDup (ic_loc <$> run_half) by (rewrite Hlocs; exact HndLocRun).
    have Hidxkw : uint.nat idx = kw := NoDup_lookup _ _ _ _ HndLocRunHalf Hidxloc Hkwloc.
    have Hcrescl : cres = cl.
    { have Htmp : run_half !! kw = Some cres by (rewrite -Hidxkw; exact Hcres). congruence. }
    iEval (rewrite Hlocs) in "Hslice".
    (* ----- the make+copy item-map surgery ----- *)
    iDestruct (own_slice_len with "Hslice") as %[Hslklen Hslklen0].
    rewrite length_fmap in Hslklen Hslklen0.
    have Hnbound : (Z.of_nat (length (client_run types kc)) + 1 < 2^63)%Z by (rewrite -Hcwcc; lia).
    have Hkwlt2 : (kw < length (client_run types kc))%nat by (apply lookup_lt_Some in Hkw).
    have Hidxsint : sint.Z idx = Z.of_nat kw by (move: Hnbound Hkwlt2; rewrite -Hidxkw => ? ?; word).
    wp_auto.
    iDestruct (own_slice_wf with "Hslice") as %Hslkwf.
    (* prefix := nodes[:index+1] *)
    rewrite decide_True; last word.
    wp_auto.
    (* suffix := nodes[index+1:] *)
    rewrite decide_True; last word.
    wp_auto.
    (* newNodes := make([]*item, uint64(len(nodes))+1) *)
    wp_apply wp_slice_make2.
    { iPureIntro. word. }
    iIntros (newSl) "[HnewNodes HnewCap]".
    wp_auto.
    (* copy(newNodes, prefix): split the client slice, copy the disjoint prefix *)
    have Hsplitbnd : (0 ≤ sint.Z (w64_word_instance.(word.add) idx (W64 1)) ≤ sint.Z slk.(slice.len) ≤ sint.Z slk.(slice.len))%Z by word.
    iDestruct (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) (ic_loc <$> client_run types kc) Hsplitbnd with "Hslice") as "(Hsl_pre & Hsl_suf & Hsl_tail)".
    wp_apply (wp_slice_copy with "[$HnewNodes $Hsl_pre]").
    iIntros (nc1) "(%Hnc1 & HnewNodes & Hsl_pre)".
    wp_auto.
    have HnkA : sint.nat (w64_word_instance.(word.add) slk.(slice.len) (W64 1)) = (length (client_run types kc) + 1)%nat by word.
    have HB : (sint.Z (w64_word_instance.(word.add) idx (W64 1)) = Z.of_nat kw + 1)%Z by word.
    have HnkB : sint.nat (w64_word_instance.(word.add) idx (W64 1)) = (kw + 1)%nat by rewrite HB; lia.
    have HnewEq : take (length (replicate (sint.nat (w64_word_instance.(word.add) slk.(slice.len) (W64 1))) (zero_val loc))) (take (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (ic_loc <$> client_run types kc)) ++ drop (length (take (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (ic_loc <$> client_run types kc))) (replicate (sint.nat (w64_word_instance.(word.add) slk.(slice.len) (W64 1))) (zero_val loc)) = take (kw + 1) (ic_loc <$> client_run types kc) ++ replicate (length (client_run types kc) - kw) (zero_val loc).
    { rewrite HnkA HnkB length_replicate take_ge; last first.
      { rewrite length_take length_fmap. lia. }
      rewrite length_take length_fmap Nat.min_l; last lia.
      rewrite drop_replicate. f_equal. f_equal. lia. }
    iEval (rewrite HnewEq) in "HnewNodes".
    iDestruct (own_slice_len with "HnewNodes") as %[HnewLen HnewLen0].
    have HnewLenN : (length (client_run types kc) + 1)%nat = sint.nat newSl.(slice.len).
    { rewrite -HnewLen length_app length_take length_fmap length_replicate.
      clear -Hkwlt2. lia. }
    have HnewLenZ : (sint.Z newSl.(slice.len) = Z.of_nat (length (client_run types kc)) + 1)%Z by (clear -HnewLenN HnewLen0; lia).
    (* newNodes[index+1] = right *)
    rewrite decide_True; last (clear -HB HnewLenZ Hkwlt2; rewrite HB HnewLenZ; lia).
    wp_auto.
    wp_apply (wp_store_slice_index with "[$HnewNodes]").
    { iPureIntro. rewrite length_app length_take length_fmap length_replicate HB.
      clear -Hkwlt2. lia. }
    iIntros "HnewNodes".
    have HinsEq : <[sint.nat (w64_word_instance.(word.add) idx (W64 1)) := rs]> (take (kw + 1) (ic_loc <$> client_run types kc) ++ replicate (length (client_run types kc) - kw) (zero_val loc)) = take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: replicate (length (client_run types kc) - kw - 1) (zero_val loc).
    { rewrite HnkB insert_app_r_alt; last (rewrite length_take length_fmap; clear -Hkwlt2; lia).
      rewrite length_take length_fmap Nat.min_l; last (clear -Hkwlt2; lia).
      have -> : ((kw + 1) - (kw + 1))%nat = 0%nat by lia.
      have -> : (length (client_run types kc) - kw)%nat = S (length (client_run types kc) - kw - 1) by (clear -Hkwlt2; lia).
      simpl. f_equal. f_equal. f_equal. clear -k. lia. }
    iEval (rewrite HinsEq) in "HnewNodes".
    wp_auto.
    (* copy(newNodes[index+2:], suffix) *)
    have HC : (sint.Z (w64_word_instance.(word.add) idx (W64 2)) = Z.of_nat kw + 2)%Z by word.
    iDestruct (own_slice_wf with "HnewNodes") as %HnewWf.
    rewrite decide_True; last (clear -HC HnewLenZ HnewWf Hkwlt2; lia).
    wp_auto.
    have Hsplitbnd2 : (0 ≤ sint.Z (w64_word_instance.(word.add) idx (W64 2)) ≤ sint.Z newSl.(slice.len) ≤ sint.Z newSl.(slice.len))%Z by (clear -HC HnewLenZ Hkwlt2; lia).
    iDestruct (own_slice_slice (w64_word_instance.(word.add) idx (W64 2)) newSl.(slice.len) newSl (DfracOwn 1) _ Hsplitbnd2 with "HnewNodes") as "(Hnn_pre & Hnn_mid & Hnn_tail)".
    wp_apply (wp_slice_copy with "[$Hnn_mid $Hsl_suf]").
    iIntros (nc2) "(%Hnc2 & Hnn_mid & Hsl_suf)".
    have HnkC : sint.nat (w64_word_instance.(word.add) idx (W64 2)) = (kw + 2)%nat by (rewrite HC; clear -k; lia).
    have Esrc : subslice (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (sint.nat slk.(slice.len)) (ic_loc <$> client_run types kc) = drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite HnkB -Hslklen /subslice take_ge; [reflexivity | rewrite length_fmap; clear -Hkwlt2; lia]. }
    have Edst : subslice (sint.nat (w64_word_instance.(word.add) idx (W64 2))) (sint.nat newSl.(slice.len)) (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: replicate (length (client_run types kc) - kw - 1) (zero_val loc)) = replicate (length (client_run types kc) - kw - 1) (zero_val loc).
    { rewrite HnkC -HnewLenN /subslice.
      rewrite take_ge; last (rewrite length_app length_take length_fmap /= length_replicate; clear -Hkwlt2; lia).
      rewrite drop_app_ge; last (rewrite length_take length_fmap; clear -Hkwlt2; lia).
      rewrite length_take length_fmap Nat.min_l; last (clear -Hkwlt2; lia).
      have -> : ((kw + 2) - (kw + 1))%nat = 1%nat by (clear -k; lia).
      simpl. reflexivity. }
    iEval (rewrite Esrc Edst) in "Hnn_mid".
    have Emid : take (length (replicate (length (client_run types kc) - kw - 1) (zero_val loc))) (drop (kw + 1) (ic_loc <$> client_run types kc)) ++ drop (length (drop (kw + 1) (ic_loc <$> client_run types kc))) (replicate (length (client_run types kc) - kw - 1) (zero_val loc)) = drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite length_replicate length_drop length_fmap.
      rewrite take_ge; last (rewrite length_drop length_fmap; clear -Hkwlt2; lia).
      rewrite (drop_ge (replicate (length (client_run types kc) - kw - 1) (zero_val loc))); last (rewrite length_replicate; clear -Hkwlt2; lia).
      apply app_nil_r. }
    iEval (rewrite Emid) in "Hnn_mid".
    (* reassemble newNodes = take (kw+1) ++ rs :: drop (kw+1), and the untouched slk *)
    have Epre : take (sint.nat (w64_word_instance.(word.add) idx (W64 2))) (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: replicate (length (client_run types kc) - kw - 1) (zero_val loc)) = take (kw + 1) (ic_loc <$> client_run types kc) ++ [rs].
    { rewrite HnkC take_app_ge; last (rewrite length_take length_fmap; clear -Hkwlt2; lia).
      rewrite length_take length_fmap Nat.min_l; last (clear -Hkwlt2; lia).
      have -> : ((kw + 2) - (kw + 1))%nat = 1%nat by (clear -k; lia).
      simpl. reflexivity. }
    have Etailcur : drop (sint.nat newSl.(slice.len)) (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: replicate (length (client_run types kc) - kw - 1) (zero_val loc)) = [].
    { rewrite -HnewLenN. apply drop_ge.
      rewrite length_app length_take length_fmap /= length_replicate.
      clear -Hkwlt2. lia. }
    have Efl_take : take (sint.nat (w64_word_instance.(word.add) idx (W64 2))) (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: drop (kw + 1) (ic_loc <$> client_run types kc)) = take (kw + 1) (ic_loc <$> client_run types kc) ++ [rs].
    { rewrite HnkC take_app_ge; last (rewrite length_take length_fmap; clear -Hkwlt2; lia).
      rewrite length_take length_fmap Nat.min_l; last (clear -Hkwlt2; lia).
      have -> : ((kw + 2) - (kw + 1))%nat = 1%nat by (clear -k; lia).
      simpl. reflexivity. }
    have Efl_mid : subslice (sint.nat (w64_word_instance.(word.add) idx (W64 2))) (sint.nat newSl.(slice.len)) (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: drop (kw + 1) (ic_loc <$> client_run types kc)) = drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite HnkC -HnewLenN /subslice.
      rewrite take_ge; last (rewrite length_app length_take length_fmap /= length_drop length_fmap; clear -Hkwlt2; lia).
      rewrite drop_app_ge; last (rewrite length_take length_fmap; clear -Hkwlt2; lia).
      rewrite length_take length_fmap Nat.min_l; last (clear -Hkwlt2; lia).
      have -> : ((kw + 2) - (kw + 1))%nat = 1%nat by (clear -k; lia).
      simpl. reflexivity. }
    have Efl_tail : drop (sint.nat newSl.(slice.len)) (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: drop (kw + 1) (ic_loc <$> client_run types kc)) = [].
    { rewrite -HnewLenN. apply drop_ge.
      rewrite length_app length_take length_fmap /= length_drop length_fmap.
      clear -Hkwlt2. lia. }
    iAssert (newSl ↦* (take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: drop (kw + 1) (ic_loc <$> client_run types kc)))%I with "[Hnn_pre Hnn_mid Hnn_tail]" as "HnewNodes".
    { rewrite (own_slice_slice (w64_word_instance.(word.add) idx (W64 2)) newSl.(slice.len) newSl (DfracOwn 1) _ Hsplitbnd2).
      rewrite Efl_take Efl_mid Efl_tail Epre Etailcur.
      iFrame. }
    iAssert (slk ↦* (ic_loc <$> client_run types kc))%I with "[Hsl_pre Hsl_suf Hsl_tail]" as "Hslice".
    { rewrite (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) (ic_loc <$> client_run types kc) Hsplitbnd). iFrame. }
    (* s.items[client] = newNodes: the key read borrows cl's node back from types2 *)
    have Hklt : (k < length cells)%nat by (apply lookup_lt_Some in Hcellk).
    have Hsck : split_cells cells k o rs !! k = Some cl.
    { rewrite Hsc /pre lookup_app_r; last (rewrite length_take; clear -Hklt; lia).
      rewrite length_take Nat.min_l; last (clear -Hklt; lia).
      have -> : (k - k)%nat = 0%nat by (clear -k; lia).
      reflexivity. }
    have Hlk2 : (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) !! parent = Some {| ty_cells := split_cells cells k o rs; ty_arr := arr |} by apply lookup_insert_eq.
    iDestruct (big_sepM_lookup_acc _ _ parent {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Hlk2 with "Htypes2") as "[(Hpc2 & %Harrinv2) Hclose2]".
    iDestruct "Hpc2" as (yt2 tl2) "(Hparent2 & Hdll3 & %Hlen2 & %Hrepr2 & %Hcpar2)".
    iDestruct (own_dll_acc (DfracOwn 1) (split_cells cells k o rs) yt2.(yjs.yType.start') tl2 k cl Hsck with "Hdll3") as (iv2 olid2 orid2) "(%Hcloc2 & %Hcl2 & %Hcr2 & %Hid2 & %Hcontent2 & %Holid2 & %Horid2 & %Hflags2 & %Hrun2 & %Hpar2 & Hcval2 & Hcol2 & Hcor2 & Hback2)".
    iEval (rewrite Hclloc) in "Hcval2".
    have Hkey : iv2.(yjs.item.id').(yjs.id.clientId') = kc.
    { move: Hid2. rewrite Hrhcl' Hid /toYjsId /=. move=> Heq.
      have Hc1 := f_equal clientId Heq. simpl in Hc1. rewrite /kc.
      clear -Hc1. word. }
    wp_auto.
    wp_apply (wp_map_insert with "Hmap").
    iIntros "Hmap".
    iEval (rewrite Hkey) in "Hmap".
    iEval (rewrite -Hclloc) in "Hcval2".
    iDestruct ("Hback2" with "Hcval2") as "Hdll3".
    iAssert (own_ytype_cells parent (DfracOwn 1) (split_cells cells k o rs) arr) with "[Hparent2 Hdll3]" as "Hyt2b".
    { iExists yt2, tl2. iFrame "Hparent2 Hdll3". iPureIntro.
      split_and!; [exact Hlen2 | exact Hrepr2 | exact Hcpar2]. }
    iDestruct ("Hclose2" with "[Hyt2b]") as "Htypes2"; first (iFrame "Hyt2b"; iPureIntro; exact Harrinv2).
    (* the item-map model surgery: the right half's loc lands at position kw+1 *)
    have Hkpcl : cell_kp cl = cell_kp cw.
    { rewrite /cell_kp /cell_pr Hcccl Hclcl Hclloc. reflexivity. }
    have Hkp : cell_kp <$> all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp cr].
    { etransitivity.
      { apply Permutation_map.
        exact (all_cells_insert types parent {| ty_cells := cells; ty_arr := arr |} {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Htypes). }
      simpl. rewrite Hsc.
      etransitivity; last first.
      { apply Permutation_app_tail. apply Permutation_map. symmetry.
        exact (all_cells_lookup types parent {| ty_cells := cells; ty_arr := arr |} Htypes). }
      simpl. rewrite -Hsplit !map_app /= Hkpcl -!app_assoc /=.
      apply Permutation_app_head. apply perm_skip.
      etransitivity; [apply Permutation_cons_append |].
      simpl. rewrite -!app_assoc. reflexivity. }
    have Hbef : forall y, y ∈ take (kw + 1) (client_run types (cell_client cr)) -> ((cell_pr y).1 < (cell_pr cr).1)%Z.
    { move=> y Hy.
      rewrite Hcccr Hcwcc in Hy.
      apply list_elem_of_lookup_1 in Hy as [j Hj].
      apply lookup_take_Some in Hj as [Hj Hjlt].
      have Hple : (uint.Z (cell_clock y) <= uint.Z (cell_clock cw))%Z.
      { destruct (decide (j = kw)) as [-> | Hne].
        - rewrite Hkw in Hj. injection Hj as <-. lia.
        - exact (StronglySorted_lookup_le cell_le (client_run types kc) j kw y cw (client_run_sorted types kc) Hj Hkw ltac:(clear -Hjlt Hne; lia)). }
      rewrite /cell_pr /= Hccr_clock. clear -Hple Hopos. lia. }
    have Haft : forall y, y ∈ drop (kw + 1) (client_run types (cell_client cr)) -> ((cell_pr cr).1 < (cell_pr y).1)%Z.
    { move=> y Hy.
      rewrite Hcccr Hcwcc in Hy.
      apply list_elem_of_lookup_1 in Hy as [j Hj].
      rewrite lookup_drop in Hj.
      have HyCR : y ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hj.
      have Hyall : y ∈ all_cells types := proj1 (proj1 (client_run_mem types kc y) HyCR).
      have Hycc : cell_client y = cell_client cw.
      { rewrite (proj2 (proj1 (client_run_mem types kc y) HyCR)) Hcwcc //. }
      have Hyne : y ≠ cw.
      { move=> Heq. rewrite Heq in Hj.
        have := NoDup_lookup _ _ _ _ Hndrun Hkw Hj. clear -k. lia. }
      have Hylocne : y.(ic_loc) ≠ cw.(ic_loc).
      { move=> Heq. apply Hyne. exact (Hinj y cw HyCR (list_elem_of_lookup_2 _ _ _ Hkw) Heq). }
      have Hle : (uint.Z (cell_clock cw) <= uint.Z (cell_clock y))%Z.
      { exact (StronglySorted_lookup_le cell_le (client_run types kc) kw (kw + 1 + j) cw y (client_run_sorted types kc) Hkw Hj ltac:(clear -k; lia)). }
      rewrite /cell_pr /= Hccr_clock.
      destruct (Hdisj y Hyall Hycc Hylocne) as [Hd | Hd].
      - exfalso.
        have Hyeq : uint.Z (cell_clock y) = uint.Z (cell_clock cw) by (clear -Hd Hle; lia).
        apply Hylocne. apply (Hclkloc y cw Hyall Hcwmem Hycc).
        rewrite /cell_pr /=. exact Hyeq.
      - clear -Hd Hoinrun. lia. }
    have Hrun_eq := client_run_loc_insert types (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) cr (kw + 1) Hkp Hclkloc Hbef Haft.
    rewrite Hcccr Hcwcc Hcrloc in Hrun_eq.
    iEval (rewrite -Hrun_eq) in "HnewNodes".
    (* re-establish the own_item_map side conditions over types2 *)
    have HinjAll : forall x y, x ∈ all_cells types -> y ∈ all_cells types -> x.(ic_loc) = y.(ic_loc) -> x = y.
    { move=> x y Hx Hy Hxy.
      apply list_elem_of_lookup_1 in Hx as [ix Hix]. apply list_elem_of_lookup_1 in Hy as [iy Hiy].
      have Hlix : (ic_loc <$> all_cells types) !! ix = Some (y.(ic_loc)) by (rewrite list_lookup_fmap Hix /= Hxy //).
      have Hliy : (ic_loc <$> all_cells types) !! iy = Some (y.(ic_loc)) by (rewrite list_lookup_fmap Hiy //).
      have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnodup Hlix Hliy.
      congruence. }
    have Hdecomp : forall c0, c0 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> c0 ∈ all_cells types \/ c0 = cl \/ c0 = cr.
    { move=> c0 Hc0.
      have Hp := all_cells_insert types parent {| ty_cells := cells; ty_arr := arr |} {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Htypes.
      rewrite Hp /= Hsc in Hc0.
      apply elem_of_app in Hc0 as [Hc0 | Hc0].
      - apply elem_of_app in Hc0 as [Hc0 | Hc0].
        + left. apply all_cells_elem_of. exists parent, {| ty_cells := cells; ty_arr := arr |}.
          split; [exact Htypes |]. simpl. rewrite -Hsplit. apply elem_of_app. by left.
        + apply elem_of_cons in Hc0 as [-> | Hc0]; [by right; left |].
          apply elem_of_cons in Hc0 as [-> | Hc0]; [by right; right |].
          left. apply all_cells_elem_of. exists parent, {| ty_cells := cells; ty_arr := arr |}.
          split; [exact Htypes |]. simpl. rewrite -Hsplit. apply elem_of_app. right.
          apply elem_of_cons. by right.
      - left.
        have Hq := all_cells_lookup types parent {| ty_cells := cells; ty_arr := arr |} Htypes.
        rewrite Hq /=. apply elem_of_app. by right. }
    have Hcomplete2 : forall c0 : w64, c0 ∈ cell_client <$> all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> is_Some (<[kc := newSl]> gm !! c0).
    { move=> c0 Hc0. apply list_elem_of_fmap in Hc0 as (cc & -> & Hcc0).
      destruct (Hdecomp cc Hcc0) as [Hin | [-> | ->]].
      - destruct (decide (cell_client cc = kc)) as [He | Hne].
        + rewrite He lookup_insert_eq. eauto.
        + rewrite lookup_insert_ne; [| congruence]. apply Hcomplete. apply list_elem_of_fmap_2. exact Hin.
      - rewrite Hcccl Hcwcc lookup_insert_eq. eauto.
      - rewrite Hcccr Hcwcc lookup_insert_eq. eauto. }
    have HF2 : forall c, c ∈ all_cells types -> cell_client c = cell_client cw -> (cell_pr c).1 = (cell_pr cr).1 -> False.
    { move=> c Hc Hcc Hpr.
      rewrite /cell_pr /= Hccr_clock in Hpr.
      destruct (decide (c.(ic_loc) = cw.(ic_loc))) as [He | Hne].
      - have Heq : c = cw := HinjAll c cw Hc Hcwmem He.
        rewrite Heq in Hpr. clear -Hpr Hopos. lia.
      - destruct (Hdisj c Hc Hcc Hne) as [Hd | Hd].
        + clear -Hd Hpr Hopos. lia.
        + clear -Hd Hpr Hoinrun. lia. }
    have Hprcl : (cell_pr cl).1 = (cell_pr cw).1 by (rewrite /cell_pr /= Hclcl //).
    have Hclkloc2 : forall c1 c2, c1 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> c2 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> cell_client c1 = cell_client c2 -> (cell_pr c1).1 = (cell_pr c2).1 -> c1.(ic_loc) = c2.(ic_loc).
    { move=> c1 c2 Hc1 Hc2 Hcc Hpr.
      destruct (Hdecomp c1 Hc1) as [Hin1 | [-> | ->]]; destruct (Hdecomp c2 Hc2) as [Hin2 | [-> | ->]].
      - exact (Hclkloc c1 c2 Hin1 Hin2 Hcc Hpr).
      - rewrite Hclloc.
        apply (Hclkloc c1 cw Hin1 Hcwmem); [rewrite Hcc Hcccl // | rewrite Hpr Hprcl //].
      - exfalso. apply (HF2 c1 Hin1); [rewrite Hcc Hcccr // | exact Hpr].
      - rewrite Hclloc. symmetry.
        apply (Hclkloc c2 cw Hin2 Hcwmem); [rewrite -Hcc Hcccl // | rewrite -Hpr Hprcl //].
      - reflexivity.
      - exfalso. rewrite /cell_pr /= Hclcl Hccr_clock in Hpr. clear -Hpr Hopos. lia.
      - exfalso. apply (HF2 c2 Hin2); [rewrite -Hcc Hcccr // | rewrite -Hpr //].
      - exfalso. rewrite /cell_pr /= Hclcl Hccr_clock in Hpr. clear -Hpr Hopos. lia.
      - reflexivity. }
    iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
    iAssert (own_item_map mref (DfracOwn 1) (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types)) with "[Hmap HnewNodes HnewCap Hruns]" as "Hitemmap2".
    { iExists (<[kc := newSl]> gm). iFrame "Hmap".
      iSplitL "HnewNodes HnewCap Hruns".
      - rewrite big_sepM_insert_delete. iSplitL "HnewNodes HnewCap"; [iFrame |].
        iDestruct (big_sepM_delete _ _ kc slk Hslk with "Hruns") as "[_ Hrest2]".
        iApply (big_sepM_impl with "Hrest2").
        iIntros "!#" (client s0 Hcs) "H". iNamed "H".
        have Hne2 : client ≠ cell_client cr.
        { rewrite Hcccr Hcwcc. move=> Heqc. rewrite Heqc lookup_delete_eq in Hcs. discriminate. }
        rewrite (client_run_loc_other types (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) cr client Hkp Hclkloc Hne2). iFrame.
      - iPureIntro. split; [exact Hcomplete2 | exact Hclkloc2]. }
    wp_auto.
    iApply ("HΦ" $! rs).
    iFrame "Hitemsf Hitemmap2 Htypes2".
    iPureIntro. exact Hrsnn.
Qed.

(** [store.splitAtAndGetLeft] / [store.splitAtAndGetRight], unit fast path
    (issue #28 M2): with every run 1-char (the M1 all-singleton invariant) the
    found node already ends (resp. starts) at the requested id — the offset is
    0 and [Len() - 1] is 0 — so the split branch is dead and each helper
    coincides with [GetNode]. The general (actually splitting) specs arrive
    with the run-integrate milestone (M4), where runs become reachable. *)
Lemma wp_store__splitAtAndGetLeft (s mref : loc) (dq : dfrac) (idv : yjs.id.t)
    (types : gmap loc type_state) (cw : item_cell) :
  cw ∈ all_cells types ->
  item_id (run_head cw) = toYjsId idv ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetLeft" #idv
  {{{ RET (#(ic_loc cw), #true);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}.
Proof using Type*.
  move=> Hcw Hcwid Hnowrap.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_store__GetNode s mref dq idv types cw Hcw Hcwid Hnowrap
              with "[$Hitemsf $Hitemmap $Htypes]").
  iIntros "(Hitemsf & Hitemmap & Htypes)".
  wp_auto.
  iDestruct (types_cell_acc types cw Hcw with "Htypes") as "Hacc".
  iNamed "Hacc".
  have Hclkeq : iv.(yjs.item.id').(yjs.id.clock') = idv.(yjs.id.clock').
  { have Heq : toYjsId iv.(yjs.item.id') = toYjsId idv by rewrite -Hid Hcwid //.
    injection Heq => Hclk Hcli. word. }
  wp_auto.
  wp_apply (wp_item__Len (ic_loc cw) (DfracOwn 1) iv with "[$Hval]"). iIntros "Hval".
  rewrite Hrun Hclkeq.
  wp_auto.
  (* the offset is clock - clock = 0 and Len() - 1 = 0: goose destructs the
     [!=] through the underlying equality, so the FIRST goal is the equal
     (no-split) return path and the SECOND the dead split branch *)
  wp_if_destruct.
  2: exfalso; word.
  iDestruct ("Hback" with "Hval") as "Htypes".
  iApply "HΦ". iFrame "Hitemsf Hitemmap Htypes".
Qed.

Lemma wp_store__splitAtAndGetRight (s mref : loc) (dq : dfrac) (idv : yjs.id.t)
    (types : gmap loc type_state) (cw : item_cell) :
  cw ∈ all_cells types ->
  item_id (run_head cw) = toYjsId idv ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetRight" #idv
  {{{ RET (#(ic_loc cw), #true);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}.
Proof using Type*.
  move=> Hcw Hcwid Hnowrap.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_store__GetNode s mref dq idv types cw Hcw Hcwid Hnowrap
              with "[$Hitemsf $Hitemmap $Htypes]").
  iIntros "(Hitemsf & Hitemmap & Htypes)".
  wp_auto.
  iDestruct (types_cell_acc types cw Hcw with "Htypes") as "Hacc".
  iNamed "Hacc".
  have Hclkeq : iv.(yjs.item.id').(yjs.id.clock') = idv.(yjs.id.clock').
  { have Heq : toYjsId iv.(yjs.item.id') = toYjsId idv by rewrite -Hid Hcwid //.
    injection Heq => Hclk Hcli. word. }
  wp_auto.
  rewrite Hclkeq.
  (* offset = clock - clock = 0: the split branch is dead *)
  wp_if_destruct.
  1: exfalso; word.
  iDestruct ("Hback" with "Hval") as "Htypes".
  iApply "HΦ". iFrame "Hitemsf Hitemmap Htypes".
Qed.

(** [store.getOrCreateYType], lookup-hit case: the name is already bound in
    the registry, so the creation branch is dead and the bound type comes
    back. This is the only case the verified update path needs — see
    [wp_store__applyUpdate]'s bound-names precondition (the on-the-fly type
    creation of y-octo's update path is outside the verified subset for now:
    it would grow [types]/[bind]/[m] with a fresh empty type mid-batch). *)
Lemma wp_store__getOrCreateYType (s tref : loc) (dq : dfrac) (bind : gmap P loc)
    (nm : go_string) (p : loc) :
  bind !! nm = Some p ->
  {{{ is_pkg_init yjs ∗ (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref dq bind }}}
    s @! (go.PointerType yjs.store) @! "getOrCreateYType" #nm
  {{{ RET #p; (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref dq bind }}}.
Proof using Type*.
  move=> Hp.
  iIntros (Φ) "(#Hpkg & Htypesf & Hmap) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Hmap"). iIntros "Hmap".
  rewrite Hp /=.
  wp_auto.
  iApply "HΦ". iFrame "Htypesf Hmap".
Qed.

(** [store.repair]: resolve a fresh decoded item's origin pointers (store-wide
    [GetNode]) and its parent ([getOrCreateYType] for Parent::String, the
    left/right neighbour's own parent for Parent::None). Specified against
    caller-supplied witness cells [ocL]/[ocR] (present exactly when the
    corresponding origin id is, and carrying it — on the verified update path
    these come from the [ValidReplay]'s [toItem] resolution, so they live in
    the TARGET type's DLL and their [ic_parent] IS the target type, making the
    borrow land on [p_t]). The fresh item [own_linked_item _ _ null null null]
    comes back linked: [own_linked_item _ _ p_t lft rgt] with the neighbours'
    node locations. *)
Lemma wp_store__repair (s mref tref item_l pname : loc) (dq : dfrac)
    (input : IntegrateInput (A := A)) (opn : option go_string)
    (types : gmap loc type_state) (bind : gmap P loc)
    (ocL ocR : option item_cell) (p_t : loc) :
  match in_originId input, ocL with
  | Some oid, Some c => c ∈ all_cells types /\ item_id (run_head c) = oid
  | None, None => True
  | _, _ => False
  end ->
  match in_rightOriginId input, ocR with
  | Some oid, Some c => c ∈ all_cells types /\ item_id (run_head c) = oid
  | None, None => True
  | _, _ => False
  end ->
  match opn with
  | Some nm => bind !! nm = Some p_t
  | None => match ocL with
            | Some c => p_t = ic_parent c
            | None => match ocR with
                      | Some c => p_t = ic_parent c
                      | None => False
                      end
            end
  end ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗
      own_linked_item item_l input null null null ∗
      is_parent_name pname opn ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref dq bind ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "repair" #item_l #pname
  {{{ RET #();
      own_linked_item item_l input p_t
        (match ocL with Some c => ic_loc c | None => null end)
        (match ocR with Some c => ic_loc c | None => null end) ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref dq bind ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}.
Proof using Type*.
  move=> HwL HwR Hwpar Hnowrap.
  iIntros (Φ) "(#Hpkg & Hlinked & #HisPN & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes) HΦ".
  iDestruct "Hlinked" as (iv oleft oright) "(Hraw & %Hfl & %Hfr & %Hfpar & %Hflags & %Hrun)".
  iNamed "Hraw".
  wp_method_call. wp_call. wp_call. wp_auto.
  destruct oleft as [idvL|].
  - (* left origin present: GetNode resolves it *)
    have HinlS : input.(in_originId) = Some (toYjsId idvL) by rewrite -Hin_l //.
    rewrite HinlS in HwL. destruct ocL as [cL|]; last done.
    destruct HwL as [HcLmem HcLid].
    iDestruct "Holeft" as "[%HnnL #HolC]".
    rewrite (bool_decide_eq_false_2 (iv.(yjs.item.originLeftId') = null) HnnL) /=.
    wp_auto.
    wp_apply (wp_store__splitAtAndGetLeft s mref dq idvL types cL HcLmem (eq_trans HcLid eq_refl) Hnowrap
                with "[$Hitemsf $Hitemmap $Htypes]").
    iIntros "(Hitemsf & Hitemmap & Htypes)".
    wp_auto.
    destruct oright as [idvR|].
    + (* right origin present *)
      have HinrS : input.(in_rightOriginId) = Some (toYjsId idvR) by rewrite -Hin_r //.
      rewrite HinrS in HwR. destruct ocR as [cR|]; last done.
      destruct HwR as [HcRmem HcRid].
      iDestruct "Horight" as "[%HnnR #HorC]".
      rewrite (bool_decide_eq_false_2 (iv.(yjs.item.originRightId') = null) HnnR) /=.
      wp_auto.
      wp_apply (wp_store__splitAtAndGetRight s mref dq idvR types cR HcRmem (eq_trans HcRid eq_refl) Hnowrap
                  with "[$Hitemsf $Hitemmap $Htypes]").
      iIntros "(Hitemsf & Hitemmap & Htypes)".
      wp_auto.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType s tref dq bind nm p_t Hwpar
                    with "[$Htypesf $Htypesmap]").
        iIntros "(Htypesf & Htypesmap)".
        wp_auto.
        iApply "HΦ".
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iExists _, (Some idvL), (Some idvR).
        rewrite /own_fresh_item_raw. simpl.
        iFrame "Hitem". iFrame "HolC HorC".
        iPureIntro. split_and!; try done.
      * (* Parent::None: borrow from the resolved left neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        iDestruct (types_cell_acc types cL HcLmem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCL.
        wp_auto.
        rewrite (bool_decide_eq_false_2 (cL.(ic_loc) = null) HnnCL) /=.
        wp_auto.
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar Hwpar.
        iApply "HΦ".
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iExists _, (Some idvL), (Some idvR).
        rewrite /own_fresh_item_raw. simpl.
        iFrame "Hitem". iFrame "HolC HorC".
        iPureIntro. split_and!; try done.
    + (* no right origin *)
      have HinrN : input.(in_rightOriginId) = None by rewrite -Hin_r //.
      rewrite HinrN in HwR. destruct ocR as [cR|]; first done.
      iDestruct "Horight" as "%HnR".
      rewrite (bool_decide_eq_true_2 (iv.(yjs.item.originRightId') = null) HnR) /=.
      wp_auto.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType s tref dq bind nm p_t Hwpar
                    with "[$Htypesf $Htypesmap]").
        iIntros "(Htypesf & Htypesmap)".
        wp_auto.
        iApply "HΦ".
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iExists _, (Some idvL), None.
        rewrite /own_fresh_item_raw. simpl.
        iFrame "Hitem". iFrame "HolC".
        iPureIntro. split_and!; try done.
      * (* Parent::None: borrow from the resolved left neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        iDestruct (types_cell_acc types cL HcLmem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCL.
        wp_auto.
        rewrite (bool_decide_eq_false_2 (cL.(ic_loc) = null) HnnCL) /=.
        wp_auto.
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar Hwpar.
        iApply "HΦ".
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iExists _, (Some idvL), None.
        rewrite /own_fresh_item_raw. simpl.
        iFrame "Hitem". iFrame "HolC".
        iPureIntro. split_and!; try done.
  - (* no left origin *)
    have HinlN : input.(in_originId) = None by rewrite -Hin_l //.
    rewrite HinlN in HwL. destruct ocL as [cL|]; first done.
    iDestruct "Holeft" as "%HnL".
    rewrite (bool_decide_eq_true_2 (iv.(yjs.item.originLeftId') = null) HnL) /=.
    wp_auto.
    destruct oright as [idvR|].
    + (* right origin present *)
      have HinrS : input.(in_rightOriginId) = Some (toYjsId idvR) by rewrite -Hin_r //.
      rewrite HinrS in HwR. destruct ocR as [cR|]; last done.
      destruct HwR as [HcRmem HcRid].
      iDestruct "Horight" as "[%HnnR #HorC]".
      rewrite (bool_decide_eq_false_2 (iv.(yjs.item.originRightId') = null) HnnR) /=.
      wp_auto.
      wp_apply (wp_store__splitAtAndGetRight s mref dq idvR types cR HcRmem (eq_trans HcRid eq_refl) Hnowrap
                  with "[$Hitemsf $Hitemmap $Htypes]").
      iIntros "(Hitemsf & Hitemmap & Htypes)".
      wp_auto.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType s tref dq bind nm p_t Hwpar
                    with "[$Htypesf $Htypesmap]").
        iIntros "(Htypesf & Htypesmap)".
        wp_auto.
        iApply "HΦ".
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iExists _, None, (Some idvR).
        rewrite /own_fresh_item_raw. simpl.
        iFrame "Hitem". iFrame "HorC".
        iPureIntro. split_and!; try done.
      * (* Parent::None: borrow from the resolved right neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        have Hfl' : (iv <| yjs.item.right' := cR.(ic_loc) |>).(yjs.item.left') = null
          by simpl; exact Hfl.
        iDestruct (types_cell_acc types cR HcRmem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCR.
        wp_auto.
        rewrite (bool_decide_eq_true_2 _ Hfl') /=.
        wp_auto.
        rewrite (bool_decide_eq_false_2 (cR.(ic_loc) = null) HnnCR) /=.
        wp_auto.
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar Hwpar.
        iApply "HΦ".
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iExists _, None, (Some idvR).
        rewrite /own_fresh_item_raw. simpl.
        iFrame "Hitem". iFrame "HorC".
        iPureIntro. split_and!; try done.
    + (* no origins at all: [is_update_item]'s Hborrow rules Parent::None out *)
      have HinrN : input.(in_rightOriginId) = None by rewrite -Hin_r //.
      rewrite HinrN in HwR. destruct ocR as [cR|]; first done.
      iDestruct "Horight" as "%HnR".
      rewrite (bool_decide_eq_true_2 (iv.(yjs.item.originRightId') = null) HnR) /=.
      wp_auto.
      destruct opn as [nm|]; last done.
      iDestruct "HisPN" as "[%HnnP #HpnC]".
      rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
      wp_auto.
      wp_apply (wp_store__getOrCreateYType s tref dq bind nm p_t Hwpar
                  with "[$Htypesf $Htypesmap]").
      iIntros "(Htypesf & Htypesmap)".
      wp_auto.
      iApply "HΦ".
      iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
      iExists _, None, None.
      rewrite /own_fresh_item_raw. simpl.
      iFrame "Hitem".
      iPureIntro. split_and!; try done.
Qed.

(* ===== applyUpdate (doc-level, #49) ====================================== *)

(** Both origin indices of a successful [integrate], off its bind chain. *)
Lemma integrate_finds (input : IntegrateInput (A := A)) (arr arr2 : list (YjsItem A)) :
  integrate input arr = Some arr2 ->
  ∃ leftIdx rightIdx, findLeftIdx (in_originId input) arr = Some leftIdx /\
                      findRightIdx (in_rightOriginId input) arr = Some rightIdx.
Proof.
  rewrite /integrate.
  move=> /bind_Some [leftIdx [HfindLeft Hr1]].
  move: Hr1 => /bind_Some [rightIdx [HfindRight Hr2]].
  by exists leftIdx, rightIdx.
Qed.

(** A present origin's [find*Idx] hit names the origin item's exact index. *)
Lemma findLeftIdx_inv (oid : YjsId) (arr : list (YjsItem A)) (k : Z) :
  findLeftIdx (Some oid) arr = Some k ->
  ∃ (kn : nat) (it : YjsItem A), k = Z.of_nat kn /\ arr !! kn = Some it /\ item_id it = oid.
Proof.
  rewrite /findLeftIdx.
  destruct (list_find (fun item => item_id item = oid) arr) as [[kn it]|] eqn:Hf; last done.
  simpl. move=> [= <-]. apply list_find_Some in Hf. destruct Hf as (Hlk & Hidf & _).
  by exists kn, it.
Qed.

Lemma findRightIdx_inv (oid : YjsId) (arr : list (YjsItem A)) (k : Z) :
  findRightIdx (Some oid) arr = Some k ->
  ∃ (kn : nat) (it : YjsItem A), k = Z.of_nat kn /\ arr !! kn = Some it /\ item_id it = oid.
Proof.
  rewrite /findRightIdx.
  destruct (list_find (fun item => item_id item = oid) arr) as [[kn it]|] eqn:Hf; last done.
  simpl. move=> [= <-]. apply list_find_Some in Hf. destruct Hf as (Hlk & Hidf & _).
  by exists kn, it.
Qed.

(** One entry's [own_ytype_cells] pures, read off the big-sep (which the
    conclusion being pure lets the caller keep). *)
Lemma types_entry_pures (types : gmap loc type_state) (p : loc) (ts : type_state) :
  types !! p = Some ts ->
  ([∗ map] parent ↦ ts0 ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts0) (ty_arr ts0) ∗
      ⌜YjsArrInvariant (ty_arr ts0)⌝ ∗
      ⌜Forall cell_unit (ty_cells ts0)⌝) -∗
  ⌜cells_repr (ty_arr ts) (ty_cells ts) (ty_arr ts) ∧
   (∀ c, c ∈ ty_cells ts -> ic_parent c = p) ∧
   Forall cell_unit (ty_cells ts)⌝.
Proof.
  move=> Hp. iIntros "Htypes".
  iDestruct (big_sepM_lookup_acc _ _ p ts Hp with "Htypes") as "[(Hyt & _ & %Hunitp) _]".
  iDestruct "Hyt" as (yt tl) "(_ & _ & %Hlen & %Hrepr & %Hcpar)".
  iPureIntro. by split_and!.
Qed.

Lemma types_repr_all (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
      ⌜Forall cell_unit (ty_cells ts)⌝) -∗
  ⌜∀ p ts, types !! p = Some ts -> cells_repr (ty_arr ts) (ty_cells ts) (ty_arr ts)⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types,
      ⌜cells_repr (ty_arr ts) (ty_cells ts) (ty_arr ts)⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "[Hyt _]".
    iDestruct "Hyt" as (yt tl) "(_ & _ & %Hlen & %Hrepr & %Hcpar)".
    by iPureIntro. }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> p ts Hp. exact (Hall p ts Hp).
Qed.

(** [store_inv] is exactly [own_store] with the model existentially closed.
    The forward direction restates the per-client counter clause at the
    model; the backward direction re-derives the [types]-level and the W64
    cell-level counter bounds from the model-level one, via the registry
    coherence and the DLL id-bound pins. A lock-holding caller uses this to
    trade the lock body for [own_store] (feeding a store-state spec such as
    [wp_store__applyUpdate_certs]) and back. *)
Lemma store_inv_own_store (s_loc : loc) (γs : store_names) (γh : history_names) :
  store_inv s_loc γs γh ⊣⊢
  ∃ (c : ClientId) (h : list Ev) (m : DocM)
    (pend : list (TId * IntegrateInput (A := A))),
    own_store s_loc γs γh c h m pend.
Proof.
  iSplit.
  - iIntros "H". iNamed "H". iNamed "Hexcl". iNamed "Hro".
    iExists (uint.nat client), h, m, pend.
    iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind.
    iFrame "∗#".
    iPureIntro. split_and!.
    + reflexivity.
    + exact Hpendbnd.
    + rewrite /doc_registry_coh. split_and!; assumption.
    + exact Hhcoh.
    + (* the model-level counter from the [types]-level one *)
      move=> t x Hx Hcx.
      have Hne : docm_get m t ≠ [].
      { move=> Heq. move: Hx. rewrite Heq elem_of_nil. done. }
      destruct (Hmdom t Hne) as (nm & p & -> & Hbnm).
      destruct (Hbindtypes nm p Hbnm) as [ts Hts].
      have Hdg : docm_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
      rewrite Hdg in Hx.
      exact (Hctr p ts x Hts Hx Hcx).
    + exact Hlocdup.
    + exact Hrangedisj.
  - iIntros "H". iDestruct "H" as (c h m pend) "H". iNamed "H". subst c.
    iDestruct (types_repr_all with "Htypes") as %Hreprall.
    iDestruct (types_unit_all with "Htypes") as %Hunitall.
    iDestruct (types_cells_id_bounds with "Htypes") as %Hcellbnd.
    destruct Hregcoh as (Hbindtypes & Hbindinj & Htypesbound & Hmtypes & Hmdom).
    (* the [types]-level counter from the model-level one *)
    have Hctrt : ∀ parent ts x, types !! parent = Some ts -> x ∈ ty_arr ts ->
        clientId (item_id x) = uint.nat client -> (clock (item_id x) < uint.nat k)%nat.
    { move=> parent ts x Hts Hx Hcx.
      destruct (Htypesbound parent (ex_intro _ ts Hts)) as [nm Hbnm].
      have Hdg : docm_get m (RootId nm) = ty_arr ts := Hmtypes nm parent ts Hbnm Hts.
      apply (Hctr (RootId nm) x); [by rewrite Hdg | exact Hcx]. }
    (* the W64 cell-level shadow, via the id-bound pins *)
    have Hcellctr : ∀ c0, c0 ∈ all_cells types -> cell_client c0 = client ->
        (uint.Z (cell_clock c0) < uint.Z k)%Z.
    { move=> c0 Hc0 Hcc.
      have Hc0m := Hc0. apply all_cells_elem_of in Hc0m.
      destruct Hc0m as (p & ts & Hts & Hcts).
      have Hitemmem : run_head c0 ∈ ty_arr ts.
      { rewrite (Hreprall p ts Hts).
        apply run_head_in_flatten; [exact Hcts |].
        exact (proj1 (Forall_forall _ _) (Hunitall p ts Hts) _ Hcts). }
      have [Hcb Hkb] := Hcellbnd c0 Hc0.
      have Hceq : clientId (item_id (run_head c0)) = uint.nat client.
      { move: Hcc. rewrite /cell_client. move=> Hcc.
        have Hz : uint.Z (W64 (clientId (item_id (run_head c0)))) = uint.Z client
          by rewrite Hcc.
        word. }
      have Hlt := Hctrt p ts (run_head c0) Hts Hitemmem Hceq.
      rewrite /cell_clock. word. }
    iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind, h, m, pend.
    iSplitR "Hseq Htypes"; last by iFrame "Hseq Htypes".
    iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hpendcert Hpendroot HtypesAuth Hbinds Hhist".
    iPureIntro. split_and!;
      [exact Hpendbnd | exact Hctrt | exact Hcellctr | exact Hlocdup | exact Hrangedisj
      | exact Hbindtypes | exact Hbindinj
      | exact Htypesbound | exact Hhcoh | exact Hmtypes | exact Hmdom].
Qed.

(* ===== #40 gate toolkit (getNodeIndex/GetNode total, hasNode) ===== *)
Lemma wp_getNodeIndex_total (sl : slice.t) (dq : dfrac) (types : gmap loc type_state)
    (run : list item_cell) (clk : w64) :
  StronglySorted cell_le run ->
  (∀ c, c ∈ run -> c ∈ all_cells types) ->
  (∀ c, c ∈ run -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ sl ↦*{dq} (ic_loc <$> run) ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}
    @! yjs.getNodeIndex #sl #clk
  {{{ (i : w64) (ok : bool), RET (#i, #ok);
      sl ↦*{dq} (ic_loc <$> run) ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) ∗
      ⌜if ok then ∃ c, run !! uint.nat i = Some c ∧ cell_clock c = clk
       else ∀ (k : nat) (c : item_cell), run !! k = Some c -> cell_clock c ≠ clk⌝ }}}.
Proof using Type*.
  move=> Hsort Hmem Hnowrap.
  wp_start as "(Hsl & Htypes)".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  rewrite length_fmap in Hsllen Hsllen0.
  wp_auto.
  iAssert (∃ (lo hi : w64),
    "Hleft" ∷ left_ptr ↦ lo ∗ "Hright" ∷ right_ptr ↦ hi ∗
    "Hnodes" ∷ nodes_ptr ↦ sl ∗ "Hclock" ∷ clock_ptr ↦ clk ∗
    "Hsl" ∷ sl ↦*{dq} (ic_loc <$> run) ∗
    "Htypes" ∷ ([∗ map] parent ↦ ts ∈ types,
        own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
        ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
        ⌜Forall cell_unit (ty_cells ts)⌝) ∗
    "%Hbnd" ∷ ⌜(0 <= uint.Z lo /\ uint.Z hi <= Z.of_nat (length run))%Z⌝ ∗
    "%Hwin" ∷ ⌜∀ (k : nat) (c : item_cell), run !! k = Some c -> cell_clock c = clk ->
                (uint.Z lo <= Z.of_nat k < uint.Z hi)%Z⌝)%I
    with "[left right nodes clock Hsl Htypes]" as "IH".
  { iExists (W64 0), sl.(slice.len).
    iFrame "left right nodes clock Hsl Htypes".
    iPureIntro. split; [word |].
    move=> k c Hk Hc. have Hklt := lookup_lt_Some _ _ _ Hk. word. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - (* probe the middle *)
    set (mid := word.add lo (word.divu (word.sub hi lo) (W64 2))).
    have Hmid : (uint.Z lo <= uint.Z mid < uint.Z hi)%Z.
    { rewrite /mid. destruct Hbnd as [Hb1 Hb2]. word. }
    wp_auto.
    rewrite decide_True; last word.
    have Hmidlt : (uint.nat mid < length run)%nat by word.
    destruct (run !! uint.nat mid) as [cmid|] eqn:Hcmid;
      last by (apply lookup_ge_None in Hcmid; lia).
    have Hlocmid : (ic_loc <$> run) !! uint.nat mid = Some cmid.(ic_loc)
      by rewrite list_lookup_fmap Hcmid //.
    iDestruct (own_slice_elem_acc (sint.Z mid) (ic_loc cmid) sl dq (ic_loc <$> run) with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z mid)) with (uint.nat mid) by word. exact Hlocmid. }
    wp_auto.
    iDestruct ("Hgive" $! cmid.(ic_loc) with "Hel") as "Hsl".
    have Hinsid : (<[sint.nat mid := cmid.(ic_loc)]> (ic_loc <$> run)) = (ic_loc <$> run).
    { apply list_insert_id. replace (sint.nat mid) with (uint.nat mid) by word. exact Hlocmid. }
    iEval (rewrite Hinsid) in "Hsl".
    have Hcmemall : cmid ∈ all_cells types
      by (apply Hmem; exact (list_elem_of_lookup_2 _ _ _ Hcmid)).
    iDestruct (types_cell_acc types cmid Hcmemall with "Htypes") as "Hacc".
    iNamed "Hacc".
    wp_auto.
    have Hmcv : cell_clock cmid = iv.(yjs.item.id').(yjs.id.clock')
      by (rewrite /cell_clock Hid /toYjsId /=; word).
    wp_apply (wp_item__Len cmid.(ic_loc) (DfracOwn 1) iv with "[$Hval]"). iIntros "Hval".
    rewrite Hrun.
    iDestruct ("Hback" with "Hval") as "Htypes".
    wp_auto.
    destruct (bool_decide (uint.Z clk < uint.Z iv.(yjs.item.id').(yjs.id.clock'))) eqn:Hcmp1.
    + (* clk < middleClock: shrink [right] to [mid] *)
      apply bool_decide_eq_true_1 in Hcmp1.
      wp_auto. wp_for_post.
      iFrame "HΦ". iExists lo, mid.
      iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
      iPureIntro. split.
      { lia. }
      move=> k c Hk Hc.
      have [Hlo Hhi] := Hwin k c Hk Hc.
      split; [exact Hlo |].
      destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
      * lia.
      * exfalso. subst k. rewrite Hcmid in Hk. injection Hk as <-.
        rewrite -Hmcv Hc in Hcmp1. lia.
      * exfalso.
        have Hle := StronglySorted_lookup_le cell_le run (uint.nat mid) k cmid c Hsort Hcmid Hk Hgt.
        rewrite /cell_le Hc Hmcv in Hle. lia.
    + (* clk >= middleClock *)
      apply bool_decide_eq_false_1 in Hcmp1.
      have Hnw : (uint.Z (cell_clock cmid) + 1 < 2^64)%Z
        by (apply Hnowrap; exact (list_elem_of_lookup_2 _ _ _ Hcmid)).
      rewrite Hmcv in Hnw.
      wp_auto.
      case_bool_decide as Hcmp2.
      * (* clk >= middleEnd: move [left] past [mid] *)
        have Hgtm : (uint.Z iv.(yjs.item.id').(yjs.id.clock') < uint.Z clk)%Z by word.
        wp_auto. wp_for_post.
        iFrame "HΦ". iExists (word.add mid (W64 1)), hi.
        iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
        iPureIntro. split.
        { word. }
        move=> k c Hk Hc.
        have [Hlo Hhi] := Hwin k c Hk Hc.
        split; [| exact Hhi].
        destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
        { exfalso.
          have Hle := StronglySorted_lookup_le cell_le run k (uint.nat mid) c cmid Hsort Hk Hcmid Hlt.
          rewrite /cell_le Hc Hmcv in Hle. lia. }
        { exfalso. subst k. rewrite Hcmid in Hk. injection Hk as <-.
          rewrite -Hmcv Hc in Hgtm. lia. }
        word.
      * (* middleClock <= clk < middleClock + 1: the probe hit *)
        have Hclkeq : cell_clock cmid = clk by (apply word.unsigned_inj; rewrite Hmcv; word).
        wp_auto. wp_for_post.
        iApply ("HΦ" $! mid true). iFrame "Hsl Htypes".
        iPureIntro. exists cmid. split; [exact Hcmid | exact Hclkeq].
  - (* the window is empty: no run cell carries [clk] *)
    wp_auto.
    iApply ("HΦ" $! (W64 0) false). iFrame "Hsl Htypes".
    iPureIntro. move=> k c Hk Hc.
    have := Hwin k c Hk Hc. lia.
Qed.

(** [store.GetNode], TOTAL (issue #40): the pending gate probes ids that may
    be absent, so both miss paths (unknown client, clock not covered) are live.
    [ok = true] pins the returned loc to a store cell carrying the probed id;
    [ok = false] certifies no store cell carries it. *)
Lemma wp_store__GetNode_total (s mref : loc) (dq : dfrac) (idv : yjs.id.t)
    (types : gmap loc type_state) :
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "GetNode" #idv
  {{{ (l : loc) (ok : bool), RET (#l, #ok);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) ∗
      ⌜if ok
       then ∃ c, c ∈ all_cells types ∧ item_id (run_head c) = toYjsId idv ∧
                 ic_loc c = l
       else ∀ c, c ∈ all_cells types -> item_id (run_head c) ≠ toYjsId idv⌝ }}}.
Proof using Type*.
  move=> Hnowrap.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  set (kc := idv.(yjs.id.clientId')).
  iDestruct (types_cells_id_bounds with "Htypes") as %Hcellbnd.
  (* the id glue: a cell carries [toYjsId idv] iff its W64 components are
     [idv]'s *)
  have Hglue : ∀ c, c ∈ all_cells types ->
      (item_id (run_head c) = toYjsId idv <->
       cell_client c = kc ∧ cell_clock c = idv.(yjs.id.clock')).
  { move=> c Hc. have [Hab Hbb] := Hcellbnd c Hc. split.
    - move=> Hid. split.
      + rewrite /cell_client Hid /toYjsId /kc /=. word.
      + rewrite /cell_clock Hid /toYjsId /=. word.
    - move=> [Hcc Hck].
      move: Hcc Hck Hab Hbb. rewrite /cell_client /cell_clock /toYjsId.
      destruct (item_id (run_head c)) as [a b]. simpl.
      move=> Hcc Hck Hab Hbb. f_equal; word. }
  iNamed "Hitemmap".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Hmap"). iIntros "Hmap".
  destruct (gm !! kc) as [slk |] eqn:Hslk; rewrite Hslk /=.
  - (* known client: run the binary search *)
    wp_auto.
    iDestruct (big_sepM_lookup_acc _ _ kc slk Hslk with "Hruns") as "[Hrun Hrunsback]".
    iNamed "Hrun".
    wp_apply (wp_getNodeIndex_total slk dq types (client_run types kc) idv.(yjs.id.clock')
                (client_run_sorted types kc)
                (fun c Hc => proj1 (proj1 (client_run_mem types kc c) Hc))
                (fun c Hc => Hnowrap c (proj1 (proj1 (client_run_mem types kc c) Hc)))
                with "[$Hslice $Htypes]").
    iIntros (i ok) "(Hslice & Htypes & %Hires)".
    destruct ok.
    + (* hit *)
      destruct Hires as (cres & Hcres & Hcresclk).
      wp_auto.
      iDestruct (own_slice_len with "Hslice") as %[Hsllen Hsllen0].
      rewrite length_fmap in Hsllen Hsllen0.
      have Hilt : (uint.nat i < length (client_run types kc))%nat
        by (apply lookup_lt_Some in Hcres; lia).
      rewrite decide_True; last word.
      have Hlocres : (ic_loc <$> client_run types kc) !! uint.nat i = Some cres.(ic_loc)
        by rewrite list_lookup_fmap Hcres //.
      iDestruct (own_slice_elem_acc (sint.Z i) (ic_loc cres) slk dq (ic_loc <$> client_run types kc) with "Hslice") as "[Hel Hgive]".
      { word. }
      { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hlocres. }
      wp_auto.
      iDestruct ("Hgive" $! cres.(ic_loc) with "Hel") as "Hslice".
      have Hinsid : (<[sint.nat i := cres.(ic_loc)]> (ic_loc <$> client_run types kc)) = (ic_loc <$> client_run types kc).
      { apply list_insert_id. replace (sint.nat i) with (uint.nat i) by word. exact Hlocres. }
      iEval (rewrite Hinsid) in "Hslice".
      have Hcresmem : cres ∈ all_cells types /\ cell_client cres = kc.
      { apply client_run_mem. exact (list_elem_of_lookup_2 _ _ _ Hcres). }
      iApply ("HΦ" $! (ic_loc cres) true).
      iFrame "Hitemsf".
      iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
      iSplitL "Hmap Hruns".
      { iExists gm. iFrame "Hmap Hruns". iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
      iFrame "Htypes".
      iPureIntro. exists cres.
      split_and!; [exact (proj1 Hcresmem) | | done].
      apply (Hglue cres (proj1 Hcresmem)).
      split; [exact (proj2 Hcresmem) | exact Hcresclk].
    + (* clock miss within a known client *)
      wp_auto.
      iApply ("HΦ" $! null false).
      iFrame "Hitemsf".
      iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
      iSplitL "Hmap Hruns".
      { iExists gm. iFrame "Hmap Hruns". iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
      iFrame "Htypes".
      iPureIntro. move=> c Hc Hid.
      have [Hcc Hck] := proj1 (Hglue c Hc) Hid.
      have Hcrun : c ∈ client_run types kc by (apply client_run_mem; by split).
      apply list_elem_of_lookup_1 in Hcrun. destruct Hcrun as [kx Hkx].
      exact (Hires kx c Hkx Hck).
  - (* unknown client: no cell of this author at all *)
    wp_auto.
    iApply ("HΦ" $! null false).
    iFrame "Hitemsf".
    iSplitL "Hmap Hruns".
    { iExists gm. iFrame "Hmap Hruns". iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
    iFrame "Htypes".
    iPureIntro. move=> c Hc Hid.
    have [Hcc _] := proj1 (Hglue c Hc) Hid.
    have Hkcin : kc ∈ (cell_client <$> all_cells types).
    { rewrite -Hcc. apply list_elem_of_fmap_2. exact Hc. }
    destruct (Hcomplete kc Hkcin) as [slk Hslk'].
    rewrite Hslk in Hslk'. discriminate.
Qed.

(** [store.hasNode] (issue #40): the arrival test the pending gate runs. *)
Lemma wp_store__hasNode (s mref : loc) (dq : dfrac) (idv : yjs.id.t)
    (types : gmap loc type_state) :
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "hasNode" #idv
  {{{ (ok : bool), RET #ok;
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) ∗
      ⌜ok = true <-> ∃ c, c ∈ all_cells types ∧ item_id (run_head c) = toYjsId idv⌝ }}}.
Proof using Type*.
  move=> Hnowrap.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_store__GetNode_total s mref dq idv types Hnowrap
              with "[$Hitemsf $Hitemmap $Htypes]").
  iIntros (l ok) "(Hitemsf & Hitemmap & Htypes & %Hres)".
  wp_auto.
  iApply ("HΦ" $! ok).
  iFrame "Hitemsf Hitemmap Htypes".
  iPureIntro. destruct ok.
  - split; [| done]. move=> _.
    destruct Hres as (c & Hc & Hid & _). by exists c.
  - split; [done |]. move=> [c [Hc Hid]]. by destruct (Hres c Hc Hid).
Qed.

(** [store.splitAtAndGetLeft] / [store.splitAtAndGetRight], unit fast path
    (issue #28 M2): with every run 1-char (the M1 all-singleton invariant) the
    found node already ends (resp. starts) at the requested id — the offset is
    0 and [Len() - 1] is 0 — so the split branch is dead and each helper
    coincides with [GetNode]. The general (actually splitting) specs arrive
    with the run-integrate milestone (M4), where runs become reachable. *)

(* ===== #40 pending pool stack (issue #40) ===== *)
Lemma own_update_id_bounds (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A))) :
  own_update_structs sl dq inputs -∗
  ⌜∀ (i : nat) (ti : TId * IntegrateInput (A := A)), inputs !! i = Some ti →
     (Z.of_nat (clientId (in_id ti.2)) < 2^64)%Z ∧
     (Z.of_nat (clock (in_id ti.2)) < 2^64)%Z⌝.
Proof.
  iIntros "Hupd". iDestruct "Hupd" as (uivs) "(Hsl & Hcap & #Hitems)".
  iDestruct (big_sepL2_impl _ (λ _ uiv ti,
      ⌜(Z.of_nat (clientId (in_id ti.2)) < 2^64)%Z ∧
       (Z.of_nat (clock (in_id ti.2)) < 2^64)%Z⌝)%I
    with "Hitems []") as "Hpure".
  { iIntros "!>" (i uiv ti Hu Hi) "Hui".
    iDestruct "Hui" as (oleft oright opn)
      "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hulen & %Htid & %Hborrow)".
    iPureIntro. rewrite -Hin_id /toYjsId /=. split; word. }
  iDestruct (big_sepL2_length with "Hitems") as %Hlen2.
  iDestruct (big_sepL2_pure_1 with "Hpure") as %Hb.
  iPureIntro. move=> i ti Hi.
  have [uiv Huiv] : is_Some (uivs !! i).
  { apply lookup_lt_is_Some_2. rewrite Hlen2. exact (lookup_lt_Some _ _ _ Hi). }
  exact (Hb i uiv ti Huiv Hi).
Qed.

(** A valid replay leaves types outside its batch untouched. *)
Lemma ValidReplay_docm_get_off (inputs : list (TId * IntegrateInput (A := A)))
    (m0 m1 : DocM) (t : TId) :
  ValidReplay inputs m0 m1 ->
  (∀ i ti, inputs !! i = Some ti -> ti.1 ≠ t) ->
  docm_get m1 t = docm_get m0 t.
Proof.
  move=> Hvr. move: Hvr t.
  elim => [m | t0 input rest mr arr2 mr' nit _ _ _ _ _ _ IH] t Hoff; first done.
  rewrite (IH t); last by move=> i ti Hi; exact (Hoff (S i) ti Hi).
  rewrite docm_get_insert_ne //.
  move=> Heq. exact (Hoff 0%nat (t0, input) eq_refl (eq_sym Heq)).
Qed.

(* ===== the pending gate, heap side (issue #40) ============================ *)

(** [containsUpdateItemId] (the in-pool dedup probe): scans a decoded pool
    slice for a struct carrying [idv]. *)
Lemma wp_containsUpdateItemId (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A))) (idv : yjs.id.t) :
  {{{ is_pkg_init yjs ∗ own_update_structs sl dq inputs }}}
    @! yjs.containsUpdateItemId #sl #idv
  {{{ RET #(existsb (λ tj, bool_decide (in_id tj.2 = toYjsId idv)) inputs);
      own_update_structs sl dq inputs }}}.
Proof using Type*.
  wp_start as "Hupd".
  iDestruct "Hupd" as (uivs) "(Hsl & Hcap & #Hitems)".
  iDestruct (big_sepL2_length with "Hitems") as %Hlen2.
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  wp_auto.
  iAssert (∃ (j : nat),
    "Hi" ∷ i_ptr ↦ W64 j ∗ "Hitemsp" ∷ items_ptr ↦ sl ∗ "Hid" ∷ id_ptr ↦ idv ∗
    "Hsl" ∷ sl ↦*{dq} uivs ∗
    "Hcap" ∷ own_slice_cap yjs.updateItem.t sl dq ∗
    "%Hjbnd" ∷ ⌜(j <= length uivs)%nat⌝ ∗
    "%Hnomatch" ∷ ⌜existsb (λ tj, bool_decide (in_id tj.2 = toYjsId idv))
                    (take j inputs) = false⌝)%I
    with "[i items id Hsl Hcap]" as "IH".
  { iExists 0%nat. iFrame "i items id Hsl Hcap". iPureIntro.
    split; [lia | rewrite take_0 //]. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - (* probe element j *)
    have Hjlt : (j < length uivs)%nat.
    { move: Hcond. rewrite Hsllen. word. }
    destruct (uivs !! j) as [uiv|] eqn:Huiv;
      last by (apply lookup_ge_None in Huiv; lia).
    have [ti Hti] : is_Some (inputs !! j).
    { apply lookup_lt_is_Some_2. rewrite -Hlen2. exact Hjlt. }
    iDestruct (big_sepL2_lookup _ _ _ j with "Hitems") as "Hui";
      [exact Huiv | exact Hti |].
    iDestruct "Hui" as (oleft oright opn)
      "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hulen & %Htid & %Hborrow)".
    wp_auto.
    rewrite decide_True; last by word.
    iDestruct (own_slice_elem_acc (sint.Z (W64 j)) uiv sl dq uivs with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z (W64 j))) with j by word. exact Huiv. }
    wp_auto.
    wp_method_call. wp_call. wp_auto.
    wp_apply (wp_Id__Equal uiv.(yjs.updateItem.id') idv).
    iDestruct ("Hgive" $! uiv with "Hel") as "Hsl".
    have Hinsid : (<[sint.nat (W64 j) := uiv]> uivs) = uivs.
    { apply list_insert_id. replace (sint.nat (W64 j)) with j by word. exact Huiv. }
    iEval (rewrite Hinsid) in "Hsl".
    case_bool_decide as Heqid.
    + (* match: the whole scan is true *)
      wp_auto. wp_for_post.
      have -> : existsb (λ tj, bool_decide (in_id tj.2 = toYjsId idv)) inputs = true.
      { apply existsb_exists. exists ti.
        split; [by apply list_elem_of_In, (list_elem_of_lookup_2 _ j) |].
        apply bool_decide_eq_true_2. rewrite -Hin_id //. }
      iApply ("HΦ" with "[Hsl Hcap]").
      iExists uivs. iFrame "Hsl Hcap Hitems".
    + (* no match at j: advance *)
      wp_auto. wp_for_post.
      iFrame "HΦ".
      iExists (S j).
      replace (word.add (W64 j) (W64 1)) with (W64 (S j)) by word.
      iFrame "Hi Hitemsp Hid Hsl Hcap".
      iPureIntro. split; [lia |].
      erewrite take_S_r; last exact Hti.
      rewrite existsb_app Hnomatch /=.
      rewrite bool_decide_eq_false_2; first done.
      rewrite -Hin_id //.
  - (* scanned everything: the scan is false *)
    wp_auto.
    have Hjall : (j >= length uivs)%nat.
    { move: Hcond. rewrite Hsllen. rewrite Hsllen in Hjbnd. word. }
    have -> : existsb (λ tj, bool_decide (in_id tj.2 = toYjsId idv)) inputs = false.
    { rewrite -(take_ge inputs j); [exact Hnomatch | rewrite -Hlen2; lia]. }
    iApply ("HΦ" with "[Hsl Hcap]").
    iExists uivs. iFrame "Hsl Hcap Hitems".
Qed.

(** The doc-model / cell-level agreement (issue #40): under the registry
    coherence [store_inv] maintains, an id is integrated in the model iff a
    store cell carries it. This is what aligns the Go gate ([hasNode], cells)
    with the pure gate ([docm_has], the model). *)
Lemma docm_cells_agree (m : DocM) (bind : gmap P loc)
    (types : gmap loc type_state) (d : YjsId) :
  (∀ name p ts, bind !! name = Some p -> types !! p = Some ts ->
     docm_get m (RootId name) = ty_arr ts) ->
  (∀ t, docm_get m t ≠ [] -> ∃ name p, t = RootId name ∧ bind !! name = Some p) ->
  (∀ name p, bind !! name = Some p -> is_Some (types !! p)) ->
  (∀ p, is_Some (types !! p) -> ∃ name, bind !! name = Some p) ->
  (∀ p ts, types !! p = Some ts -> cells_repr (ty_arr ts) (ty_cells ts) (ty_arr ts)) ->
  (∀ p ts, types !! p = Some ts -> Forall cell_unit (ty_cells ts)) ->
  (docm_has m d = true <-> ∃ c, c ∈ all_cells types ∧ item_id (run_head c) = d).
Proof.
  move=> Hmtypes Hmdom Hbindtypes Htypesbound Hreprall Hunitall. split.
  - move=> /docm_has_spec [t [x [Hx Hid]]].
    have Hne : docm_get m t ≠ [].
    { move=> Heq. move: Hx. rewrite Heq elem_of_nil //. }
    destruct (Hmdom t Hne) as (nm & p & -> & Hbnm).
    destruct (Hbindtypes nm p Hbnm) as [ts Hts].
    have Hdg : docm_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
    have Hrep : ty_arr ts = run_flatten (ty_cells ts) := Hreprall p ts Hts.
    rewrite Hdg Hrep /run_flatten in Hx.
    apply list_elem_of_join in Hx. destruct Hx as (li & Hxin & Hli).
    apply list_elem_of_fmap in Hli. destruct Hli as (c & -> & Hcin).
    have Hu : cell_unit c := proj1 (Forall_forall _ _) (Hunitall p ts Hts) c Hcin.
    exists c. split.
    + apply all_cells_elem_of. exists p, ts. by split.
    + rewrite /cell_unit in Hu.
      rewrite /run_head.
      destruct (ic_run c) as [| y [| ? ?]] eqn:Hicr; simpl in Hu; try lia.
      move: Hxin. rewrite list_elem_of_singleton. move=> Heq. simpl.
      rewrite -Heq. exact Hid.
  - move=> [c [Hc Hid]].
    apply docm_has_spec.
    apply all_cells_elem_of in Hc. destruct Hc as (p & ts & Hts & Hcts).
    destruct (Htypesbound p (ex_intro _ ts Hts)) as [nm Hbnm].
    have Hdg : docm_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
    exists (RootId nm), (run_head c). split; [| exact Hid].
    rewrite Hdg (Hreprall p ts Hts).
    apply run_head_in_flatten; [exact Hcts |].
    exact (proj1 (Forall_forall _ _) (Hunitall p ts Hts) c Hcts).
Qed.

(* ----- the arrival gate ----- *)
(* (the pure gate lemmas [input_ready_false_of_dep] / [input_ready_true_of] /
   [input_deps_*] live in [yjs_network_model] with the pool theory) *)

(** [store.originArrived] (issue #40): the per-origin arrival check; a nil
    origin imposes no dependency. *)
Lemma wp_store__originArrived (s mref : loc) (dq : dfrac) (p : loc)
    (oid : option yjs.id.t) (types : gmap loc type_state) :
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ is_origin_id p oid ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "originArrived" #p
  {{{ (ok : bool), RET #ok;
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) ∗
      ⌜ok = true <-> match oid with
                     | None => True
                     | Some idv => ∃ c, c ∈ all_cells types ∧
                                        item_id (run_head c) = toYjsId idv
                     end⌝ }}}.
Proof using Type*.
  move=> Hnowrap.
  iIntros (Φ) "(#Hpkg & #HisP & Hitemsf & Hitemmap & Htypes) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  destruct oid as [idv |]; simpl.
  - (* a real origin: dereference and probe *)
    iDestruct "HisP" as "[%Hpne #Hpid]".
    rewrite bool_decide_eq_false_2; last first.
    { move=> Heq. exact (Hpne Heq). }
    wp_auto.
    wp_apply (wp_store__hasNode s mref dq idv types Hnowrap
                with "[$Hitemsf $Hitemmap $Htypes]").
    iIntros (ok) "(Hitemsf & Hitemmap & Htypes & %Hok)".
    wp_auto.
    iApply ("HΦ" $! ok).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. exact Hok.
  - (* nil origin: no dependency *)
    iDestruct "HisP" as %->.
    rewrite bool_decide_eq_true_2 //.
    wp_auto.
    iApply ("HΦ" $! true).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. done.
Qed.

(** [store.depsArrived] (issue #40): the structural gate, as arrival checks.
    The return value IS the pure gate [input_ready] of the decoded struct,
    given the model/cell agreement (which [store_inv]'s registry coherence
    supplies through [docm_cells_agree]). *)
Lemma wp_store__depsArrived (s mref : loc) (dq : dfrac) (uiv : yjs.updateItem.t)
    (ti : TId * IntegrateInput (A := A)) (m : DocM) (types : gmap loc type_state) :
  (∀ d : YjsId, docm_has m d = true <->
     ∃ c, c ∈ all_cells types ∧ item_id (run_head c) = d) ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ is_update_item uiv ti ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "depsArrived" #uiv
  {{{ RET #(input_ready m ti.2);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}.
Proof using Type*.
  move=> Hagree Hnowrap.
  iIntros (Φ) "(#Hpkg & #Hui & Hitemsf & Hitemmap & Htypes) HΦ".
  iDestruct "Hui" as (oleft oright opn)
    "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hulen & %Htid & %Hborrow)".
  (* the id-component views of the struct's own id *)
  have Hcid : clientId (in_id ti.2) = uint.nat uiv.(yjs.updateItem.id').(yjs.id.clientId').
  { rewrite -Hin_id /toYjsId //. }
  have Hck : clock (in_id ti.2) = uint.nat uiv.(yjs.updateItem.id').(yjs.id.clock').
  { rewrite -Hin_id /toYjsId //. }
  wp_method_call. wp_call. wp_call. wp_auto.
  (* ---- left origin ---- *)
  wp_apply (wp_store__originArrived s mref dq _ oleft types Hnowrap
              with "[$HisL $Hitemsf $Hitemmap $Htypes]").
  iIntros (okL) "(Hitemsf & Hitemmap & Htypes & %HokL)".
  wp_auto.
  destruct okL; last first.
  { (* left origin missing *)
    wp_auto.
    have Hready : input_ready m ti.2 = false.
    { destruct oleft as [idL |]; simpl in Hin_l; last first.
      { exfalso. destruct HokL as [_ H2]. have := H2 I. discriminate. }
      apply (input_ready_false_of_dep m ti.2 (toYjsId idL)).
      - apply input_deps_originL. rewrite -Hin_l //.
      - apply not_true_iff_false => Hd.
        apply Hagree in Hd. destruct HokL as [_ H2].
        have := H2 Hd. discriminate. }
    iEval (rewrite Hready) in "HΦ".
    iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]"). }
  wp_auto.
  (* ---- right origin ---- *)
  wp_apply (wp_store__originArrived s mref dq _ oright types Hnowrap
              with "[$HisR $Hitemsf $Hitemmap $Htypes]").
  iIntros (okR) "(Hitemsf & Hitemmap & Htypes & %HokR)".
  wp_auto.
  destruct okR; last first.
  { (* right origin missing *)
    wp_auto.
    have Hready : input_ready m ti.2 = false.
    { destruct oright as [idR |]; simpl in Hin_r; last first.
      { exfalso. destruct HokR as [_ H2]. have := H2 I. discriminate. }
      apply (input_ready_false_of_dep m ti.2 (toYjsId idR)).
      - apply input_deps_originR. rewrite -Hin_r //.
      - apply not_true_iff_false => Hd.
        apply Hagree in Hd. destruct HokR as [_ H2].
        have := H2 Hd. discriminate. }
    iEval (rewrite Hready) in "HΦ".
    iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]"). }
  wp_auto.
  (* the origin facts carried into the tail *)
  have HLarr : ∀ oid, in_originId ti.2 = Some oid -> docm_has m oid = true.
  { move=> oid Hoid.
    destruct oleft as [idL |]; simpl in Hin_l; last by rewrite -Hin_l in Hoid.
    rewrite -Hin_l in Hoid. injection Hoid as <-.
    apply Hagree. apply (proj1 HokL). done. }
  have HRarr : ∀ oid, in_rightOriginId ti.2 = Some oid -> docm_has m oid = true.
  { move=> oid Hoid.
    destruct oright as [idR |]; simpl in Hin_r; last by rewrite -Hin_r in Hoid.
    rewrite -Hin_r in Hoid. injection Hoid as <-.
    apply Hagree. apply (proj1 HokR). done. }
  (* ---- the own-predecessor gate ---- *)
  destruct (bool_decide
      (uint.Z (W64 0) < uint.Z uiv.(yjs.updateItem.id').(yjs.id.clock'))) eqn:Hckpos.
  - (* clock > 0: probe (client, clock-1) *)
    apply bool_decide_eq_true_1 in Hckpos.
    wp_auto.
    wp_apply (wp_NewId uiv.(yjs.updateItem.id').(yjs.id.clientId')
                (word.sub uiv.(yjs.updateItem.id').(yjs.id.clock') (W64 1))).
    wp_apply (wp_store__hasNode s mref dq _ types Hnowrap
                with "[$Hitemsf $Hitemmap $Htypes]").
    iIntros (okP) "(Hitemsf & Hitemmap & Htypes & %HokP)".
    wp_auto.
    have Hpredid : toYjsId (yjs.id.mk uiv.(yjs.updateItem.id').(yjs.id.clientId')
                     (word.sub uiv.(yjs.updateItem.id').(yjs.id.clock') (W64 1)))
                 = MkYjsId (clientId (in_id ti.2)) (clock (in_id ti.2) - 1)%nat.
    { rewrite /toYjsId /= Hcid Hck. f_equal. word. }
    have Hckform : ∃ k, clock (in_id ti.2) = S k ∧ (k = clock (in_id ti.2) - 1)%nat.
    { exists (clock (in_id ti.2) - 1)%nat. rewrite Hck. split; [word | done]. }
    destruct Hckform as (k & HckS & Hkval).
    destruct okP; last first.
    + (* predecessor missing *)
      wp_auto.
      have Hready : input_ready m ti.2 = false.
      { apply (input_ready_false_of_dep m ti.2 (MkYjsId (clientId (in_id ti.2)) k)).
        - exact (input_deps_pred ti.2 k HckS).
        - apply not_true_iff_false => Hd.
          apply Hagree in Hd. destruct HokP as [_ H2].
          rewrite Hpredid -Hkval in H2.
          have := H2 Hd. discriminate. }
      iEval (rewrite Hready) in "HΦ".
      iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]").
    + (* everything arrived *)
      wp_auto.
      have Hready : input_ready m ti.2 = true.
      { apply input_ready_true_of; [exact HLarr | exact HRarr |].
        move=> k' Hk'.
        have -> : k' = k by lia.
        apply Hagree.
        rewrite Hkval -Hpredid.
        exact (proj1 HokP eq_refl). }
      iEval (rewrite Hready) in "HΦ".
      iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]").
  - (* clock 0: no predecessor *)
    apply bool_decide_eq_false_1 in Hckpos.
    wp_auto.
    have Hready : input_ready m ti.2 = true.
    { apply input_ready_true_of; [exact HLarr | exact HRarr |].
      move=> k' Hk'. exfalso. rewrite Hck in Hk'. word. }
    iEval (rewrite Hready) in "HΦ".
    iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]").
Qed.

(* ----- the ready step: one decoded struct, repaired and integrated ----- *)

(** [store.integrateDecoded] (issue #40): the ready branch of the drain, as a
    per-struct contract — the loop-free core of the retired batch loop. The
    struct's target root must be bound ([Hbnm]; the #49 pre-bound-roots
    restriction, discharged by the drain from [is_pool_rooted] or from the
    origins' arrival), its [ValidReplay]-step facts hold at the current model
    [m], and the heap advances to the model spliced at [ti.1]. *)
Lemma wp_store__integrateDecoded (s mref tref : loc)
    (uiv : yjs.updateItem.t) (ti : TId * IntegrateInput (A := A))
    (m : DocM) (types : gmap loc type_state) (bind : gmap P loc)
    (nit : YjsItem A) (arr2 : list (YjsItem A)) (nm : P) (p : loc) :
  ti.1 = RootId nm ->
  bind !! nm = Some p ->
  toItem ti.2 (docm_get m ti.1) = Some nit ->
  IsItemValid nit ->
  maximalId nit (docm_get m ti.1) ->
  (∀ (t' : TId) x, x ∈ docm_get m t' ->
     clientId (item_id x) = clientId (in_id ti.2) ->
     (clock (item_id x) < clock (in_id ti.2))%nat) ->
  integrate ti.2 (docm_get m ti.1) = Some arr2 ->
  (∀ name p', bind !! name = Some p' -> is_Some (types !! p')) ->
  (∀ n1 n2 p', bind !! n1 = Some p' -> bind !! n2 = Some p' -> n1 = n2) ->
  (∀ name p' ts, bind !! name = Some p' -> types !! p' = Some ts ->
     docm_get m (RootId name) = ty_arr ts) ->
  (∀ d : YjsId, docm_has m d = true <->
     ∃ c, c ∈ all_cells types ∧ item_id (run_head c) = d) ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
  (Z.of_nat (clientId (in_id ti.2)) < 2^64)%Z ->
  (Z.of_nat (clock (in_id ti.2)) < 2^64)%Z ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  {{{ is_pkg_init yjs ∗ is_update_item uiv ti ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "integrateDecoded" #uiv
  {{{ (types' : gmap loc type_state), RET #();
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] parent ↦ ts ∈ types',
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) ∗
      ⌜dom types' = dom types⌝ ∗
      ⌜∀ name p' ts', bind !! name = Some p' -> types' !! p' = Some ts' ->
         docm_get (<[ti.1 := arr2]> m) (RootId name) = ty_arr ts'⌝ ∗
      ⌜∀ c, c ∈ all_cells types' -> c ∈ all_cells types ∨
         (cell_client c = W64 (clientId (in_id ti.2)) ∧
          cell_clock c = W64 (clock (in_id ti.2)))⌝ ∗
      ⌜NoDup (ic_loc <$> all_cells types')⌝ ∗
      ⌜cells_range_disjoint (all_cells types')⌝ }}}.
Proof using Type*.
  move=> Htieq Hbnm Htoit Hvld Hmax Hglob Hintg Hbindtypes Hbindinj Hmtypes
         Hagree Hnowrap Hcidb Hckb Hlocdup Hrangedisj.
  iIntros (Φ) "(#Hpkg & #Hui & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes) HΦ".
  iDestruct (types_cells_id_bounds with "Htypes") as %Hcellbnd.
  iDestruct (types_unit_all with "Htypes") as %Hunitall.
  iDestruct "Hui" as (oleft oright opn)
    "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hulen & %Htid & %Hborrow)".
  destruct ti as [tj input]. simpl in *. subst tj.
  have Hts0 : is_Some (types !! p) := Hbindtypes nm p Hbnm.
  destruct Hts0 as [[cellsj arrj0] Htsj].
  have Hdgj : docm_get m (RootId nm) = arrj0 := Hmtypes nm p _ Hbnm Htsj.
  set (arrj := docm_get m (RootId nm)) in *.
  rewrite -Hdgj in Htsj.
  iDestruct (types_arr_inv with "Htypes") as %Harrinvs.
  have Hinvj : YjsArrInvariant arrj := Harrinvs p _ Htsj.
  have Hsi : setintegrate input arrj = Some arr2.
  { rewrite (setintegrate_eq_integrate input arrj nit Hinvj Htoit Hvld Hmax). exact Hintg. }
  destruct (integrate_finds input arrj arr2 Hintg) as (leftIdx & rightIdx & HfindL & HfindR).
  iDestruct (types_entry_pures types p _ Htsj with "Htypes") as %(Hreprj & Hcparj & Hunitcj).
  simpl in Hreprj, Hcparj.
  (* uniform repair witnesses: present origins resolve inside this type's own
     cells (that is where [toItem] found them), so the borrow's parent IS
     [p]; a named parent is [nm]'s binding *)
  have Hwits : ∃ (ocL ocR : option item_cell),
    (match in_originId input, ocL with
     | Some oid, Some c => c ∈ all_cells types /\ item_id (run_head c) = oid
     | None, None => True
     | _, _ => False
     end) /\
    (match in_rightOriginId input, ocR with
     | Some oid, Some c => c ∈ all_cells types /\ item_id (run_head c) = oid
     | None, None => True
     | _, _ => False
     end) /\
    (match opn with
     | Some nm' => bind !! nm' = Some p
     | None => match ocL with
               | Some c => p = ic_parent c
               | None => match ocR with
                         | Some c => p = ic_parent c
                         | None => False
                         end
               end
     end) /\
    (match ocL with Some c => ic_loc c | None => null end) = node_loc cellsj leftIdx /\
    (match ocR with Some c => ic_loc c | None => null end) = node_loc cellsj rightIdx.
  { have Hcellsw : ∀ (kn : nat) (it : YjsItem A), arrj !! kn = Some it ->
      ∃ c, cellsj !! kn = Some c /\ run_head c = it.
    { move=> kn it Hkn. rewrite /cells_repr in Hreprj.
      rewrite Hreprj (run_flatten_singletons cellsj Hunitcj) list_lookup_fmap in Hkn.
      destruct (cellsj !! kn) as [c|] eqn:Hc; last done.
      injection Hkn as <-. by exists c. }
    have HocL : ∃ ocL,
      (match in_originId input, ocL with
       | Some oid, Some c => c ∈ all_cells types /\ item_id (run_head c) = oid
       | None, None => True
       | _, _ => False
       end) /\
      (match ocL with Some c => ic_loc c | None => null end) = node_loc cellsj leftIdx /\
      (match ocL with Some c => ic_parent c = p | None => True end).
    { destruct (in_originId input) as [oidL|] eqn:HoinL.
      - destruct (findLeftIdx_inv oidL arrj leftIdx HfindL) as (kn & it & -> & Hkn & HidL).
        destruct (Hcellsw kn it Hkn) as (cL & HcLk & HcLit).
        exists (Some cL). split_and!.
        + apply all_cells_elem_of. exists p, (MkTypeState cellsj arrj).
          split; [exact Htsj | exact (list_elem_of_lookup_2 _ _ _ HcLk)].
        + by rewrite HcLit.
        + rewrite /node_loc decide_True; last lia. rewrite Nat2Z.id HcLk //.
        + exact (Hcparj cL (list_elem_of_lookup_2 _ _ _ HcLk)).
      - exists None. move: HfindL. rewrite /findLeftIdx. move=> [= <-].
        split_and!; [done | | done].
        rewrite /node_loc. case_decide; [lia | done]. }
    have HocR : ∃ ocR,
      (match in_rightOriginId input, ocR with
       | Some oid, Some c => c ∈ all_cells types /\ item_id (run_head c) = oid
       | None, None => True
       | _, _ => False
       end) /\
      (match ocR with Some c => ic_loc c | None => null end) = node_loc cellsj rightIdx /\
      (match ocR with Some c => ic_parent c = p | None => True end).
    { destruct (in_rightOriginId input) as [oidR|] eqn:HoinR.
      - destruct (findRightIdx_inv oidR arrj rightIdx HfindR) as (kn & it & -> & Hkn & HidR).
        destruct (Hcellsw kn it Hkn) as (cR & HcRk & HcRit).
        exists (Some cR). split_and!.
        + apply all_cells_elem_of. exists p, (MkTypeState cellsj arrj).
          split; [exact Htsj | exact (list_elem_of_lookup_2 _ _ _ HcRk)].
        + by rewrite HcRit.
        + rewrite /node_loc decide_True; last lia. rewrite Nat2Z.id HcRk //.
        + exact (Hcparj cR (list_elem_of_lookup_2 _ _ _ HcRk)).
      - exists None. move: HfindR. rewrite /findRightIdx. move=> [= <-].
        split_and!; [done | | done].
        have Hlencells : length cellsj = length arrj.
        { rewrite /cells_repr in Hreprj.
          rewrite Hreprj (run_flatten_singletons cellsj Hunitcj) length_fmap //. }
        rewrite /node_loc. case_decide; [| lia].
        rewrite lookup_ge_None_2 //; lia. }
    destruct HocL as (ocL & HwL & HlocL & HparL).
    destruct HocR as (ocR & HwR & HlocR & HparR).
    exists ocL, ocR. split_and!; try done.
    destruct opn as [nm'|].
    - have Hnmeq : RootId nm = RootId nm' := Htid nm' eq_refl.
      injection Hnmeq as <-. exact Hbnm.
    - destruct ocL as [cL|]; [by rewrite -(HparL) |].
      destruct ocR as [cR|]; [by rewrite -(HparR) |].
      destruct (Hborrow eq_refl) as [HL | HR].
      + move: HwL. by destruct (in_originId input).
      + move: HwR. by destruct (in_rightOriginId input). }
  destruct Hwits as (ocL & ocR & HwL & HwR & Hwpar & HlocLeq & HlocReq).
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_func_call. wp_call. wp_auto.
  wp_alloc itv as "Hitv". wp_auto.
  set (iv := {| yjs.item.id' := uiv.(yjs.updateItem.id');
                yjs.item.originLeftId' := uiv.(yjs.updateItem.originLeftId');
                yjs.item.originRightId' := uiv.(yjs.updateItem.originRightId');
                yjs.item.left' := null; yjs.item.right' := null;
                yjs.item.parent' := null;
                yjs.item.content' := {| yjs.content.content' := uiv.(yjs.updateItem.content') |};
                yjs.item.flags' := W8 2 |}).
  iAssert (own_linked_item itv input null null null) with "[Hitv]" as "Hfresh".
  { iExists iv, oleft, oright. rewrite /own_fresh_item_raw.
    iFrame "Hitv HisL HisR". iPureIntro.
    split_and!;
      [exact Hin_l | exact Hin_r | exact Hin_id | exact Hin_c
      | reflexivity | reflexivity | reflexivity | reflexivity | exact Hulen]. }
  wp_apply (wp_store__repair s mref tref itv (uiv.(yjs.updateItem.parentName'))
              (DfracOwn 1) input opn types bind ocL ocR p
              HwL HwR Hwpar Hnowrap
              with "[$Hfresh $HisPN $Hitemsf $Hitemmap $Htypesf $Htypesmap $Htypes]").
  iIntros "(Hlinked & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes)".
  iEval (rewrite HlocLeq HlocReq) in "Hlinked".
  wp_auto.
  (* the new cell's location is fresh (issue #28 Hlocdup maintenance): the
     linked item's [itv] is a fresh allocation, so it aliases no existing cell *)
  iDestruct (linked_item_fresh with "Hlinked Htypes") as %Hfr.
  have Hidnit : item_id nit = in_id input := commutativity.toItem_id input arrj nit Htoit.
  (* the doc-global W64 clock bound from the model-level one, through the
     cells agreement *)
  have Hgmax : ∀ c0, c0 ∈ all_cells types -> cell_client c0 = W64 (clientId (item_id nit)) ->
                  (uint.Z (cell_clock c0) < uint.Z (W64 (clock (item_id nit))))%Z.
  { move=> c0 Hc0 Hcc0.
    have [Hcb0 Hkb0] := Hcellbnd c0 Hc0.
    have Hdh : docm_has m (item_id (run_head c0)) = true.
    { apply Hagree. by exists c0. }
    apply docm_has_spec in Hdh. destruct Hdh as (t' & x & Hx & Hxid).
    have Hcc0' : clientId (item_id (run_head c0)) = clientId (in_id input).
    { move: Hcc0. rewrite /cell_client Hidnit. move=> Hcc0. word. }
    have Hclt : (clock (item_id x) < clock (in_id input))%nat.
    { apply (Hglob t' x Hx). rewrite Hxid. exact Hcc0'. }
    rewrite /cell_clock Hidnit.
    have Hkeq : clock (item_id x) = clock (item_id (run_head c0)) by rewrite Hxid.
    word. }
  iDestruct (big_sepM_delete _ _ p _ Htsj with "Htypes") as "[[Hyt _] Htypesrest]".
  wp_apply (wp_Store__Integrate_nil s p itv arrj input nit cellsj types mref leftIdx rightIdx
              Hinvj Htoit Hvld Hmax HfindL HfindR Htsj Hgmax Hunitcj
              with "[$Hyt $Hlinked $Hitemsf $Hitemmap]").
  iIntros (arr2' iidx2 cells'' c2)
    "(%Hile2 & %Harr2eq & %Hinv2 & Htext2 & Hitemsf & Hitemmap & %Hperm2 & %Hsi2 & %Hnode2)".
  rewrite Hsi2 in Hsi. injection Hsi as Harr22. subst arr2'.
  destruct Hnode2 as (idx2 & Hsplice2 & Harrsp2 & Hc2look & Hc2loc & Hc2id & Hc2unit).
  have Hunitcells'' : Forall cell_unit cells''
    by (rewrite Hsplice2; exact (Forall_cell_unit_splice cellsj idx2 c2 Hunitcj Hc2unit)).
  have Hac_step : all_cells (<[p := MkTypeState cells'' arr2]> types)
                ≡ₚ all_cells types ++ [c2]
    by apply (all_cells_insert_snoc types p cellsj arrj cells'' arr2 c2 Htsj Hperm2).
  have Hcc2 : cell_client c2 = W64 (clientId (in_id input))
    by rewrite /cell_client Hc2id Hidnit //.
  have Hclk2 : cell_clock c2 = W64 (clock (in_id input))
    by rewrite /cell_clock Hc2id Hidnit //.
  iAssert ([∗ map] p' ↦ ts ∈ <[p := MkTypeState cells'' arr2]> types,
      own_ytype_cells p' (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
      ⌜Forall cell_unit (ty_cells ts)⌝)%I
    with "[Htext2 Htypesrest]" as "Htypes".
  { rewrite -insert_delete_eq.
    rewrite big_sepM_insert; last apply lookup_delete_eq.
    iFrame "Htypesrest". simpl. rewrite Harr22. iFrame "Htext2".
    iPureIntro. split; [rewrite -Harr22; exact Hinv2 | exact Hunitcells'']. }
  wp_auto.
  iEval (rewrite Harr22) in "Hitemmap".
  iApply ("HΦ" $! (<[p := MkTypeState cells'' arr2]> types)).
  iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
  iPureIntro. split_and!.
  - rewrite dom_insert_lookup_L; [done | eauto].
  - move=> nm' p' ts' Hbnm'.
    destruct (decide (p' = p)) as [-> | Hne].
    + have Hnm' : nm' = nm := Hbindinj nm' nm p Hbnm' Hbnm.
      subst nm'. rewrite lookup_insert_eq. move=> [= <-]. simpl.
      rewrite docm_get_insert_eq //.
    + rewrite lookup_insert_ne; last congruence.
      move=> Hts'.
      have Hnenm : RootId nm' ≠ RootId nm.
      { move=> [= Heqnm]. subst nm'. apply Hne.
        have : Some p' = Some p by rewrite -Hbnm' -Hbnm //.
        by move=> [=]. }
      rewrite docm_get_insert_ne //.
      exact (Hmtypes nm' p' ts' Hbnm' Hts').
  - move=> c0 Hc0.
    rewrite Hac_step in Hc0. apply elem_of_app in Hc0 as [Hold | Hnew].
    + by left.
    + apply list_elem_of_singleton in Hnew as ->.
      right. split; [exact Hcc2 | exact Hclk2].
  - (* NoDup of locations survives: the new cell's loc [itv] is fresh *)
    apply (nodup_locs_snoc (all_cells types) _ c2 Hac_step); [| exact Hlocdup].
    rewrite Hc2loc. exact Hfr.
  - (* range disjointness survives: the new cell's clock is doc-globally
       maximal among same-client cells, whose ranges are 1 (all-singleton) *)
    apply (rangedisj_snoc (all_cells types) _ c2 Hac_step); [| exact Hrangedisj].
    move=> c0 Hc0 Hcc0.
    have Hc0e := Hc0. apply all_cells_elem_of in Hc0e.
    destruct Hc0e as (p0 & ts0 & Hts0 & Hc0ts0).
    have Hu0 : cell_unit c0 := proj1 (Forall_forall _ _) (Hunitall p0 ts0 Hts0) c0 Hc0ts0.
    have Hcc0' : cell_client c0 = W64 (clientId (item_id nit)).
    { rewrite Hcc0 Hcc2 Hidnit //. }
    have Hgm := Hgmax c0 Hc0 Hcc0'.
    rewrite Hclk2 Hidnit /cell_unit in Hgm |- *.
    move: Hu0. rewrite /cell_unit. move=> Hu0. word.
Qed.

(* ===== the total applyUpdate loop (issue #40) ============================= *)

(** A [toItem] success with a present origin resolved that origin inside the
    target array, so the array is nonempty. This is how the drain derives the
    target root's binding for origin-carrying structs: a nonempty model entry
    is a registered root by [Hmdom] (origin-less structs instead carry a
    [pool_item_rooted]-style witness). *)
Lemma toItem_nonempty_of_origin (input : IntegrateInput (A := A))
    (arr : list (YjsItem A)) (nit : YjsItem A) :
  toItem input arr = Some nit ->
  in_originId input ≠ None ∨ in_rightOriginId input ≠ None ->
  arr ≠ [].
Proof.
  move=> Htoit Hor Heq. subst arr.
  have [o [r [idx [cx [_ [HoL [HoR _]]]]]]] :=
    proj1 (toItem_ok_iff input [] nit) Htoit.
  destruct Hor as [Ho | Ho].
  - destruct (in_originId input) as [oid|]; last by apply Ho.
    destruct HoL as (it & _ & Hf).
    rewrite /find_by_id /= in Hf. discriminate.
  - destruct (in_rightOriginId input) as [oid|]; last by apply Ho.
    destruct HoR as (it & _ & Hf).
    rewrite /find_by_id /= in Hf. discriminate.
Qed.

(** The two destructed corollaries of [pool_drain_unfold] the loop invariant
    steps with (goal-side rewriting keeps the [let]-reduction by conversion). *)
Lemma pool_drain_step_nil (m : DocM)
    (pool kept : list (TId * IntegrateInput (A := A))) (m1 : DocM) :
  pool_pass m pool [] = ([], kept, m1) ->
  pool_drain m pool = ([], kept, m1).
Proof. move=> Hpass. rewrite pool_drain_unfold Hpass //. Qed.

Lemma pool_drain_step_cons (m : DocM)
    (pool : list (TId * IntegrateInput (A := A)))
    (a : TId * IntegrateInput (A := A))
    (app kept app2 rest2 : list (TId * IntegrateInput (A := A))) (m1 m2 : DocM) :
  pool_pass m pool [] = (a :: app, kept, m1) ->
  pool_drain m1 kept = (app2, rest2, m2) ->
  pool_drain m pool = ((a :: app) ++ app2, rest2, m2).
Proof. move=> Hpass Hdrec. rewrite pool_drain_unfold Hpass Hdrec //. Qed.

(** [store.applyUpdate] (issue #40), the internal total loop: the pending
    buffer plus the incoming batch drain to the structural-dependency
    fixpoint. The pure [pool_drain] names the applied list, the leftover pool
    and the final model; [ValidReplay applied] carries the per-struct validity
    facts (the certificate layer produces it via [history_deliver_pool]); and
    [pool_ready_total] excludes the ready-but-stuck branch, so the Go loop
    (which integrates whenever the arrival gate passes) stays aligned with the
    model scan. Origin-less pool structs must target registered roots (the
    issue #49 pre-bound-roots restriction); origin-carrying structs derive
    their binding from the origin's arrival at integration time. *)
Lemma wp_store__applyUpdate (s mref tref : loc) (sl pend_sl0 : slice.t)
    (dq : dfrac)
    (inputs pend0 applied rest : list (TId * IntegrateInput (A := A)))
    (m m' : DocM) (types : gmap loc type_state) (bind : gmap P loc) :
  pool_drain m (pend0 ++ inputs) = (applied, rest, m') ->
  ValidReplay applied m m' ->
  pool_ready_total m (pend0 ++ inputs) applied ->
  (∀ name p, bind !! name = Some p -> is_Some (types !! p)) ->
  (∀ n1 n2 p, bind !! n1 = Some p -> bind !! n2 = Some p -> n1 = n2) ->
  (∀ p, is_Some (types !! p) -> ∃ name, bind !! name = Some p) ->
  (∀ name p ts, bind !! name = Some p -> types !! p = Some ts ->
     docm_get m (RootId name) = ty_arr ts) ->
  (∀ t, docm_get m t ≠ [] -> ∃ name p, t = RootId name ∧ bind !! name = Some p) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ pend0 ++ inputs ->
     in_originId ti.2 = None -> in_rightOriginId ti.2 = None ->
     ∃ nm, ti.1 = RootId nm ∧ is_Some (bind !! nm)) ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ pend0 ++ inputs ->
     (Z.of_nat (clock (in_id ti.2)) + 1 < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  {{{ is_pkg_init yjs ∗ own_update_structs sl dq inputs ∗
      (s .[(yjs.store.t), "pending"]) ↦ pend_sl0 ∗
      own_update_structs pend_sl0 (DfracOwn 1) pend0 ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "applyUpdate" #sl
  {{{ (pend_sl' : slice.t) (types' : gmap loc type_state), RET #();
      own_update_structs sl dq inputs ∗
      (s .[(yjs.store.t), "pending"]) ↦ pend_sl' ∗
      own_update_structs pend_sl' (DfracOwn 1) rest ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] parent ↦ ts ∈ types',
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) ∗
      ⌜dom types' = dom types⌝ ∗
      ⌜∀ name p ts', bind !! name = Some p -> types' !! p = Some ts' ->
         docm_get m' (RootId name) = ty_arr ts'⌝ ∗
      ⌜∀ t, docm_get m' t ≠ [] -> ∃ name p, t = RootId name ∧ bind !! name = Some p⌝ ∗
      ⌜∀ c, c ∈ all_cells types' -> c ∈ all_cells types ∨
         ∃ ti : TId * IntegrateInput (A := A), ti ∈ applied ∧
            cell_client c = W64 (clientId (in_id ti.2)) ∧
            cell_clock c = W64 (clock (in_id ti.2))⌝ ∗
      ⌜NoDup (ic_loc <$> all_cells types')⌝ ∗
      ⌜cells_range_disjoint (all_cells types')⌝ }}}.
Proof using Type*.
  move=> Hdrain Hvr Hrtot Hbindtypes Hbindinj Htypesbound Hmtypes Hmdom
         Hrooted Hnowrap Hkb1 Hlocdup Hrangedisj.
  iIntros (Φ) "(#Hpkg & Hupd & Hpendf & Hpend & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes) HΦ".
  (* W64 id bounds of the whole pool, from the two heap slices *)
  iDestruct (own_update_id_bounds with "Hupd") as %Hidbin.
  iDestruct (own_update_id_bounds with "Hpend") as %Hidbpd.
  have Hidb : ∀ ti : TId * IntegrateInput (A := A), ti ∈ pend0 ++ inputs ->
      (Z.of_nat (clientId (in_id ti.2)) < 2^64)%Z ∧
      (Z.of_nat (clock (in_id ti.2)) < 2^64)%Z.
  { move=> ti /elem_of_app [Hin | Hin];
      apply list_elem_of_lookup_1 in Hin; destruct Hin as [ix Hix];
      [exact (Hidbpd ix ti Hix) | exact (Hidbin ix ti Hix)]. }
  iDestruct "Hupd" as (uivs_in) "(Hslin & Hcapin & #Hitemsin)".
  iDestruct (big_sepL2_length with "Hitemsin") as %Hlenin.
  iDestruct "Hpend" as (uivs_pd) "(Hslpd & Hcappd & #Hitemspd)".
  iDestruct (big_sepL2_length with "Hitemspd") as %Hlenpd.
  wp_method_call. wp_call. wp_call. wp_auto.
  (* ----- phase A: pool := pending ++ structs ----- *)
  iDestruct (own_slice_len with "Hslin") as %[Hinlen Hinlen0].
  iAssert (∃ (j : nat) (pslA : slice.t) (uivsA : list yjs.updateItem.t),
      "Hi" ∷ i_ptr ↦ W64 j ∗
      "Hpoolp" ∷ pool_ptr ↦ pslA ∗
      "HslA" ∷ pslA ↦* uivsA ∗
      "HcapA" ∷ own_slice_cap yjs.updateItem.t pslA (DfracOwn 1) ∗
      "#HitemsA" ∷ ([∗ list] uiv;ti ∈ uivsA;(pend0 ++ take j inputs),
          is_update_item uiv ti) ∗
      "Hslin" ∷ sl ↦*{dq} uivs_in ∗
      "%HjA" ∷ ⌜(j <= length uivs_in)%nat⌝)%I
    with "[i pool Hslpd Hcappd Hslin]" as "IH".
  { iExists 0%nat, pend_sl0, uivs_pd. iFrame "i pool Hslpd Hcappd Hslin".
    rewrite take_0 app_nil_r. iFrame "Hitemspd".
    iPureIntro. lia. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - (* append structs[j] *)
    have Hjlt : (j < length uivs_in)%nat.
    { move: Hcond. rewrite Hinlen. word. }
    destruct (uivs_in !! j) as [uiv|] eqn:Huiv;
      last by (apply lookup_ge_None in Huiv; lia).
    have [ti Hti] : is_Some (inputs !! j).
    { apply lookup_lt_is_Some_2. rewrite -Hlenin. exact Hjlt. }
    iDestruct (big_sepL2_lookup _ _ _ j with "Hitemsin") as "#Hui";
      [exact Huiv | exact Hti |].
    wp_auto.
    rewrite decide_True; last by word.
    iDestruct (own_slice_elem_acc (sint.Z (W64 j)) uiv sl dq uivs_in with "Hslin")
      as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z (W64 j))) with j by word. exact Huiv. }
    wp_auto.
    iDestruct ("Hgive" $! uiv with "Hel") as "Hslin".
    have Hinsid : (<[sint.nat (W64 j) := uiv]> uivs_in) = uivs_in.
    { apply list_insert_id. replace (sint.nat (W64 j)) with j by word. exact Huiv. }
    iEval (rewrite Hinsid) in "Hslin".
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros "%sing [Hsing _]". wp_auto.
    wp_apply (wp_slice_append with "[$HslA $HcapA $Hsing]").
    iIntros (pslA') "(HslA' & HcapA' & _)". wp_auto.
    wp_for_post.
    iFrame "Hcapin Hpendf Hitemsf Hitemmap Htypesf Htypesmap Htypes HΦ s structs".
    iExists (S j), pslA', (uivsA ++ [uiv]).
    replace (word.add (W64 j) (W64 1)) with (W64 (S j)) by word.
    have H00 : sint.nat (W64 0) = 0%nat by word.
    iEval (rewrite H00 /=) in "HslA'".
    iFrame "Hi Hpoolp HslA' HcapA' Hslin".
    iSplit.
    { erewrite take_S_r; last exact Hti.
      rewrite app_assoc. rewrite big_sepL2_snoc.
      iSplit; [iFrame "HitemsA" | iFrame "Hui"]. }
    iPureIntro. lia.
  - (* pool complete: content is pend0 ++ inputs; pending := nil *)
    wp_auto.
    have Hjge : (j >= length uivs_in)%nat.
    { move: Hcond. rewrite Hinlen. rewrite Hinlen in HjA. word. }
    have Htakeall : take j inputs = inputs.
    { apply take_ge. rewrite -Hlenin. lia. }
    iEval (rewrite Htakeall) in "HitemsA".
    (* ----- phase B: the drain loop ----- *)
    iAssert (∃ (pv : bool) (poolS : slice.t) (uivsP : list yjs.updateItem.t)
               (poolj appliedj suffix : list (TId * IntegrateInput (A := A)))
               (typesj : gmap loc type_state) (mj : DocM),
        "Hprog" ∷ progress_ptr ↦ pv ∗
        "Hpoolp" ∷ pool_ptr ↦ poolS ∗
        "HslP" ∷ poolS ↦* uivsP ∗
        "HcapP" ∷ own_slice_cap yjs.updateItem.t poolS (DfracOwn 1) ∗
        "#HitemsPj" ∷ ([∗ list] uiv;ti ∈ uivsP;poolj, is_update_item uiv ti) ∗
        "Hitemsf" ∷ (s .[(yjs.store.t), "items"]) ↦ mref ∗
        "Hitemmap" ∷ own_item_map mref (DfracOwn 1) typesj ∗
        "Htypesf" ∷ (s .[(yjs.store.t), "types"]) ↦ tref ∗
        "Htypesmap" ∷ own_map tref (DfracOwn 1) bind ∗
        "Htypes" ∷ ([∗ map] parent ↦ ts ∈ typesj,
            own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
            ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
            ⌜Forall cell_unit (ty_cells ts)⌝) ∗
        "%Hpoolsubj" ∷ ⌜∀ ti : TId * IntegrateInput (A := A),
            ti ∈ poolj -> ti ∈ pend0 ++ inputs⌝ ∗
        "%Hprj" ∷ ⌜PoolReplay m appliedj mj⌝ ∗
        "%Hdomj" ∷ ⌜dom typesj = dom types⌝ ∗
        "%Hmtypesj" ∷ ⌜∀ name pl ts, bind !! name = Some pl ->
            typesj !! pl = Some ts -> docm_get mj (RootId name) = ty_arr ts⌝ ∗
        "%Hmdomj" ∷ ⌜∀ t, docm_get mj t ≠ [] ->
            ∃ name pl, t = RootId name ∧ bind !! name = Some pl⌝ ∗
        "%Hnowrapj" ∷ ⌜∀ c0, c0 ∈ all_cells typesj ->
            (uint.Z (cell_clock c0) + 1 < 2^64)%Z⌝ ∗
        "%Hprovj" ∷ ⌜∀ c0, c0 ∈ all_cells typesj -> c0 ∈ all_cells types ∨
            ∃ ti : TId * IntegrateInput (A := A), ti ∈ applied ∧
               cell_client c0 = W64 (clientId (in_id ti.2)) ∧
               cell_clock c0 = W64 (clock (in_id ti.2))⌝ ∗
        "%Hlocdupj" ∷ ⌜NoDup (ic_loc <$> all_cells typesj)⌝ ∗
        "%Hrangedisjj" ∷ ⌜cells_range_disjoint (all_cells typesj)⌝ ∗
        "%Hmid" ∷ ⌜pv = true ->
            pool_drain mj poolj = (suffix, rest, m') ∧
            applied = appliedj ++ suffix ∧ ValidReplay suffix mj m'⌝ ∗
        "%Hfin" ∷ ⌜pv = false -> poolj = rest ∧ mj = m' ∧ applied = appliedj⌝)%I
      with "[progress Hpoolp HslA HcapA Hitemsf Hitemmap Htypesf Htypesmap Htypes]"
      as "IH".
    { iExists true, pslA, uivsA, (pend0 ++ inputs), [], applied, types, m.
      iFrame "progress Hpoolp HslA HcapA Hitemsf Hitemmap Htypesf Htypesmap Htypes".
      iFrame "HitemsA".
      iPureIntro. split_and!.
      - done.
      - constructor.
      - done.
      - exact Hmtypes.
      - exact Hmdom.
      - exact Hnowrap.
      - move=> c0 Hc0. by left.
      - exact Hlocdup.
      - exact Hrangedisj.
      - move=> _. split_and!; [exact Hdrain | done | exact Hvr].
      - move=> Hf. discriminate. }
    wp_for "IH".
    destruct pv.
    + (* progress: run one more pass *)
      rewrite decide_True; last done.
      destruct (Hmid eq_refl) as (Hdrainj & Happj & Hvrj).
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done.
      iIntros "%rsl0 [Hrsl0 Hrcap0]". wp_auto.
      (* the pass computation this iteration refines *)
      destruct (pool_pass mj poolj []) as [[app_rem0 keptfin0] m_pend0] eqn:Hpass0.
      (* the future passes' applied list ([suffix] is introduced as [suffix0]:
         the binder shadows stdpp's [suffix]) *)
      have [af [Hsufdec Hvraf]] : ∃ af,
          suffix0 = app_rem0 ++ af ∧ ValidReplay (app_rem0 ++ af) mj m'.
      { destruct app_rem0 as [| a0 ar0].
        - have Hdd := pool_drain_step_nil mj poolj keptfin0 m_pend0 Hpass0.
          rewrite Hdrainj in Hdd.
          move: Hdd => [= Hsuf Hrest2 Hm2].
          have Hmp0 : m_pend0 = mj :=
            pool_pass_no_progress poolj mj [] keptfin0 m_pend0 Hpass0.
          subst suffix0. exists []. split; first done.
          rewrite Hm2 Hmp0. constructor.
        - destruct (pool_drain m_pend0 keptfin0) as [[app2 rest2] m2] eqn:Hdrec.
          have Hdd := pool_drain_step_cons mj poolj a0 ar0 keptfin0 app2 rest2
                        m_pend0 m2 Hpass0 Hdrec.
          rewrite Hdrainj in Hdd.
          move: Hdd => [= Hsuf Hrest2 Hm2].
          exists app2. split; first exact Hsuf.
          rewrite Hsuf in Hvrj. exact Hvrj. }
      iDestruct (big_sepL2_length with "HitemsPj") as %HlenP.
      iDestruct (own_slice_len with "HslP") as %[HPlen HPlen0].
      (* ----- the inner scan ----- *)
      iAssert (∃ (i : nat) (pvi : bool) (restS : slice.t)
                 (uivsR : list yjs.updateItem.t)
                 (keptacc appacc app_rem af2 : list (TId * IntegrateInput (A := A)))
                 (types_c : gmap loc type_state) (m_c : DocM),
          "Hii" ∷ i_ptr ↦ W64 i ∗
          "Hprog" ∷ progress_ptr ↦ pvi ∗
          "Hrestp" ∷ rest_ptr ↦ restS ∗
          "HslR" ∷ restS ↦* uivsR ∗
          "HcapR" ∷ own_slice_cap yjs.updateItem.t restS (DfracOwn 1) ∗
          "#HitemsR" ∷ ([∗ list] uiv;ti ∈ uivsR;keptacc, is_update_item uiv ti) ∗
          "Hitemsf" ∷ (s .[(yjs.store.t), "items"]) ↦ mref ∗
          "Hitemmap" ∷ own_item_map mref (DfracOwn 1) types_c ∗
          "Htypesf" ∷ (s .[(yjs.store.t), "types"]) ↦ tref ∗
          "Htypesmap" ∷ own_map tref (DfracOwn 1) bind ∗
          "Htypes" ∷ ([∗ map] parent ↦ ts ∈ types_c,
              own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
              ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
              ⌜Forall cell_unit (ty_cells ts)⌝) ∗
          "%Hilen" ∷ ⌜(i <= length poolj)%nat⌝ ∗
          "%Hpassa" ∷ ⌜pool_pass m_c (drop i poolj) keptacc =
              (app_rem, keptfin0, m_pend0)⌝ ∗
          "%Hpassc" ∷ ⌜pool_pass mj poolj [] =
              (appacc ++ app_rem, keptfin0, m_pend0)⌝ ∗
          "%Happdec" ∷ ⌜applied = appliedj ++ appacc ++ app_rem ++ af2⌝ ∗
          "%Hvrc" ∷ ⌜ValidReplay (app_rem ++ af2) m_c m'⌝ ∗
          "%Hprc" ∷ ⌜PoolReplay m (appliedj ++ appacc) m_c⌝ ∗
          "%Hkeptsub" ∷ ⌜∀ ti, ti ∈ keptacc -> ti ∈ poolj⌝ ∗
          "%Hpv" ∷ ⌜pvi = false <-> appacc = []⌝ ∗
          "%Hdomc" ∷ ⌜dom types_c = dom types⌝ ∗
          "%Hmtypesc" ∷ ⌜∀ name pl ts, bind !! name = Some pl ->
              types_c !! pl = Some ts -> docm_get m_c (RootId name) = ty_arr ts⌝ ∗
          "%Hmdomc" ∷ ⌜∀ t, docm_get m_c t ≠ [] ->
              ∃ name pl, t = RootId name ∧ bind !! name = Some pl⌝ ∗
          "%Hnowrapc" ∷ ⌜∀ c0, c0 ∈ all_cells types_c ->
              (uint.Z (cell_clock c0) + 1 < 2^64)%Z⌝ ∗
          "%Hprovc" ∷ ⌜∀ c0, c0 ∈ all_cells types_c -> c0 ∈ all_cells types ∨
              ∃ ti : TId * IntegrateInput (A := A), ti ∈ applied ∧
                 cell_client c0 = W64 (clientId (in_id ti.2)) ∧
                 cell_clock c0 = W64 (clock (in_id ti.2))⌝ ∗
          "%Hlocdupc" ∷ ⌜NoDup (ic_loc <$> all_cells types_c)⌝ ∗
          "%Hrangedisjc" ∷ ⌜cells_range_disjoint (all_cells types_c)⌝)%I
        with "[i Hprog rest Hrsl0 Hrcap0 Hitemsf Hitemmap Htypesf Htypesmap Htypes]"
        as "IHin".
      { iExists 0%nat, false, _, [], [], [], app_rem0, af, typesj, mj.
        iFrame "i Hprog rest Hrsl0 Hrcap0 Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplit; first by rewrite big_sepL2_nil.
        iPureIntro. split_and!.
        - lia.
        - rewrite drop_0. exact Hpass0.
        - exact Hpass0.
        - rewrite Happj Hsufdec //.
        - exact Hvraf.
        - rewrite app_nil_r. exact Hprj.
        - move=> ti Hti. by apply elem_of_nil in Hti.
        - done.
        - exact Hdomj.
        - exact Hmtypesj.
        - exact Hmdomj.
        - exact Hnowrapj.
        - exact Hprovj.
        - exact Hlocdupj.
        - exact Hrangedisjj. }
      wp_for "IHin".
      case_bool_decide as Hcondi.
      * (* scan struct i *)
        have Hilt : (i < length uivsP)%nat.
        { move: Hcondi. rewrite HPlen. word. }
        destruct (uivsP !! i) as [uiv|] eqn:Huiv;
          last by (apply lookup_ge_None in Huiv; lia).
        destruct (poolj !! i) as [[tj input]|] eqn:Hpi;
          last by (apply lookup_ge_None in Hpi; rewrite -HlenP in Hpi; lia).
        iDestruct (big_sepL2_lookup _ _ _ i with "HitemsPj") as "#Hui";
          [exact Huiv | exact Hpi |].
        iDestruct (big_sepL2_lookup _ _ _ i with "HitemsPj") as
          (oleft oright opn)
          "(#HisL & #HisR & #HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hulen & %Htid & %Hborrow)";
          [exact Huiv | exact Hpi |].
        simpl in Hin_l, Hin_r, Hin_id, Hin_c, Htid, Hborrow.
        (* registry coherence, transported to the current [types_c] *)
        have Hbindtypesc : ∀ name pl, bind !! name = Some pl ->
            is_Some (types_c !! pl).
        { move=> name pl Hb. apply elem_of_dom. rewrite Hdomc.
          apply elem_of_dom. exact (Hbindtypes name pl Hb). }
        have Htypesboundc : ∀ pl, is_Some (types_c !! pl) ->
            ∃ name, bind !! name = Some pl.
        { move=> pl Hs0. apply Htypesbound. apply elem_of_dom. rewrite -Hdomc.
          apply elem_of_dom. exact Hs0. }
        iDestruct (types_repr_all with "Htypes") as %Hreprallc.
        iDestruct (types_unit_all with "Htypes") as %Hunitallc.
        have Hagreec : ∀ d : YjsId, docm_has m_c d = true <->
            ∃ c0, c0 ∈ all_cells types_c ∧ item_id (run_head c0) = d.
        { move=> d.
          exact (docm_cells_agree m_c bind types_c d Hmtypesc Hmdomc
                   Hbindtypesc Htypesboundc Hreprallc Hunitallc). }
        have Hpool0in : (tj, input) ∈ pend0 ++ inputs.
        { apply Hpoolsubj. exact (list_elem_of_lookup_2 _ _ _ Hpi). }
        (* read pool[i] into ui *)
        wp_auto.
        rewrite decide_True; last by word.
        iDestruct (own_slice_elem_acc (sint.Z (W64 i)) uiv poolS (DfracOwn 1)
                     uivsP with "HslP") as "[Hel Hgive]".
        { word. }
        { replace (Z.to_nat (sint.Z (W64 i))) with i by word. exact Huiv. }
        wp_auto.
        iDestruct ("Hgive" $! uiv with "Hel") as "HslP".
        have Hinsid : (<[sint.nat (W64 i) := uiv]> uivsP) = uivsP.
        { apply list_insert_id.
          replace (sint.nat (W64 i)) with i by word. exact Huiv. }
        iEval (rewrite Hinsid) in "HslP".
        (* the arrival probe: hasNode *)
        wp_apply (wp_store__hasNode s mref (DfracOwn 1)
                    (uiv.(yjs.updateItem.id')) types_c Hnowrapc
                    with "[$Hitemsf $Hitemmap $Htypes]").
        iIntros (ok) "(Hitemsf & Hitemmap & Htypes & %Hok)".
        have Hokm : ok = docm_has m_c (in_id input).
        { destruct (docm_has m_c (in_id input)) eqn:Hd.
          - apply Hagreec in Hd. destruct Hd as (c0 & Hc0 & Hid0).
            apply Hok. exists c0. split; [exact Hc0 | by rewrite Hid0 -Hin_id].
          - destruct ok; last done.
            destruct (proj1 Hok eq_refl) as (c0 & Hc0 & Hid0).
            have Hd' : docm_has m_c (in_id input) = true.
            { apply Hagreec. exists c0.
              split; [exact Hc0 | by rewrite Hid0 Hin_id]. }
            congruence. }
        destruct (docm_has m_c (in_id input)) eqn:Hd; subst ok.
        { (* duplicate: continue *)
          wp_auto. wp_for_post.
          iFrame "Hcapin Hpendf HΦ s Hslin Hpoolp HslP HcapP".
          iExists (S i), pvi, restS, uivsR, keptacc, appacc, app_rem, af2,
            types_c, m_c.
          replace (word.add (W64 i) (W64 1)) with (W64 (S i)) by word.
          iFrame "Hii Hprog Hrestp HslR HcapR Hitemsf Hitemmap Htypesf Htypesmap Htypes".
          iFrame "HitemsR".
          iPureIntro. split_and!; try done.
          - apply (lookup_lt_Some _ _ _ Hpi).
          - rewrite (drop_S poolj (tj, input) i Hpi) /= Hd in Hpassa.
            exact Hpassa. }
        (* fresh: probe the structural gate *)
        wp_auto.
        wp_apply (wp_store__depsArrived s mref (DfracOwn 1) uiv (tj, input)
                    m_c types_c Hagreec Hnowrapc
                    with "[$Hui $Hitemsf $Hitemmap $Htypes]").
        iIntros "(Hitemsf & Hitemmap & Htypes)".
        destruct (input_ready m_c input) eqn:Hready.
        -- (* ready: certified pools always integrate *)
           have Hsome : is_Some (integrate input (docm_get m_c tj)).
           { apply (Hrtot (appliedj ++ appacc) (app_rem ++ af2) m_c (tj, input)).
             - rewrite Happdec !app_assoc //.
             - exact Hprc.
             - exact Hpool0in.
             - exact Hd.
             - exact Hready. }
           destruct Hsome as [arr' Hint'].
           (* step the pass equation *)
           rewrite (drop_S poolj (tj, input) i Hpi) /= Hd Hready Hint' in Hpassa.
           destruct (pool_pass (<[tj := arr']> m_c) (drop (S i) poolj) keptacc)
             as [[app2 kept2] m2] eqn:Hrec.
           move: Hpassa => [= Happrem Hkeq Hmeq].
           subst app_rem kept2 m2.
           (* align with the replay: the head is exactly this struct *)
           rewrite -app_comm_cons in Hvrc.
           inversion Hvrc as [| t0 input0 rest0 m0 arr2 mf nit Htoit Hvld
                                Hmax Hglob Hintg Hrest Heqin [Heqi Heqa Heqf]];
             subst.
           have Harr2 : arr2 = arr'.
           { rewrite Hint' in Hintg. by injection Hintg. }
           subst arr2.
           (* the target root's binding: origin-less structs carry a witness,
              origin-carrying structs land in a nonempty (hence bound) type *)
           have [nm [Htjeq [pl Hbnm]]] : ∃ nm, tj = RootId nm ∧ is_Some (bind !! nm).
           { destruct (decide (in_originId input = None ∧
                               in_rightOriginId input = None)) as [[HoN HrN] | Hor].
             - destruct (Hrooted (tj, input) Hpool0in HoN HrN) as (nm & Heq & Hsm).
               by exists nm.
             - have Hne : docm_get m_c tj ≠ [].
               { apply (toItem_nonempty_of_origin input _ nit Htoit).
                 apply not_and_l in Hor.
                 by destruct Hor as [Ho | Ho]; [left | right]. }
               destruct (Hmdomc tj Hne) as (nm & pl & Heq & Hb).
               exists nm. split; [exact Heq | by exists pl]. }
           have Hcidb : (Z.of_nat (clientId (in_id input)) < 2^64)%Z.
           { exact (proj1 (Hidb (tj, input) Hpool0in)). }
           have Hckb : (Z.of_nat (clock (in_id input)) < 2^64)%Z.
           { exact (proj2 (Hidb (tj, input) Hpool0in)). }
           simpl. rewrite Hready. wp_auto.
           wp_apply (wp_store__integrateDecoded s mref tref uiv (tj, input)
                       m_c types_c bind nit arr' nm pl
                       Htjeq Hbnm Htoit Hvld Hmax Hglob Hint'
                       Hbindtypesc Hbindinj Hmtypesc Hagreec Hnowrapc Hcidb Hckb
                       Hlocdupc Hrangedisjc
                       with "[$Hui $Hitemsf $Hitemmap $Htypesf $Htypesmap $Htypes]").
           iIntros (types'') "(Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes & %Hdom'' & %Hmtypes'' & %Hprov'' & %Hlocdup'' & %Hrangedisj'')".
           wp_auto. wp_for_post.
           iFrame "Hcapin Hpendf HΦ s Hslin Hpoolp HslP HcapP".
           iExists (S i), true, restS, uivsR, keptacc, (appacc ++ [(tj, input)]),
             app2, af2, types'', (<[tj := arr']> m_c).
           replace (word.add (W64 i) (W64 1)) with (W64 (S i)) by word.
           iFrame "Hii Hprog Hrestp HslR HcapR Hitemsf Hitemmap Htypesf Htypesmap Htypes".
           iFrame "HitemsR".
           iPureIntro. split_and!.
           ++ apply (lookup_lt_Some _ _ _ Hpi).
           ++ exact Hrec.
           ++ rewrite -app_assoc /=. exact Hpassc.
           ++ rewrite -app_assoc /=. exact Happdec.
           ++ exact Hrest.
           ++ rewrite app_assoc.
              apply (PoolReplay_app m m_c _ (appliedj ++ appacc) [(tj, input)] Hprc).
              apply (PoolReplay_cons m_c (tj, input) arr' [] _ Hd Hready Hint').
              constructor.
           ++ exact Hkeptsub.
           ++ split; [move=> Hf; discriminate | move=> Habs; by destruct appacc].
           ++ by rewrite Hdom''.
           ++ exact Hmtypes''.
           ++ move=> t Hne.
              destruct (decide (t = tj)) as [-> | Hnet].
              { exists nm, pl. split; [exact Htjeq | exact Hbnm]. }
              rewrite docm_get_insert_ne // in Hne.
              exact (Hmdomc t Hne).
           ++ move=> c0 Hc0.
              destruct (Hprov'' c0 Hc0) as [Hold | [Hcc Hck]].
              { exact (Hnowrapc c0 Hold). }
              rewrite Hck. simpl in Hck |- *.
              have Hb := Hkb1 (tj, input) Hpool0in. simpl in Hb. word.
           ++ move=> c0 Hc0.
              destruct (Hprov'' c0 Hc0) as [Hold | [Hcc Hck]].
              { exact (Hprovc c0 Hold). }
              right. exists (tj, input). split_and!; [| exact Hcc | exact Hck].
              rewrite Happdec. apply elem_of_app; right.
              apply elem_of_app; right. apply elem_of_app; left.
              apply elem_of_cons. by left.
           ++ exact Hlocdup''.
           ++ exact Hrangedisj''.
        -- (* blocked: keep (deduplicated by id) *)
           rewrite (drop_S poolj (tj, input) i Hpi) /= Hd Hready in Hpassa.
           simpl. rewrite Hready. wp_auto.
           wp_apply (wp_containsUpdateItemId restS (DfracOwn 1) keptacc
                       (uiv.(yjs.updateItem.id')) with "[HslR HcapR]").
           { iExists uivsR. iFrame "HslR HcapR HitemsR". }
           iIntros "Hos". iDestruct "Hos" as (uivsR2) "(HslR & HcapR & #HitemsR2)".
           rewrite Hin_id.
           destruct (existsb (λ tj0, bool_decide (in_id tj0.2 = in_id input))
                       keptacc) eqn:Hex.
           ** (* already kept: skip *)
              wp_auto. wp_for_post.
              iFrame "Hcapin Hpendf HΦ s Hslin Hpoolp HslP HcapP".
              iExists (S i), pvi, restS, uivsR2, keptacc, appacc, app_rem, af2,
                types_c, m_c.
              replace (word.add (W64 i) (W64 1)) with (W64 (S i)) by word.
              iFrame "Hii Hprog Hrestp HslR HcapR Hitemsf Hitemmap Htypesf Htypesmap Htypes".
              iFrame "HitemsR2".
              iPureIntro. split_and!; try done.
              --- apply (lookup_lt_Some _ _ _ Hpi).
              --- rewrite /pool_keep /= Hex in Hpassa. exact Hpassa.
           ** (* newly kept: append to rest *)
              wp_auto.
              wp_apply wp_slice_literal. iSplitR; first done.
              iIntros "%sing [Hsing _]". wp_auto.
              wp_apply (wp_slice_append with "[$HslR $HcapR $Hsing]").
              iIntros (restS') "(HslR' & HcapR' & _)". wp_auto.
              wp_for_post.
              iFrame "Hcapin Hpendf HΦ s Hslin Hpoolp HslP HcapP".
              iExists (S i), pvi, restS', (uivsR2 ++ [uiv]),
                (keptacc ++ [(tj, input)]), appacc, app_rem, af2, types_c, m_c.
              replace (word.add (W64 i) (W64 1)) with (W64 (S i)) by word.
              have H00 : sint.nat (W64 0) = 0%nat by word.
              iEval (rewrite H00 /=) in "HslR'".
              iFrame "Hii Hprog Hrestp HslR' HcapR' Hitemsf Hitemmap Htypesf Htypesmap Htypes".
              iSplit.
              { rewrite big_sepL2_snoc.
                iSplit; [iFrame "HitemsR2" | iFrame "Hui"]. }
              iPureIntro. split_and!; try done.
              --- apply (lookup_lt_Some _ _ _ Hpi).
              --- rewrite /pool_keep /= Hex in Hpassa. exact Hpassa.
              --- move=> ti Hti. apply elem_of_app in Hti.
                  destruct Hti as [Hti | Hti]; first exact (Hkeptsub ti Hti).
                  apply list_elem_of_singleton in Hti. subst ti.
                  exact (list_elem_of_lookup_2 _ _ _ Hpi).
      * (* scan done: close the pass *)
        have Hige : (length poolj <= i)%nat.
        { rewrite -HlenP HPlen. rewrite -HlenP HPlen in Hilen.
          move: Hcondi. word. }
        rewrite drop_ge in Hpassa; last exact Hige.
        simpl in Hpassa.
        move: Hpassa => [= Happrem Hkeq Hmeq].
        subst app_rem keptfin0 m_pend0.
        rewrite app_nil_r in Hpassc.
        have Hsufeq : suffix0 = appacc ++ af2.
        { apply (app_inv_head appliedj). rewrite -Happj.
          rewrite Happdec /= //. }
        wp_auto. wp_for_post.
        iFrame "Hcapin Hpendf HΦ s Hslin".
        iExists pvi, restS, uivsR, keptacc, (appliedj ++ appacc), af2,
          types_c, m_c.
        iFrame "Hprog Hpoolp HslR HcapR Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iFrame "HitemsR".
        iPureIntro. split_and!.
        ** move=> ti Hti. apply Hpoolsubj. exact (Hkeptsub ti Hti).
        ** exact Hprc.
        ** exact Hdomc.
        ** exact Hmtypesc.
        ** exact Hmdomc.
        ** exact Hnowrapc.
        ** exact Hprovc.
        ** exact Hlocdupc.
        ** exact Hrangedisjc.
        ** (* progress: one more drain iteration remains *)
           move=> Hpvt.
           destruct appacc as [| a0 acc0].
           { have := proj2 Hpv eq_refl. rewrite Hpvt.
             move=> Hcontra. discriminate. }
           destruct (pool_drain m_c keptacc) as [[app2' rest2'] m2'] eqn:Hdrec2.
           have Hdd := pool_drain_step_cons mj poolj a0 acc0 keptacc app2'
                         rest2' m_c m2' Hpassc Hdrec2.
           rewrite Hdrainj in Hdd.
           move: Hdd => [= Hsuf Hrest2 Hm2].
           have Haf2 : af2 = app2'.
           { apply (app_inv_head (a0 :: acc0)). rewrite -Hsufeq Hsuf //. }
           split_and!.
           --- rewrite Haf2 Hrest2 Hm2 //.
           --- rewrite -app_assoc. exact Happdec.
           --- exact Hvrc.
        ** (* no progress: the drain is complete *)
           move=> Hpvf.
           have Hacc0 : appacc = [] := proj1 Hpv Hpvf.
           subst appacc.
           have Hdd := pool_drain_step_nil mj poolj keptacc m_c Hpassc.
           rewrite Hdrainj in Hdd.
           move: Hdd => [= Hsuf Hrest2 Hm2].
           split_and!.
           --- by rewrite Hrest2.
           --- by rewrite Hm2.
           --- rewrite Happj Hsuf app_nil_r //.
    + (* drain complete: write back the pending pool and return *)
      rewrite decide_False; last done.
      rewrite decide_True; last done.
      destruct (Hfin eq_refl) as (Hpooleq & Hmeq & Happeq).
      subst poolj mj.
      wp_auto.
      iApply ("HΦ" $! poolS typesj).
      iFrame "Hpendf Hitemsf Hitemmap Htypesf Htypesmap Htypes".
      iSplitL "Hslin Hcapin".
      { iExists uivs_in. iFrame "Hslin Hcapin Hitemsin". }
      iSplitL "HslP HcapP".
      { iExists uivsP. iFrame "HslP HcapP HitemsPj". }
      iPureIntro. split_and!.
      * exact Hdomj.
      * exact Hmtypesj.
      * exact Hmdomj.
      * move=> c0 Hc0.
        destruct (Hprovj c0 Hc0) as [Hold | Hnew]; [by left | by right].
      * exact Hlocdupj.
      * exact Hrangedisjj.
Qed.

(* ===== the public certificate spec (issue #40) ============================ *)

(** An applied struct's target type is nonempty at the final model (its own
    item landed there and membership is monotone) -- what lets the public spec
    mint one [is_root_lb] content certificate per applied struct. *)
Lemma ValidReplay_applied_nonempty
    (l : list (TId * IntegrateInput (A := A))) (m0 m1 : DocM) :
  ValidReplay l m0 m1 ->
  ∀ ti : TId * IntegrateInput (A := A), ti ∈ l -> docm_get m1 ti.1 ≠ [].
Proof.
  elim => [mx | t input rest0 mr arr2 mr' nit Htoit Hvld Hmax Hglob Hint Hrest IH]
    ti Hin.
  - by apply elem_of_nil in Hin.
  - apply elem_of_cons in Hin. destruct Hin as [-> | Hin]; last exact (IH ti Hin).
    simpl.
    destruct (integrate_new_mem input _ _ Hint) as (it & Hid & Hit).
    have Hit' : it ∈ docm_get mr' t.
    { apply (ValidReplay_mem rest0 (<[t := arr2]> mr) mr' Hrest t).
      rewrite docm_get_insert_eq //. }
    move=> Heq. rewrite Heq in Hit'. by apply elem_of_nil in Hit'.
Qed.

(** The gate totality of a certified pool, extracted from the ghost history:
    at any drain intermediate, a fresh ready struct integrates. Stated here
    rather than in [yjs_history] to keep this iteration off the slow
    downstream rebuild; the proof opens the history invariant read-only,
    mirroring [history_deliver_pool]. *)
Lemma history_pool_ready_total γh (c : ClientId) h (m : DocM)
    (pool applied : list (TId * IntegrateInput (A := A))) E :
  ↑histN ⊆ E ->
  history_state_coh h m ->
  (∀ t : TId, YjsArrInvariant (docm_get m t)) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ applied -> ti ∈ pool) ->
  is_history (A := A) (P := P) γh -∗ own_client_history γh c h -∗
  is_pool_certified γh pool ={E}=∗
    own_client_history γh c h ∗ ⌜pool_ready_total m pool applied⌝.
Proof.
  iIntros (HE Hcoh Hinvs Happsub) "#Hinv Hown #Hcertsin".
  iInv "Hinv" as ">H" "Hclose". iNamed "H".
  iDestruct (hist_auth_elem_lookup with "HhistAuth Hown") as %HNc.
  iAssert (⌜∀ ti : TId * IntegrateInput (A := A), ti ∈ pool ->
             ops !! (in_id ti.2) = Some ((ti.1, OpInsert ti.2) : Op)⌝)%I as %Hlk.
  { iIntros (ti Hin).
    destruct (list_elem_of_lookup_1 _ _ Hin) as (i & Hi).
    iDestruct (big_sepL_lookup _ _ i with "Hcertsin") as "Hc"; [exact Hi |].
    iApply (ghost_map_lookup with "HopsAuth Hc"). }
  have Hbc : ∀ ti : TId * IntegrateInput (A := A), ti ∈ pool ->
      op_broadcast N (ti.1, OpInsert ti.2).
  { move=> ti Hin. destruct Hopscoh as [Hc1 _].
    have [_ Hreg] := Hc1 _ _ (Hlk ti Hin).
    exists (clientId (DocOp_id ((ti.1, OpInsert ti.2) : Op))). exact Hreg. }
  have Hrt := pool_ready_total_of_certs N c h m pool applied Hwf HNc Hcoh
                Hinvs Hbc Happsub.
  iMod ("Hclose" with "[HhistAuth HopsAuth]") as "_".
  { iNext. iExists _, _. iFrame "HhistAuth HopsAuth Hcerts".
    iPureIntro. split; [exact Hwf | exact Hopscoh]. }
  iModIntro. iFrame "Hown". iPureIntro. exact Hrt.
Qed.

(** [applyUpdate], the PUBLIC certificate spec (issue #40): the whole store
    state is ONE [own_store] before and after. The incoming batch carries its
    persistent certificates and its rooted-head witnesses; there is NO
    causal-order assumption, not even within the batch, and no state-vector
    tracking -- the heap drains the pending buffer plus the batch to the
    structural-dependency fixpoint. [pool_drain] names the applied list, the
    new pending buffer and the final model; the delivery's pure content is
    [ValidReplay applied m m'] (which determines [m']), every applied struct
    is foreign (a replica never receives its own insert back before minting
    the next one: per-author FIFO), and each applied struct yields one
    monotone content certificate [is_root_lb] at its root's full
    post-delivery item set. *)
Lemma wp_store__applyUpdate_certs (s_loc : loc) (sl : slice.t) (dq : dfrac)
    (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocM)
    (pend inputs : list (TId * IntegrateInput (A := A))) :
  (∀ (t : TId) x, x ∈ docm_get m t -> (Z.of_nat (clock (item_id x)) + 1 < 2^64)%Z) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ inputs ->
     (Z.of_nat (clock (in_id ti.2)) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ is_history (A := A) (P := P) γh ∗
      own_store s_loc γs γh c h m pend ∗
      own_update_structs sl dq inputs ∗
      is_pool_certified γh inputs ∗
      is_pool_rooted γs inputs }}}
    s_loc @! (go.PointerType yjs.store) @! "applyUpdate" #sl
  {{{ (applied rest : list (TId * IntegrateInput (A := A))) (m' : DocM),
      RET #();
      own_update_structs sl dq inputs ∗
      own_store s_loc γs γh c (h ++ (deliver_ev <$> applied)) m' rest ∗
      is_history_lb γh c (h ++ (deliver_ev <$> applied)) ∗
      ⌜pool_drain m (pend ++ inputs) = (applied, rest, m')⌝ ∗
      ⌜ValidReplay applied m m'⌝ ∗
      ⌜∀ ti : TId * IntegrateInput (A := A), ti ∈ applied ->
         clientId (in_id ti.2) ≠ c⌝ ∗
      ([∗ list] ti ∈ applied, ∃ nm : P, ⌜ti.1 = RootId nm⌝ ∗
         is_root_lb γs nm (list_to_set (docm_get m' ti.1))) }}}.
Proof using Type*.
  move=> Hnowrapm Hnowrapb.
  iIntros (Φ) "(#Hpkg & #Hishist & Hstore & Hupd & #Hcertsin & #Hrootsin) HΦ".
  iNamed "Hstore".
  destruct Hregcoh as (Hbindtypes & Hbindinj & Htypesbound & Hmtypes & Hmdom).
  iDestruct (types_arr_inv with "Htypes") as %Htsinv.
  iDestruct (types_repr_all with "Htypes") as %Hreprall.
  iDestruct (types_unit_all with "Htypes") as %Hunitall.
  iDestruct (types_cells_id_bounds with "Htypes") as %Hcellbnd.
  have Harrinv : ∀ t : TId, YjsArrInvariant (docm_get m t).
  { move=> t. destruct (docm_get m t) as [|x l] eqn:Hdg.
    - exact YjsArrInvariant_empty.
    - rewrite -Hdg.
      have Hne : docm_get m t ≠ [] by rewrite Hdg.
      destruct (Hmdom t Hne) as (nm & p & -> & Hbnm).
      destruct (Hbindtypes nm p Hbnm) as [ts Hts].
      rewrite (Hmtypes nm p ts Hbnm Hts). exact (Htsinv p ts Hts). }
  have Hnowrap : ∀ c0, c0 ∈ all_cells types -> (uint.Z (cell_clock c0) + 1 < 2^64)%Z.
  { move=> c0 Hc0.
    have Hc0m := Hc0. apply all_cells_elem_of in Hc0m.
    destruct Hc0m as (p & ts & Hts & Hcts).
    have Hitemmem : run_head c0 ∈ ty_arr ts.
    { rewrite (Hreprall p ts Hts).
      apply run_head_in_flatten; [exact Hcts |].
      exact (proj1 (Forall_forall _ _) (Hunitall p ts Hts) _ Hcts). }
    destruct (Htypesbound p (ex_intro _ ts Hts)) as [nm Hbnm].
    have Hdg : docm_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
    have Hmem : run_head c0 ∈ docm_get m (RootId nm) by rewrite Hdg.
    have [Hcb Hkb] := Hcellbnd c0 Hc0.
    have Hnw := Hnowrapm (RootId nm) (run_head c0) Hmem.
    rewrite /cell_clock. word. }
  have Hkb1c : ∀ ti : TId * IntegrateInput (A := A), ti ∈ pend ++ inputs ->
      (Z.of_nat (clock (in_id ti.2)) + 1 < 2^64)%Z.
  { move=> ti /elem_of_app [Hin | Hin];
      [exact (Hpendbnd ti Hin) | exact (Hnowrapb ti Hin)]. }
  (* the whole drained pool and its certificates *)
  iAssert (is_pool_certified γh (pend ++ inputs)) as "#Hcertpool".
  { rewrite /is_pool_certified big_sepL_app.
    iSplit; [iFrame "Hpendcert" | iFrame "Hcertsin"]. }
  iAssert (is_pool_rooted γs (pend ++ inputs)) as "#Hrootpool".
  { rewrite /is_pool_rooted big_sepL_app.
    iSplit; [iFrame "Hpendroot" | iFrame "Hrootsin"]. }
  iAssert (⌜∀ ti : TId * IntegrateInput (A := A), ti ∈ pend ++ inputs ->
      in_originId ti.2 = None -> in_rightOriginId ti.2 = None ->
      ∃ nm, ti.1 = RootId nm ∧ is_Some (bind !! nm)⌝)%I as %Hrooted0.
  { iIntros (ti Hin HoN HrN).
    iDestruct (big_sepL_elem_of _ _ ti Hin with "Hrootpool") as "Hri".
    rewrite /pool_item_rooted decide_True; last by split.
    iDestruct "Hri" as (nm) "[%Htieq Hroot]".
    iDestruct "Hroot" as (p) "Hbind".
    iDestruct (ghost_map_lookup with "HtypesAuth Hbind") as %Hb.
    iPureIntro. exists nm. split; [exact Htieq | by exists p]. }
  destruct (pool_drain m (pend ++ inputs)) as [[applied rest'] m'] eqn:Hdrainc.
  have Happsub := proj1 (pool_drain_subset m (pend ++ inputs) applied rest' m' Hdrainc).
  have Hrestsub := proj2 (pool_drain_subset m (pend ++ inputs) applied rest' m' Hdrainc).
  (* ghost first: the gate totality, then the batch delivery *)
  iApply wp_fupd.
  iApply fupd_wp.
  have HmaskN : ↑histN ⊆ (⊤ : coPset) by solve_ndisj.
  iMod (history_pool_ready_total γh c h m (pend ++ inputs) applied ⊤ HmaskN
          Hhcoh Harrinv Happsub with "Hishist Hhist Hcertpool") as "[Hhist %Hrtot]".
  iMod (history_deliver_pool γh c h m (pend ++ inputs) applied rest' m' ⊤ HmaskN
          Hdrainc Hhcoh with "Hishist Hhist Hcertpool")
    as "(Hhist & #Hlbnew & %Hvr & %Hcoh' & %Hnoc)".
  iModIntro.
  wp_apply (wp_store__applyUpdate s_loc items_mref types_mref sl pend_sl dq
              inputs pend applied rest' m m' types bind
              Hdrainc Hvr Hrtot Hbindtypes Hbindinj Htypesbound Hmtypes Hmdom
              Hrooted0 Hnowrap Hkb1c Hlocdup Hrangedisj
              with "[$Hupd $Hpendf $Hpend $Hitemsf $Hitemmap $Htypesf $Htypesmap $Htypes]").
  iIntros (pend_sl' types') "(Hupd & Hpendf & Hpend' & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes & %Hdom' & %Hmtypes' & %Hmdom' & %Hprov' & %Hlocdup' & %Hrangedisj')".
  have Hbindtypes' : ∀ nm p, bind !! nm = Some p -> is_Some (types' !! p).
  { move=> nm p Hb. apply elem_of_dom. rewrite Hdom'. apply elem_of_dom.
    exact (Hbindtypes nm p Hb). }
  have Htypesbound' : ∀ p, is_Some (types' !! p) -> ∃ nm, bind !! nm = Some p.
  { move=> p Hs. apply Htypesbound. apply elem_of_dom. rewrite -Hdom'.
    apply elem_of_dom. exact Hs. }
  (* grow the item-set authority to the new types and snapshot it *)
  have Hdomf : dom ((λ ts : type_state, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types')
             = dom ((λ ts : type_state, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types)
    by rewrite !dom_fmap_L Hdom'.
  have Hgrowf : ∀ p S S',
      ((λ ts : type_state, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types) !! p = Some S ->
      ((λ ts : type_state, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types') !! p = Some S' ->
      S ⊆ S'.
  { move=> p S S'. rewrite !lookup_fmap.
    destruct (types !! p) as [ts|] eqn:Hts; last done.
    destruct (types' !! p) as [ts'|] eqn:Hts'; last done.
    move=> [= <-] [= <-].
    destruct (Htypesbound p (ex_intro _ ts Hts)) as [nm Hbnm].
    have Hdg : docm_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
    have Hdg' : docm_get m' (RootId nm) = ty_arr ts' := Hmtypes' nm p ts' Hbnm Hts'.
    move=> x. rewrite !elem_of_list_to_set. move=> Hx.
    rewrite -Hdg'. apply (ValidReplay_mem applied m m' Hvr (RootId nm)).
    by rewrite Hdg. }
  iMod (auth_gmap_gset_grow_snap γs.(sn_seq) _ _ Hdomf Hgrowf with "Hseq")
    as "[Hseq #Hsnap]".
  (* per-applied bindings: the applied item landed in its (hence bound) root *)
  have Happbnd : ∀ ti : TId * IntegrateInput (A := A), ti ∈ applied ->
      ∃ nm p, ti.1 = RootId nm ∧ bind !! nm = Some p.
  { move=> ti Hin.
    have Hne := ValidReplay_applied_nonempty applied m m' Hvr ti Hin.
    destruct (Hmdom' ti.1 Hne) as (nm & p & Heq & Hb). by exists nm, p. }
  iAssert ([∗ list] ti ∈ applied, ∃ nm : P, ⌜ti.1 = RootId nm⌝ ∗
             is_root_lb γs nm (list_to_set (docm_get m' ti.1)))%I as "#Hlbs".
  { iApply big_sepL_intro.
    iIntros "!#" (i ti Hi).
    destruct (Happbnd ti (list_elem_of_lookup_2 _ _ _ Hi)) as (nm & p & Htieq & Hbnm).
    destruct (Hbindtypes' nm p Hbnm) as [ts' Hts'].
    have Hdg' : docm_get m' (RootId nm) = ty_arr ts' := Hmtypes' nm p ts' Hbnm Hts'.
    iDestruct (big_sepM_lookup _ _ nm p Hbnm with "Hbinds") as "#Hbind".
    iExists nm. iSplit; [done |].
    iExists p. iFrame "Hbind".
    rewrite /is_type_lb Htieq Hdg'.
    iApply (auth_gmap_gset_frag_lookup with "Hsnap").
    rewrite lookup_fmap Hts' //. }
  (* the leftover pool re-certifies the new pending buffer *)
  iAssert (is_pool_certified γh rest') as "#Hpendcert'".
  { rewrite /is_pool_certified. iApply big_sepL_intro.
    iIntros "!#" (i ti Hi).
    iApply (big_sepL_elem_of _ _ ti (Hrestsub ti (list_elem_of_lookup_2 _ _ _ Hi))
              with "Hcertpool"). }
  iAssert (is_pool_rooted γs rest') as "#Hpendroot'".
  { rewrite /is_pool_rooted. iApply big_sepL_intro.
    iIntros "!#" (i ti Hi).
    iApply (big_sepL_elem_of _ _ ti (Hrestsub ti (list_elem_of_lookup_2 _ _ _ Hi))
              with "Hrootpool"). }
  have Hpendbnd' : ∀ ti : TId * IntegrateInput (A := A), ti ∈ rest' ->
      (Z.of_nat (clock (in_id ti.2)) + 1 < 2^64)%Z.
  { move=> ti Hin. exact (Hkb1c ti (Hrestsub ti Hin)). }
  (* the counter clause survives: nothing applied is ours *)
  have Hctr' : ∀ (t : TId) x, x ∈ docm_get m' t -> clientId (item_id x) = c ->
      (clock (item_id x) < uint.nat k)%nat.
  { move=> t x Hx Hcx.
    destruct (ValidReplay_prov applied m m' Hvr t x Hx) as [Hold | (i & ti & Hi & Hid)].
    - exact (Hctr t x Hold Hcx).
    - exfalso. apply (Hnoc ti (list_elem_of_lookup_2 _ _ _ Hi)). by rewrite -Hid. }
  iModIntro. iApply ("HΦ" $! applied rest' m').
  iFrame "Hupd". iFrame "Hlbnew". iFrame "Hlbs".
  iSplitL "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend' Hseq Htypes HtypesAuth Hhist";
    last by (iPureIntro; split_and!; [done | exact Hvr | exact Hnoc]).
  iExists client, k, items_mref, types_mref, dset, pend_sl', types', bind.
  iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend' Hseq Htypes HtypesAuth Hbinds Hhist".
  iFrame "Hpendcert' Hpendroot'".
  iPureIntro. split_and!.
  - exact Hclientc.
  - exact Hpendbnd'.
  - rewrite /doc_registry_coh.
    split_and!; [exact Hbindtypes' | exact Hbindinj | exact Htypesbound'
                 | exact Hmtypes' | exact Hmdom'].
  - exact Hcoh'.
  - exact Hctr'.
  - exact Hlocdup'.
  - exact Hrangedisj'.
Qed.

End store_update.
