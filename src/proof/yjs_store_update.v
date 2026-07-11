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

(* ===== apply_update: store.applyUpdate (insert-only, decoded, causal-order ==
   subset). The integrate loop of y-octo's Doc::apply_update, refining a valid
   causal replay of the pure model. See issue #40 for the order-independent /
   ghost-global-history end state (which will also add the public entry). *)

(** A decoded parent name is either absent (Parent::None: borrow from a
    neighbour in [store.repair]) or a read-only string cell (Parent::String).
    Mirrors [is_origin_id]. *)
Definition is_parent_name (p : loc) (opn : option go_string) : iProp Σ :=
  match opn with
  | None => ⌜p = null⌝
  | Some nm => ⌜p ≠ null⌝ ∗ p ↦□ nm
  end.

Global Instance is_parent_name_persistent p opn : Persistent (is_parent_name p opn).
Proof. rewrite /is_parent_name. by destruct opn; apply _. Qed.

(** [is_update_item uiv ti]: the decoded heap struct [uiv] (a [updateItem])
    translates to the model doc-op payload [ti = (tid, input)] -- its id /
    content / both origin pointers map across (origins via [is_origin_id],
    persistent), its content is a single char, and its decoded parent name
    (when present) is the name of the root type [tid] (issue #49; when absent
    the batch-level well-formedness pins [tid] through the origins). *)
Definition is_update_item (uiv : yjs.updateItem.t)
    (ti : TId * IntegrateInput (A := A)) : iProp Σ :=
  ∃ (oleft oright : option yjs.id.t) (opn : option go_string),
    "HisL" ∷ is_origin_id uiv.(yjs.updateItem.originLeftId') oleft ∗
    "HisR" ∷ is_origin_id uiv.(yjs.updateItem.originRightId') oright ∗
    "HisPN" ∷ is_parent_name uiv.(yjs.updateItem.parentName') opn ∗
    "%Hin_l" ∷ ⌜(toYjsId <$> oleft) = in_originId ti.2⌝ ∗
    "%Hin_r" ∷ ⌜(toYjsId <$> oright) = in_rightOriginId ti.2⌝ ∗
    "%Hin_id" ∷ ⌜toYjsId uiv.(yjs.updateItem.id') = in_id ti.2⌝ ∗
    "%Hin_c" ∷ ⌜uiv.(yjs.updateItem.content') = in_content ti.2⌝ ∗
    "%Hclen" ∷ ⌜length uiv.(yjs.updateItem.content') = 1%nat⌝ ∗
    "%Htid" ∷ ⌜∀ nm, opn = Some nm -> ti.1 = RootId nm⌝ ∗
    "%Hborrow" ∷ ⌜opn = None -> in_originId ti.2 ≠ None ∨ in_rightOriginId ti.2 ≠ None⌝.

#[global] Instance is_update_item_persistent uiv ti : Persistent (is_update_item uiv ti).
Proof. rewrite /is_update_item. apply _. Qed.

(** [own_update sl dq inputs]: the heap slice of decoded structs at [sl] (Go
    [Update.structs]) abstracts to the model list [inputs] of type-tagged
    integrate inputs. Owns the backing array (+ cap) at [dq] — [applyUpdate]
    only reads it, so any fraction works — and, per element, the persistent
    [is_update_item]. *)
Definition own_update (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A))) : iProp Σ :=
  ∃ (uivs : list yjs.updateItem.t),
    "Hsl" ∷ sl ↦*{dq} uivs ∗
    "Hcap" ∷ own_slice_cap yjs.updateItem.t sl dq ∗
    "Hitems" ∷ ([∗ list] uiv;ti ∈ uivs;inputs, is_update_item uiv ti).

(* ===== applyUpdate (doc-level, #49): store-wide node lookup ==============
   [store.repair] resolves a decoded struct's origins through the store-wide
   [GetNode] (per-client clock-sorted run lists + binary search) instead of
   walking one type's DLL. The heap cells backing the probes live in the
   per-type DLLs, so the lookup specs borrow single cells out of the
   document-wide big-sep (what [store_inv] holds as [Htypes]) via
   [types_cell_acc]. *)

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
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
    ∃ (iv : yjs.item.t),
      "%Hid" ∷ ⌜item_id (ic_item c) = toYjsId iv.(yjs.item.id')⌝ ∗
      "%Hcontlen" ∷ ⌜length (iv.(yjs.item.content').(yjs.content.content')) = 1%nat⌝ ∗
      "%Hpar" ∷ ⌜iv.(yjs.item.parent') = ic_parent c⌝ ∗
      "Hval" ∷ ic_loc c ↦ iv ∗
      "Hback" ∷ (ic_loc c ↦ iv -∗
        ([∗ map] parent ↦ ts ∈ types,
            own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
            ⌜YjsArrInvariant (ty_arr ts)⌝)).
Proof.
  move=> Hc. iIntros "Htypes".
  apply all_cells_elem_of in Hc. destruct Hc as (p & ts & Hp & Hcts).
  apply list_elem_of_lookup_1 in Hcts. destruct Hcts as [k Hk].
  iDestruct (big_sepM_lookup_acc _ _ p ts Hp with "Htypes") as "[[Hyt %Hinvp] Hrest]".
  iDestruct "Hyt" as (yt tl) "(Hparent & Hdll & %Hlen & %Hrepr & %Hcpar)".
  iDestruct (own_dll_acc (DfracOwn 1) (ty_cells ts) yt.(yjs.yType.start') tl k c Hk with "Hdll") as "Hacc".
  iNamed "Hacc".
  iExists iv.
  iFrame "Hcval".
  iSplitR; [iPureIntro; exact Hid |].
  iSplitR; [iPureIntro; exact Hcontlen |].
  iSplitR; [iPureIntro; exact Hpar |].
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
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
  ⌜∀ c, c ∈ all_cells types ->
     (Z.of_nat (clientId (item_id (ic_item c))) < 2^64)%Z ∧
     (Z.of_nat (clock (item_id (ic_item c))) < 2^64)%Z⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types,
      ⌜∀ c, c ∈ ty_cells ts ->
         (Z.of_nat (clientId (item_id (ic_item c))) < 2^64)%Z ∧
         (Z.of_nat (clock (item_id (ic_item c))) < 2^64)%Z⌝)%I
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
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
  ⌜∀ p ts, types !! p = Some ts -> YjsArrInvariant (ty_arr ts)⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types, ⌜YjsArrInvariant (ty_arr ts)⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "[_ %Hinv]". by iPureIntro. }
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
  (∀ c, c ∈ run -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
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
      ∃ c, ⌜run !! uint.nat i = Some c ∧ cell_clock c = clk⌝ }}}.
Proof using Type*.
  move=> Hsort Hmem Hnowrap Hk0 Hclk0.
  wp_start as "(Hsl & Htypes)".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  rewrite length_fmap in Hsllen Hsllen0.
  wp_auto.
  (* loop invariant: the window [lo, hi) contains every hit *)
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
    iDestruct (types_cell_acc types cmid Hcmemall with "Htypes") as "Hacc".
    iNamed "Hacc".
    wp_auto.
    have Hmcv : cell_clock cmid = iv.(yjs.item.id').(yjs.id.clock')
      by (rewrite /cell_clock Hid /toYjsId /=; word).
    wp_apply (wp_item__Len cmid.(ic_loc) (DfracOwn 1) iv with "[$Hval]"). iIntros "Hval".
    rewrite Hcontlen.
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
        iApply ("HΦ" $! mid). iFrame "Hsl Htypes".
        iExists cmid. iPureIntro. split; [exact Hcmid | exact Hclkeq].
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
  item_id (ic_item cw) = toYjsId idv ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "GetNode" #idv
  {{{ RET (#(ic_loc cw), #true);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}.
Proof using Type*.
  move=> Hcw Hcwid Hnowrap.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
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
  wp_apply (wp_getNodeIndex slk dq types (client_run types kc) idv.(yjs.id.clock') kw cw
              (client_run_sorted types kc)
              (fun c Hc => proj1 (proj1 (client_run_mem types kc c) Hc))
              (fun c Hc => Hnowrap c (proj1 (proj1 (client_run_mem types kc c) Hc)))
              Hkw Hclkw
              with "[$Hslice $Htypes]").
  iIntros (i) "(Hslice & Htypes & %Hires)".
  destruct Hires as (cres & Hcres & Hcresclk).
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
  have Hloceq : cres.(ic_loc) = cw.(ic_loc).
  { apply (Hclkloc cres cw (proj1 Hcresmem) Hcw).
    - rewrite (proj2 Hcresmem) Hcwcc //.
    - rewrite /cell_pr /= Hcresclk Hclkw //. }
  rewrite Hloceq.
  iApply "HΦ".
  iFrame "Hitemsf".
  iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
  iSplitL "Hmap Hruns".
  { iExists gm. iFrame "Hmap Hruns". iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
  iFrame "Htypes".
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
  | Some oid, Some c => c ∈ all_cells types /\ item_id (ic_item c) = oid
  | None, None => True
  | _, _ => False
  end ->
  match in_rightOriginId input, ocR with
  | Some oid, Some c => c ∈ all_cells types /\ item_id (ic_item c) = oid
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
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "repair" #item_l #pname
  {{{ RET #();
      own_linked_item item_l input p_t
        (match ocL with Some c => ic_loc c | None => null end)
        (match ocR with Some c => ic_loc c | None => null end) ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref dq bind ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}.
Proof using Type*.
  move=> HwL HwR Hwpar Hnowrap.
  iIntros (Φ) "(#Hpkg & Hlinked & #HisPN & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes) HΦ".
  iDestruct "Hlinked" as (iv oleft oright) "(Hraw & %Hfl & %Hfr & %Hfpar & %Hflags & %Hcontlen)".
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
    wp_apply (wp_store__GetNode s mref dq idvL types cL HcLmem (eq_trans HcLid eq_refl) Hnowrap
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
      wp_apply (wp_store__GetNode s mref dq idvR types cR HcRmem (eq_trans HcRid eq_refl) Hnowrap
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
      wp_apply (wp_store__GetNode s mref dq idvR types cR HcRmem (eq_trans HcRid eq_refl) Hnowrap
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
      ⌜YjsArrInvariant (ty_arr ts0)⌝) -∗
  ⌜cells_repr (ty_arr ts) (ty_cells ts) (ty_arr ts) ∧
   (∀ c, c ∈ ty_cells ts -> ic_parent c = p)⌝.
Proof.
  move=> Hp. iIntros "Htypes".
  iDestruct (big_sepM_lookup_acc _ _ p ts Hp with "Htypes") as "[[Hyt _] _]".
  iDestruct "Hyt" as (yt tl) "(_ & _ & %Hlen & %Hrepr & %Hcpar)".
  iPureIntro. by split.
Qed.

Lemma types_repr_all (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
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
  ∃ (c : ClientId) (h : list Ev) (m : DocM), own_store s_loc γs γh c h m.
Proof.
  iSplit.
  - iIntros "H". iNamed "H". iNamed "Hexcl". iNamed "Hro".
    iExists (uint.nat client), h, m.
    iExists client, k, items_mref, types_mref, dset, types, bind.
    iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hseq Htypes HtypesAuth Hbinds Hhist".
    iPureIntro. split_and!.
    + reflexivity.
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
  - iIntros "H". iDestruct "H" as (c h m) "H". iNamed "H". subst c.
    iDestruct (types_repr_all with "Htypes") as %Hreprall.
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
      have Hitemmem : ic_item c0 ∈ ty_arr ts.
      { rewrite (Hreprall p ts Hts). apply list_elem_of_fmap_2. exact Hcts. }
      have [Hcb Hkb] := Hcellbnd c0 Hc0.
      have Hceq : clientId (item_id (ic_item c0)) = uint.nat client.
      { move: Hcc. rewrite /cell_client. move=> Hcc.
        have Hz : uint.Z (W64 (clientId (item_id (ic_item c0)))) = uint.Z client
          by rewrite Hcc.
        word. }
      have Hlt := Hctrt p ts (ic_item c0) Hts Hitemmem Hceq.
      rewrite /cell_clock. word. }
    iExists client, k, items_mref, types_mref, dset, types, bind, h, m.
    iSplitR "Hseq Htypes"; last by iFrame "Hseq Htypes".
    iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset HtypesAuth Hbinds Hhist".
    iPureIntro. split_and!;
      [exact Hctrt | exact Hcellctr | exact Hbindtypes | exact Hbindinj
      | exact Htypesbound | exact Hhcoh | exact Hmtypes | exact Hmdom].
Qed.

(** [store.applyUpdate], doc-level (#49): integrate the decoded, type-tagged
    batch in list order, [repair]ing each struct against the whole store and
    integrating it into its OWN root type — a refinement of the doc-level
    [ValidReplay] from [m] to [m'].

    Restriction (issue #49 slice): every struct's target root must already be
    bound in the registry ([Hbatchbnd]) — the on-the-fly type creation of
    y-octo's update path (getOrCreateYType's miss branch growing
    [types]/[bind]/[m] mid-batch) is outside the verified subset for now.
    The two no-wrap hypotheses are the W64 seam: [getNodeIndex] computes
    [middleClock + 1] in [w64], so every probed clock (existing cells and the
    batch's own, which land in the pool mid-batch) must not sit at [2^64-1];
    the pure model's clocks are unbounded [nat]s, so this cannot come from the
    replay itself.

    This receiver-side [ValidReplay] spec is the INTERNAL composition lemma:
    [wp_store__applyUpdate_certs_aux] below obtains the [ValidReplay] from
    the ghost op history and invokes this proof verbatim, and the public
    [wp_store__applyUpdate_certs] wraps that in [own_store]. *)
Lemma wp_store__applyUpdate (s : loc) (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A)))
    (m m' : DocM) (types : gmap loc type_state) (bind : gmap P loc)
    (mref tref : loc) :
  ValidReplay inputs m m' ->
  (∀ nm p, bind !! nm = Some p -> is_Some (types !! p)) ->
  (∀ n1 n2 p, bind !! n1 = Some p -> bind !! n2 = Some p -> n1 = n2) ->
  (∀ nm p ts, bind !! nm = Some p -> types !! p = Some ts ->
     docm_get m (RootId nm) = ty_arr ts) ->
  (∀ i ti, inputs !! i = Some ti -> ∃ nm p, ti.1 = RootId nm /\ bind !! nm = Some p) ->
  (∀ (i : nat) (ti : TId * IntegrateInput (A := A)), inputs !! i = Some ti ->
     ∀ c0, c0 ∈ all_cells types -> cell_client c0 = W64 (clientId (in_id ti.2)) ->
        (uint.Z (cell_clock c0) < uint.Z (W64 (clock (in_id ti.2))))%Z) ->
  (∀ (i j : nat) (ti tj : TId * IntegrateInput (A := A)),
     inputs !! i = Some ti -> inputs !! j = Some tj ->
     (j < i)%nat -> W64 (clientId (in_id tj.2)) = W64 (clientId (in_id ti.2)) ->
        (uint.Z (W64 (clock (in_id tj.2))) < uint.Z (W64 (clock (in_id ti.2))))%Z) ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + 1 < 2^64)%Z) ->
  (∀ i ti, inputs !! i = Some ti -> (Z.of_nat (clock (in_id ti.2)) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ own_update sl dq inputs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "applyUpdate" #sl
  {{{ (types' : gmap loc type_state), RET #();
      own_update sl dq inputs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜dom types' = dom types⌝ ∗
      ⌜∀ nm p ts', bind !! nm = Some p -> types' !! p = Some ts' ->
         docm_get m' (RootId nm) = ty_arr ts'⌝ ∗
      ⌜∀ c, c ∈ all_cells types' -> c ∈ all_cells types ∨
         ∃ i ti, inputs !! i = Some ti /\
            cell_client c = W64 (clientId (in_id ti.2)) /\
            cell_clock c = W64 (clock (in_id ti.2))⌝ }}}.
Proof using Type*.
  move=> Hreplay Hbindtypes Hbindinj Hmtypes Hbatchbnd Hfresh Hcausal Hnowrap Hnowrapb.
  iIntros (Φ) "(#Hpkg & Hupd & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes) HΦ".
  iDestruct "Hupd" as (uivs) "(Hsl & Hcap & Hitems)".
  iDestruct (big_sepL2_length with "Hitems") as %Hlen_ui.
  wp_method_call. wp_call. wp_call. wp_auto.
  iDestruct "Hitems" as "#Hitems".
  (* loop invariant: [j] structs integrated, [typesj]/[mj] in step, the
     remainder still a valid replay to [m'] *)
  iAssert (∃ (j : nat) (typesj : gmap loc type_state) (mj : DocM),
    "Hi" ∷ i_ptr ↦ W64 j ∗ "Hs" ∷ s_ptr ↦ s ∗ "Hstructs" ∷ structs_ptr ↦ sl ∗
    "Hsl" ∷ sl ↦*{dq} uivs ∗
    "Hcap" ∷ own_slice_cap yjs.updateItem.t sl dq ∗
    "Hitemsf" ∷ (s .[(yjs.store.t), "items"]) ↦ mref ∗
    "Hitemmap" ∷ own_item_map mref (DfracOwn 1) typesj ∗
    "Htypesf" ∷ (s .[(yjs.store.t), "types"]) ↦ tref ∗
    "Htypesmap" ∷ own_map tref (DfracOwn 1) bind ∗
    "Htypes" ∷ ([∗ map] p ↦ ts ∈ typesj,
        own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
        ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
    "%Hreplayj" ∷ ⌜ValidReplay (drop j inputs) mj m'⌝ ∗
    "%Hjle" ∷ ⌜(j <= length uivs)%nat⌝ ∗
    "%Hdomj" ∷ ⌜dom typesj = dom types⌝ ∗
    "%Hmtypesj" ∷ ⌜∀ nm p ts, bind !! nm = Some p -> typesj !! p = Some ts ->
        docm_get mj (RootId nm) = ty_arr ts⌝ ∗
    "%Hbndj" ∷ ⌜∀ c0, c0 ∈ all_cells typesj ->
        ∀ i ti, (j <= i)%nat -> inputs !! i = Some ti ->
          cell_client c0 = W64 (clientId (in_id ti.2)) ->
          (uint.Z (cell_clock c0) < uint.Z (W64 (clock (in_id ti.2))))%Z⌝ ∗
    "%Hnowrapj" ∷ ⌜∀ c0, c0 ∈ all_cells typesj -> (uint.Z (cell_clock c0) + 1 < 2^64)%Z⌝ ∗
    "%Hprovj" ∷ ⌜∀ c0, c0 ∈ all_cells typesj -> c0 ∈ all_cells types ∨
        ∃ i ti, inputs !! i = Some ti /\
           cell_client c0 = W64 (clientId (in_id ti.2)) /\
           cell_clock c0 = W64 (clock (in_id ti.2))⌝)%I
    with "[i s structs Hsl Hcap Hitemsf Hitemmap Htypesf Htypesmap Htypes]" as "IH".
  { iExists 0%nat, types, m.
    iFrame "i s structs Hsl Hcap Hitemsf Hitemmap Htypesf Htypesmap Htypes".
    iPureIntro. split_and!.
    - rewrite drop_0. exact Hreplay.
    - lia.
    - reflexivity.
    - exact Hmtypes.
    - move=> c0 Hc0 i ti _ Hti Hcc. exact (Hfresh i ti Hti c0 Hc0 Hcc).
    - exact Hnowrap.
    - move=> c0 Hc0. by left. }
  wp_for "IH".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  case_bool_decide as Hcond.
  - (* loop body: repair + integrate the j-th struct *)
    have Hjlt : (j < length uivs)%nat by word.
    destruct (uivs !! j) as [uiv|] eqn:Huiv; [| apply lookup_ge_None in Huiv; lia].
    destruct (inputs !! j) as [[tj input]|] eqn:Hinput;
      [| apply lookup_ge_None in Hinput; lia].
    iDestruct (big_sepL2_lookup _ _ _ j with "Hitems") as "Hui"; [exact Huiv | exact Hinput |].
    iDestruct "Hui" as (oleft oright opn)
      "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hclen & %Htid & %Hborrow)".
    simpl in Hin_l, Hin_r, Hin_id, Hin_c, Htid, Hborrow.
    destruct (Hbatchbnd j (tj, input) Hinput) as (nmj & pj & Htjeq & Hbindj).
    simpl in Htjeq.
    have Htsj0 : is_Some (typesj !! pj).
    { apply elem_of_dom. rewrite Hdomj. apply elem_of_dom. exact (Hbindtypes nmj pj Hbindj). }
    destruct Htsj0 as [[cellsj arrj] Htsj].
    have Hdgj : docm_get mj (RootId nmj) = arrj := Hmtypesj nmj pj _ Hbindj Htsj.
    (* peel the head [VR_cons] off the remaining replay *)
    erewrite (drop_S inputs (tj, input) j Hinput) in Hreplayj.
    inversion Hreplayj as
      [| t0 input0 rest0 m0 arr2 mf nit Htoit Hvld Hmaxj Hglob Hintg Hrest Heqin [Heqi Heqa Heqf]];
      subst.
    set (arrj := docm_get mj (RootId nmj)) in *.
    iDestruct (types_arr_inv with "Htypes") as %Harrinvs.
    have Hinvj : YjsArrInvariant arrj := Harrinvs pj _ Htsj.
    have Hsi : setintegrate input arrj = Some arr2.
    { rewrite (setintegrate_eq_integrate input arrj nit Hinvj Htoit Hvld Hmaxj). exact Hintg. }
    destruct (integrate_finds input arrj arr2 Hintg) as (leftIdx & rightIdx & HfindL & HfindR).
    iDestruct (types_entry_pures typesj pj _ Htsj with "Htypes") as %[Hreprj Hcparj].
    simpl in Hreprj, Hcparj.
    (* uniform repair witnesses: present origins resolve inside this type's own
       cells (that is where [toItem] found them), so the borrow's parent IS
       [pj]; a named parent is [nmj]'s binding *)
    have Hwits : ∃ (ocL ocR : option item_cell),
      (match in_originId input, ocL with
       | Some oid, Some c => c ∈ all_cells typesj /\ item_id (ic_item c) = oid
       | None, None => True
       | _, _ => False
       end) /\
      (match in_rightOriginId input, ocR with
       | Some oid, Some c => c ∈ all_cells typesj /\ item_id (ic_item c) = oid
       | None, None => True
       | _, _ => False
       end) /\
      (match opn with
       | Some nm => bind !! nm = Some pj
       | None => match ocL with
                 | Some c => pj = ic_parent c
                 | None => match ocR with
                           | Some c => pj = ic_parent c
                           | None => False
                           end
                 end
       end) /\
      (match ocL with Some c => ic_loc c | None => null end) = node_loc cellsj leftIdx /\
      (match ocR with Some c => ic_loc c | None => null end) = node_loc cellsj rightIdx.
    { have Hcellsw : ∀ (kn : nat) (it : YjsItem A), arrj !! kn = Some it ->
        ∃ c, cellsj !! kn = Some c /\ ic_item c = it.
      { move=> kn it Hkn. rewrite /cells_repr in Hreprj.
        rewrite Hreprj list_lookup_fmap in Hkn.
        destruct (cellsj !! kn) as [c|] eqn:Hc; last done.
        injection Hkn as <-. by exists c. }
      have HocL : ∃ ocL,
        (match in_originId input, ocL with
         | Some oid, Some c => c ∈ all_cells typesj /\ item_id (ic_item c) = oid
         | None, None => True
         | _, _ => False
         end) /\
        (match ocL with Some c => ic_loc c | None => null end) = node_loc cellsj leftIdx /\
        (match ocL with Some c => ic_parent c = pj | None => True end).
      { destruct (in_originId input) as [oidL|] eqn:HoinL.
        - destruct (findLeftIdx_inv oidL arrj leftIdx HfindL) as (kn & it & -> & Hkn & HidL).
          destruct (Hcellsw kn it Hkn) as (cL & HcLk & HcLit).
          exists (Some cL). split_and!.
          + apply all_cells_elem_of. exists pj, (MkTypeState cellsj arrj).
            split; [exact Htsj | exact (list_elem_of_lookup_2 _ _ _ HcLk)].
          + by rewrite HcLit.
          + rewrite /node_loc decide_True; last lia. rewrite Nat2Z.id HcLk //.
          + exact (Hcparj cL (list_elem_of_lookup_2 _ _ _ HcLk)).
        - exists None. move: HfindL. rewrite /findLeftIdx. move=> [= <-].
          split_and!; [done | | done].
          rewrite /node_loc. case_decide; [lia | done]. }
      have HocR : ∃ ocR,
        (match in_rightOriginId input, ocR with
         | Some oid, Some c => c ∈ all_cells typesj /\ item_id (ic_item c) = oid
         | None, None => True
         | _, _ => False
         end) /\
        (match ocR with Some c => ic_loc c | None => null end) = node_loc cellsj rightIdx /\
        (match ocR with Some c => ic_parent c = pj | None => True end).
      { destruct (in_rightOriginId input) as [oidR|] eqn:HoinR.
        - destruct (findRightIdx_inv oidR arrj rightIdx HfindR) as (kn & it & -> & Hkn & HidR).
          destruct (Hcellsw kn it Hkn) as (cR & HcRk & HcRit).
          exists (Some cR). split_and!.
          + apply all_cells_elem_of. exists pj, (MkTypeState cellsj arrj).
            split; [exact Htsj | exact (list_elem_of_lookup_2 _ _ _ HcRk)].
          + by rewrite HcRit.
          + rewrite /node_loc decide_True; last lia. rewrite Nat2Z.id HcRk //.
          + exact (Hcparj cR (list_elem_of_lookup_2 _ _ _ HcRk)).
        - exists None. move: HfindR. rewrite /findRightIdx. move=> [= <-].
          split_and!; [done | | done].
          have Hlencells : length cellsj = length arrj.
          { rewrite /cells_repr in Hreprj. rewrite Hreprj length_fmap //. }
          rewrite /node_loc. case_decide; [| lia].
          rewrite lookup_ge_None_2 //; lia. }
      destruct HocL as (ocL & HwL & HlocL & HparL).
      destruct HocR as (ocR & HwR & HlocR & HparR).
      exists ocL, ocR. split_and!; try done.
      destruct opn as [nm|].
      - have Hnmeq : RootId nmj = RootId nm := Htid nm eq_refl.
        injection Hnmeq as <-. exact Hbindj.
      - destruct ocL as [cL|]; [by rewrite -(HparL) |].
        destruct ocR as [cR|]; [by rewrite -(HparR) |].
        destruct (Hborrow eq_refl) as [HL | HR].
        + move: HwL. by destruct (in_originId input).
        + move: HwR. by destruct (in_rightOriginId input). }
    destruct Hwits as (ocL & ocR & HwL & HwR & Hwpar & HlocLeq & HlocReq).
    wp_auto.
    rewrite decide_True; last by word.
    iDestruct (own_slice_elem_acc (sint.Z (W64 j)) uiv sl dq uivs with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z (W64 j))) with j by word. exact Huiv. }
    wp_auto.
    have Huiv2 : uivs !! sint.nat (W64 j) = Some uiv
      by (replace (sint.nat (W64 j)) with j by word; exact Huiv).
    iDestruct ("Hgive" $! uiv with "Hel") as "Hsl".
    iEval (rewrite (list_insert_id _ _ _ Huiv2)) in "Hsl".
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
        | reflexivity | reflexivity | reflexivity | reflexivity | exact Hclen]. }
    wp_apply (wp_store__repair s mref tref itv (uiv.(yjs.updateItem.parentName'))
                (DfracOwn 1) input opn typesj bind ocL ocR pj
                HwL HwR Hwpar Hnowrapj
                with "[$Hfresh $HisPN $Hitemsf $Hitemmap $Htypesf $Htypesmap $Htypes]").
    iIntros "(Hlinked & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes)".
    iEval (rewrite HlocLeq HlocReq) in "Hlinked".
    wp_auto.
    have Hidnit : item_id nit = in_id input := commutativity.toItem_id input arrj nit Htoit.
    have Hgmaxj : ∀ c0, c0 ∈ all_cells typesj → cell_client c0 = W64 (clientId (item_id nit)) →
                    (uint.Z (cell_clock c0) < uint.Z (W64 (clock (item_id nit))))%Z.
    { intros c0 Hc0 Hcc0. rewrite Hidnit in Hcc0 |- *.
      exact (Hbndj c0 Hc0 j (RootId nmj, input) ltac:(lia) Hinput Hcc0). }
    iDestruct (big_sepM_delete _ _ pj _ Htsj with "Htypes") as "[[Hyt _] Htypesrest]".
    wp_apply (wp_Store__Integrate_nil s pj itv arrj input nit cellsj typesj mref leftIdx rightIdx
                Hinvj Htoit Hvld Hmaxj HfindL HfindR Htsj Hgmaxj
                with "[$Hyt $Hlinked $Hitemsf $Hitemmap]").
    iIntros (arr2' iidx2 cells'' c2)
      "(%Hile2 & %Harr2eq & %Hinv2 & Htext2 & Hitemsf & Hitemmap & %Hperm2 & %Hsi2 & %Hnode2)".
    rewrite Hsi2 in Hsi. injection Hsi as Harr22. subst arr2'.
    destruct Hnode2 as (idx2 & Hsplice2 & Harrsp2 & Hc2look & Hc2loc & Hc2id).
    (* the pool grows by exactly [c2] *)
    have Hac_step : all_cells (<[pj := MkTypeState cells'' arr2]> typesj)
                  ≡ₚ all_cells typesj ++ [c2]
      by apply (all_cells_insert_snoc typesj pj cellsj arrj cells'' arr2 c2 Htsj Hperm2).
    have Hcc2 : cell_client c2 = W64 (clientId (in_id input))
      by rewrite /cell_client Hc2id Hidnit //.
    have Hclk2 : cell_clock c2 = W64 (clock (in_id input))
      by rewrite /cell_clock Hc2id Hidnit //.
    (* rebuild the per-type big-sep over the grown map *)
    iAssert ([∗ map] p ↦ ts ∈ <[pj := MkTypeState cells'' arr2]> typesj,
        own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
        ⌜YjsArrInvariant (ty_arr ts)⌝)%I
      with "[Htext2 Htypesrest]" as "Htypes".
    { rewrite -insert_delete_eq.
      rewrite big_sepM_insert; last apply lookup_delete_eq.
      iFrame "Htypesrest". simpl. rewrite Harr22. iFrame "Htext2".
      iPureIntro. rewrite -Harr22. exact Hinv2. }
    wp_auto. wp_for_post.
    iFrame "HΦ".
    iExists (S j), (<[pj := MkTypeState cells'' arr2]> typesj), (<[RootId nmj := arr2]> mj).
    replace (W64 (S j)) with (word.add (W64 j) (W64 1)) by word.
    iEval (rewrite Harr22) in "Hitemmap".
    iFrame "Hi Hs Hstructs Hsl Hcap Hitemsf Hitemmap Htypesf Htypesmap Htypes".
    iPureIntro. split_and!.
    + exact Hrest.
    + lia.
    + rewrite dom_insert_lookup_L; [exact Hdomj | eauto].
    + (* per-name coherence after the splice *)
      move=> nm p ts Hbnm.
      destruct (decide (p = pj)) as [-> | Hne].
      * have Hnmj : nm = nmj := Hbindinj nm nmj pj Hbnm Hbindj.
        subst nm. rewrite lookup_insert_eq. move=> [= <-].
        rewrite docm_get_insert_eq //.
      * rewrite lookup_insert_ne; last congruence.
        move=> Hts.
        have Hnenm : RootId nm ≠ RootId nmj.
        { move=> [= Heqnm]. subst nm. apply Hne.
          have : Some p = Some pj by rewrite -Hbnm -Hbindj //.
          by move=> [=]. }
        rewrite docm_get_insert_ne //.
        exact (Hmtypesj nm p ts Hbnm Hts).
    + (* freshness of the remaining batch against the grown pool *)
      move=> c0 Hc0 i ti Hile' Hinput' Hcc0.
      rewrite Hac_step in Hc0. apply elem_of_app in Hc0 as [Hold | Hnew].
      * exact (Hbndj c0 Hold i ti ltac:(lia) Hinput' Hcc0).
      * apply list_elem_of_singleton in Hnew as ->.
        rewrite Hclk2.
        exact (Hcausal i j ti (RootId nmj, input) Hinput' Hinput ltac:(lia)
                 (eq_trans (eq_sym Hcc2) Hcc0)).
    + (* no-wrap for the grown pool *)
      move=> c0 Hc0.
      rewrite Hac_step in Hc0. apply elem_of_app in Hc0 as [Hold | Hnew].
      * exact (Hnowrapj c0 Hold).
      * apply list_elem_of_singleton in Hnew as ->.
        rewrite Hclk2.
        have := Hnowrapb j (RootId nmj, input) Hinput. simpl. word.
    + (* provenance *)
      move=> c0 Hc0.
      rewrite Hac_step in Hc0. apply elem_of_app in Hc0 as [Hold | Hnew].
      * exact (Hprovj c0 Hold).
      * apply list_elem_of_singleton in Hnew as ->.
        right. exists j, (RootId nmj, input). split_and!; [exact Hinput | exact Hcc2 | exact Hclk2].
  - (* loop exit: the whole batch is integrated, [mj = m'] *)
    have Hjeq : (j = length uivs)%nat by word.
    rewrite Hjeq Hlen_ui drop_all in Hreplayj.
    inversion Hreplayj; subst.
    wp_auto.
    iApply ("HΦ" $! typesj).
    iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
    iSplitL "Hsl Hcap".
    { iExists uivs. iFrame "Hsl Hcap Hitems". }
    iPureIntro. split_and!; [exact Hdomj | exact Hmtypesj | exact Hprovj].
Qed.

(** The decoded batch's ids round-trip through the heap's [w64] id fields
    ([is_update_item]), so both components are bounded by [2^64] — the glue
    that turns the model-level (nat) clock facts of a [ValidReplay] into the
    W64-level side conditions of [wp_store__applyUpdate]. *)
Lemma own_update_id_bounds (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A))) :
  own_update sl dq inputs -∗
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
      "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hclen & %Htid & %Hborrow)".
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

(** INTERNAL certificate lemma (field-level): the receiver-side [ValidReplay]
    precondition of [wp_store__applyUpdate] is replaced by the sender-side op
    certificates plus the id-level coverage [batch_ok] (what y-octo's
    UpdateIterator establishes with the state vector). The proof advances the
    ghost history up front ([history_deliver_batch], which yields the
    doc-level [ValidReplay] before any code runs) and then invokes the
    heap-level loop proof verbatim.

    The batch's W64-level freshness/order side conditions are derived from
    the replay itself ([ValidReplay_arr_fresh] / [ValidReplay_batch_causal],
    id components bounded via [own_update_id_bounds] / the DLL pins),
    including the freshness against OTHER types' cells: the doc-level
    [ValidReplay] carries doc-GLOBAL per-step freshness, and the registry
    ties every type to its entry of [m]. Only the [2^64-1] no-wrap seam
    remains hypothetical (see [wp_store__applyUpdate]).

    The public spec is [wp_store__applyUpdate_certs] below, which wraps this
    lemma's raw footprint (struct fields, [types]/[bind] maps) in
    [own_store] and its raw pure post in [ValidReplay] + [is_root_lb]
    certificates. *)
Lemma wp_store__applyUpdate_certs_aux (s : loc) (sl : slice.t) (dq : dfrac)
    (γh : history_names) (c : ClientId) (h : list Ev)
    (inputs : list (TId * IntegrateInput (A := A))) (Ds : list (gset YjsId))
    (m : DocM) (types : gmap loc type_state) (bind : gmap P loc)
    (mref tref : loc) :
  batch_ok h inputs Ds ->
  history_state_coh h m ->
  doc_registry_coh m bind types ->
  (∀ i ti, inputs !! i = Some ti -> ∃ nm p, ti.1 = RootId nm /\ bind !! nm = Some p) ->
  (∀ c0, c0 ∈ all_cells types -> (uint.Z (cell_clock c0) + 1 < 2^64)%Z) ->
  (∀ i ti, inputs !! i = Some ti -> (Z.of_nat (clock (in_id ti.2)) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ is_history (A := A) (P := P) γh ∗
      own_client_history γh c h ∗
      ([∗ list] ti;D ∈ inputs;Ds, is_op_cert γh (ti.1, OpInsert ti.2) D) ∗
      own_update sl dq inputs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "applyUpdate" #sl
  {{{ (types' : gmap loc type_state) (m' : DocM), RET #();
      own_update sl dq inputs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      own_client_history γh c (h ++ (deliver_ev <$> inputs)) ∗
      is_history_lb γh c (h ++ (deliver_ev <$> inputs)) ∗
      ⌜history_state_coh (h ++ (deliver_ev <$> inputs)) m'⌝ ∗
      ⌜doc_registry_coh m' bind types'⌝ ∗
      ⌜dom types' = dom types⌝ ∗
      ⌜ValidReplay inputs m m'⌝ ∗
      ⌜∀ (i : nat) (ti : TId * IntegrateInput (A := A)),
         inputs !! i = Some ti -> clientId (in_id ti.2) ≠ c⌝ ∗
      ⌜∀ c0, c0 ∈ all_cells types' -> c0 ∈ all_cells types ∨
         ∃ i ti, inputs !! i = Some ti /\
            cell_client c0 = W64 (clientId (in_id ti.2)) /\
            cell_clock c0 = W64 (clock (in_id ti.2))⌝ }}}.
Proof using Type*.
  move=> Hbatch Hcoh Hcohreg Hbatchbnd Hnowrap Hnowrapb.
  destruct Hcohreg as (Hbindtypes & Hbindinj & Htypesbound & Hmtypes & Hmdom).
  iIntros (Φ) "(#Hpkg & #Hhist & Hown & #Hcerts & Hupd & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes) HΦ".
  iDestruct (types_arr_inv with "Htypes") as %Htsinv.
  iDestruct (types_repr_all with "Htypes") as %Hreprall.
  iDestruct (types_cells_id_bounds with "Htypes") as %Hcellbnd.
  iDestruct (own_update_id_bounds with "Hupd") as %Hidbnd.
  have Harrinv : ∀ t : TId, YjsArrInvariant (docm_get m t).
  { move=> t. destruct (docm_get m t) as [|x l] eqn:Hdg.
    - exact YjsArrInvariant_empty.
    - rewrite -Hdg.
      have Hne : docm_get m t ≠ [] by rewrite Hdg.
      destruct (Hmdom t Hne) as (nm & p & -> & Hbnm).
      destruct (Hbindtypes nm p Hbnm) as [ts Hts].
      rewrite (Hmtypes nm p ts Hbnm Hts). exact (Htsinv p ts Hts). }
  (* ghost first: deliver the batch, obtaining the ValidReplay *)
  iApply fupd_wp.
  have HmaskN : ↑histN ⊆ (⊤ : coPset) by solve_ndisj.
  iMod (history_deliver_batch γh c h m inputs Ds ⊤ HmaskN Hbatch Hcoh Harrinv
          with "Hhist Hown Hcerts") as (m') "(Hown & #Hlbnew & %Hvr & %Hcoh' & %Hnoc)".
  iModIntro.
  (* the W64-level freshness of the batch against ALL cells *)
  have Hfresh : ∀ (i : nat) (ti : TId * IntegrateInput (A := A)), inputs !! i = Some ti →
     ∀ c0, c0 ∈ all_cells types → cell_client c0 = W64 (clientId (in_id ti.2)) →
        (uint.Z (cell_clock c0) < uint.Z (W64 (clock (in_id ti.2))))%Z.
  { move=> i ti Hi c0 Hc0 Hcc.
    have Hc0m := Hc0.
    apply all_cells_elem_of in Hc0m. destruct Hc0m as (p & ts & Hts & Hcts).
    have Hitemmem : ic_item c0 ∈ ty_arr ts.
    { rewrite (Hreprall p ts Hts). apply list_elem_of_fmap_2. exact Hcts. }
    destruct (Htypesbound p (ex_intro _ ts Hts)) as [nm Hbnm].
    have Hdg : docm_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
    have Hmem : ic_item c0 ∈ docm_get m (RootId nm) by rewrite Hdg.
    have [Hcb Hkb] := Hcellbnd c0 Hc0.
    have [Hicb Hikb] := Hidbnd i ti Hi.
    have Hceq : clientId (item_id (ic_item c0)) = clientId (in_id ti.2).
    { move: Hcc. rewrite /cell_client. move=> Hcc.
      have Hz : uint.Z (W64 (clientId (item_id (ic_item c0))))
              = uint.Z (W64 (clientId (in_id ti.2))) by rewrite Hcc.
      word. }
    have Hlt := ValidReplay_arr_fresh inputs m m' Hvr i ti Hi (RootId nm) (ic_item c0) Hmem Hceq.
    rewrite /cell_clock. word. }
  (* the W64-level intra-batch causal order *)
  have Hcausal : ∀ (i j : nat) (ti tj : TId * IntegrateInput (A := A)),
     inputs !! i = Some ti → inputs !! j = Some tj →
     (j < i)%nat → W64 (clientId (in_id tj.2)) = W64 (clientId (in_id ti.2)) →
        (uint.Z (W64 (clock (in_id tj.2))) < uint.Z (W64 (clock (in_id ti.2))))%Z.
  { move=> i j ti tj Hi Hj Hji Hcc.
    have [Hicbi Hikbi] := Hidbnd i ti Hi.
    have [Hicbj Hikbj] := Hidbnd j tj Hj.
    have Hceq : clientId (in_id tj.2) = clientId (in_id ti.2).
    { have Hz : uint.Z (W64 (clientId (in_id tj.2)))
              = uint.Z (W64 (clientId (in_id ti.2))) by rewrite Hcc.
      word. }
    have Hlt := ValidReplay_batch_causal inputs m m' Hvr i j ti tj Hi Hj Hji Hceq.
    word. }
  wp_apply (wp_store__applyUpdate s sl dq inputs m m' types bind mref tref
              Hvr Hbindtypes Hbindinj Hmtypes Hbatchbnd Hfresh Hcausal Hnowrap Hnowrapb
              with "[$Hupd $Hitemsf $Hitemmap $Htypesf $Htypesmap $Htypes]").
  iIntros (types') "(Hupd & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes & %Hdom' & %Hmtypes' & %Hprov')".
  iApply ("HΦ" $! types' m').
  iFrame "Hupd Hitemsf Hitemmap Htypesf Htypesmap Htypes Hown Hlbnew".
  (* re-package [doc_registry_coh] for [m']/[types']: [bind] is unchanged and
     [dom types' = dom types], so the structural halves transfer; [Hmtypes']
     gives model agreement, and off-batch types are untouched by the replay. *)
  have Hbindtypes' : ∀ nm p, bind !! nm = Some p -> is_Some (types' !! p).
  { move=> nm p Hb. apply elem_of_dom. rewrite Hdom'. apply elem_of_dom.
    exact (Hbindtypes nm p Hb). }
  have Htypesbound' : ∀ p, is_Some (types' !! p) -> ∃ nm, bind !! nm = Some p.
  { move=> p Hs. apply Htypesbound. apply elem_of_dom. rewrite -Hdom'.
    apply elem_of_dom. exact Hs. }
  have Hmdom' : ∀ t, docm_get m' t ≠ [] -> ∃ nm p, t = RootId nm /\ bind !! nm = Some p.
  { move=> t Hne.
    destruct (decide (t ∈ ((fun ti : TId * IntegrateInput (A := A) => ti.1) <$> inputs))) as [Hin | Hnin].
    - apply list_elem_of_fmap in Hin. destruct Hin as (ti & -> & Htiin).
      apply list_elem_of_lookup_1 in Htiin. destruct Htiin as [i Hi].
      exact (Hbatchbnd i ti Hi).
    - have Hoff : ∀ i ti, inputs !! i = Some ti -> ti.1 ≠ t.
      { move=> i ti Hi Heq. apply Hnin. rewrite -Heq.
        apply list_elem_of_fmap_2. exact (list_elem_of_lookup_2 _ _ _ Hi). }
      rewrite (ValidReplay_docm_get_off inputs m m' t Hvr Hoff) in Hne.
      exact (Hmdom t Hne). }
  iPureIntro. split_and!.
  - exact Hcoh'.
  - rewrite /doc_registry_coh. split_and!;
      [exact Hbindtypes' | exact Hbindinj | exact Htypesbound' | exact Hmtypes' | exact Hmdom'].
  - exact Hdom'.
  - exact Hvr.
  - exact Hnoc.
  - exact Hprov'.
Qed.

(** [applyUpdate], the PUBLIC certificate spec (issues #42/#49): the whole
    store state is ONE [own_store] before and after, at models [(c, h, m)]
    and [(c, h ++ delivers, m')]. The batch comes with its persistent
    certificates ([is_certified_batch], covering sets hidden) and one
    registration witness per target root ([is_root], replacing the raw
    registry-lookup hypothesis). The pure post is the doc-level replay
    [ValidReplay inputs m m'], which determines [m']; the resource post
    additionally hands back one monotone content certificate per input:
    [is_root_lb] at the root's full post-delivery item set, a persistent
    fragment of the grow-only item-set authority (which this spec, unlike
    the internal lemma, also advances, so a lock-holding caller can rebuild
    [store_inv] via [store_inv_own_store]).

    The only pure preconditions left are the [2^64-1] no-wrap seam, now
    stated over the model [m] (see [wp_store__applyUpdate]). *)
Lemma wp_store__applyUpdate_certs (s : loc) (sl : slice.t) (dq : dfrac)
    (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocM)
    (inputs : list (TId * IntegrateInput (A := A))) :
  (∀ (t : TId) x, x ∈ docm_get m t -> (Z.of_nat (clock (item_id x)) + 1 < 2^64)%Z) ->
  (∀ (i : nat) (ti : TId * IntegrateInput (A := A)),
     inputs !! i = Some ti -> (Z.of_nat (clock (in_id ti.2)) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ is_history (A := A) (P := P) γh ∗
      own_store s γs γh c h m ∗
      own_update sl dq inputs ∗
      is_certified_batch γh h inputs ∗
      ([∗ list] ti ∈ inputs, ∃ nm : P, ⌜ti.1 = RootId nm⌝ ∗ is_root γs nm) }}}
    s @! (go.PointerType yjs.store) @! "applyUpdate" #sl
  {{{ (m' : DocM), RET #();
      own_store s γs γh c (h ++ (deliver_ev <$> inputs)) m' ∗
      own_update sl dq inputs ∗
      ⌜ValidReplay inputs m m'⌝ ∗
      is_history_lb γh c (h ++ (deliver_ev <$> inputs)) ∗
      ([∗ list] ti ∈ inputs, ∃ nm : P, ⌜ti.1 = RootId nm⌝ ∗
         is_root_lb γs nm (list_to_set (docm_get m' ti.1))) }}}.
Proof using Type*.
  move=> Hnowrapm Hnowrapb.
  iIntros (Φ) "(#Hpkg & #Hishist & Hstore & Hupd & #Hcertb & #Hroots) HΦ".
  iNamed "Hstore".
  iDestruct "Hcertb" as (Ds) "[%Hbatch #Hcerts]".
  (* recover the raw registry-lookup facts the internal lemma wants *)
  iAssert (⌜∀ (i : nat) (ti : TId * IntegrateInput (A := A)),
      inputs !! i = Some ti -> ∃ nm p, ti.1 = RootId nm /\ bind !! nm = Some p⌝)%I
    as %Hbatchbnd.
  { iIntros (i ti Hi).
    iDestruct (big_sepL_lookup _ _ i ti Hi with "Hroots") as (nm) "[%Htieq Hroot]".
    iDestruct "Hroot" as (p) "Hbind".
    iDestruct (ghost_map_lookup with "HtypesAuth Hbind") as %Hb.
    iPureIntro. by exists nm, p. }
  (* the cell-level no-wrap seam from the model-level one *)
  iDestruct (types_repr_all with "Htypes") as %Hreprall.
  iDestruct (types_cells_id_bounds with "Htypes") as %Hcellbnd.
  have Hregcohd := Hregcoh.
  destruct Hregcohd as (Hbindtypes & Hbindinj & Htypesbound & Hmtypes & Hmdom).
  have Hnowrap : ∀ c0, c0 ∈ all_cells types -> (uint.Z (cell_clock c0) + 1 < 2^64)%Z.
  { move=> c0 Hc0.
    have Hc0m := Hc0. apply all_cells_elem_of in Hc0m.
    destruct Hc0m as (p & ts & Hts & Hcts).
    have Hitemmem : ic_item c0 ∈ ty_arr ts.
    { rewrite (Hreprall p ts Hts). apply list_elem_of_fmap_2. exact Hcts. }
    destruct (Htypesbound p (ex_intro _ ts Hts)) as [nm Hbnm].
    have Hdg : docm_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
    have Hmem : ic_item c0 ∈ docm_get m (RootId nm) by rewrite Hdg.
    have [Hcb Hkb] := Hcellbnd c0 Hc0.
    have Hnw := Hnowrapm (RootId nm) (ic_item c0) Hmem.
    rewrite /cell_clock. word. }
  (* run the internal certificate lemma; keep a fupd after the call for the
     item-set authority update *)
  iApply wp_fupd.
  wp_apply (wp_store__applyUpdate_certs_aux s sl dq γh c h inputs Ds m types bind
              items_mref types_mref Hbatch Hhcoh Hregcoh Hbatchbnd Hnowrap Hnowrapb
              with "[$Hpkg $Hishist $Hhist $Hcerts $Hupd $Hitemsf $Hitemmap $Htypesf $Htypesmap $Htypes]").
  iIntros (types' m') "(Hupd & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes & Hhist & #Hlbnew & %Hcoh' & %Hregcoh' & %Hdom' & %Hvr & %Hnoc & %Hprov')".
  have Hregcohd' := Hregcoh'.
  destruct Hregcohd' as (Hbindtypes' & Hbindinj' & Htypesbound' & Hmtypes' & Hmdom').
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
    rewrite -Hdg'. apply (ValidReplay_mem inputs m m' Hvr (RootId nm)).
    by rewrite Hdg. }
  iMod (auth_gmap_gset_grow_snap γs.(sn_seq) _ _ Hdomf Hgrowf with "Hseq")
    as "[Hseq #Hsnap]".
  (* one content certificate per input, projected out of the snapshot; built
     under [big_sepL_intro]'s box, so only pure facts ([Hbatchbnd]) and
     persistent resources ([Hbinds], [Hsnap]) feed it *)
  iAssert ([∗ list] ti ∈ inputs, ∃ nm : P, ⌜ti.1 = RootId nm⌝ ∗
             is_root_lb γs nm (list_to_set (docm_get m' ti.1)))%I as "#Hlbs".
  { iApply big_sepL_intro.
    iIntros "!#" (i ti Hi).
    destruct (Hbatchbnd i ti Hi) as (nm & p & Htieq & Hbnm).
    destruct (Hbindtypes' nm p Hbnm) as [ts' Hts'].
    have Hdg' : docm_get m' (RootId nm) = ty_arr ts' := Hmtypes' nm p ts' Hbnm Hts'.
    iDestruct (big_sepM_lookup _ _ nm p Hbnm with "Hbinds") as "#Hbind".
    iExists nm. iSplit; [done |].
    iExists p. iFrame "Hbind".
    rewrite /is_type_lb Htieq Hdg'.
    iApply (auth_gmap_gset_frag_lookup with "Hsnap").
    rewrite lookup_fmap Hts' //. }
  (* the model-level counter clause survives: nothing in the batch is ours *)
  have Hctr' : ∀ (t : TId) x, x ∈ docm_get m' t -> clientId (item_id x) = c ->
      (clock (item_id x) < uint.nat k)%nat.
  { move=> t x Hx Hcx.
    destruct (ValidReplay_prov inputs m m' Hvr t x Hx) as [Hold | (i & ti & Hi & Hid)].
    - exact (Hctr t x Hold Hcx).
    - exfalso. apply (Hnoc i ti Hi). by rewrite -Hid. }
  iModIntro. iApply ("HΦ" $! m').
  iFrame "Hupd". iFrame "Hlbnew". iFrame "Hlbs".
  iSplitL "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hseq Htypes HtypesAuth Hhist";
    last by iPureIntro.
  iExists client, k, items_mref, types_mref, dset, types', bind.
  iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hseq Htypes HtypesAuth Hbinds Hhist".
  iPureIntro. split_and!; [exact Hclientc | exact Hregcoh' | exact Hcoh' | exact Hctr'].
Qed.

End store_update.
