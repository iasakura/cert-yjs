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
    "%Hulen" ∷ ⌜length uiv.(yjs.updateItem.content') = 1%nat⌝ ∗
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

(** Under the unit scaffold every doc item is a run head of some cell
    (the inverse of [run_head_in_flatten]; stage C1b's origin-item bridge). *)
Lemma unit_cells_arr_head (cells : list item_cell) (arr : list (YjsItem A)) (x : YjsItem A) :
  cells_repr arr cells arr ->
  Forall cell_unit cells ->
  x ∈ arr ->
  ∃ c, c ∈ cells ∧ x = run_head c.
Proof.
  rewrite /cells_repr. move=> Hrepr Hunit Hx.
  rewrite Hrepr (run_flatten_singletons cells Hunit) in Hx.
  apply list_elem_of_lookup_1 in Hx. destruct Hx as [i Hx].
  rewrite list_lookup_fmap in Hx.
  destruct (cells !! i) as [c|] eqn:Hc; last done.
  injection Hx as Heq. exists c.
  split; [by eapply list_elem_of_lookup_2 | by rewrite Heq].
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

(** [getNodeIndex], general covering-witness form (issue #28 stage D1): the
    witness cell [c0]'s run COVERS [clk] (it need not START there), so the
    search may end on a cell probed mid-run. The window argument needs
    index-wise clock-range disjointness of the run ([Hidisj], sourced from
    the pool's [cells_range_disjoint] + loc-NoDup at the call site): at most
    one run cell covers [clk], and the binary search corners it. Additive
    alongside the exact-hit form above, which dies with the unit scaffold at
    the C2 flip. *)
Lemma wp_getNodeIndex_range (sl : slice.t) (dq : dfrac) (types : gmap loc type_state)
    (run : list item_cell) (clk : w64) (k0 : nat) (c0 : item_cell) :
  StronglySorted cell_le run ->
  (∀ c, c ∈ run -> c ∈ all_cells types) ->
  (∀ c, c ∈ run -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  (∀ (k1 k2 : nat) (c1 c2 : item_cell),
     run !! k1 = Some c1 -> run !! k2 = Some c2 -> k1 ≠ k2 ->
     (uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)) <= uint.Z (cell_clock c2))%Z ∨
     (uint.Z (cell_clock c2) + Z.of_nat (length (ic_run c2)) <= uint.Z (cell_clock c1))%Z) ->
  run !! k0 = Some c0 ->
  (uint.Z (cell_clock c0) <= uint.Z clk)%Z ->
  (uint.Z clk < uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)))%Z ->
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
  move=> Hsort Hmem Hrunfits Hidisj Hk0 Hc0le Hc0lt.
  wp_start as "(Hsl & Htypes)".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  rewrite length_fmap in Hsllen Hsllen0.
  wp_auto.
  (* loop invariant: the window [lo, hi) contains every COVERING cell *)
  iAssert (∃ (lo hi : w64),
    "Hleft" ∷ left_ptr ↦ lo ∗ "Hright" ∷ right_ptr ↦ hi ∗
    "Hnodes" ∷ nodes_ptr ↦ sl ∗ "Hclock" ∷ clock_ptr ↦ clk ∗
    "Hsl" ∷ sl ↦*{dq} (ic_loc <$> run) ∗
    "Htypes" ∷ ([∗ map] parent ↦ ts ∈ types,
        own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
        ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
    "%Hbnd" ∷ ⌜(0 <= uint.Z lo /\ uint.Z hi <= Z.of_nat (length run))%Z⌝ ∗
    "%Hwin" ∷ ⌜∀ (k : nat) (c : item_cell), run !! k = Some c ->
                (uint.Z (cell_clock c) <= uint.Z clk)%Z ->
                (uint.Z clk < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z ->
                (uint.Z lo <= Z.of_nat k < uint.Z hi)%Z⌝)%I
    with "[left right nodes clock Hsl Htypes]" as "IH".
  { iExists (W64 0), sl.(slice.len).
    iFrame "left right nodes clock Hsl Htypes".
    iPureIntro. split; [word |].
    move=> k c Hk _ _. have Hklt := lookup_lt_Some _ _ _ Hk. word. }
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
    have HlenEq : length (iv.(yjs.item.content').(yjs.content.content')) = length (ic_run cmid).
    { have H := f_equal length Hcontent.
      rewrite length_fmap explode_length /toContent in H. lia. }
    have Hlenpos : (1 <= Z.of_nat (length (ic_run cmid)))%Z.
    { have [Hne _] := Hrun. destruct (ic_run cmid) as [|? ?]; [done | simpl; lia]. }
    have Hnw : (uint.Z (cell_clock cmid) + Z.of_nat (length (ic_run cmid)) < 2^64)%Z
      by (apply Hrunfits; exact (list_elem_of_lookup_2 _ _ _ Hcmid)).
    wp_apply (wp_item__Len cmid.(ic_loc) (DfracOwn 1) iv with "[$Hval]"). iIntros "Hval".
    rewrite HlenEq.
    iDestruct ("Hback" with "Hval") as "Htypes".
    wp_auto.
    destruct (bool_decide (uint.Z clk < uint.Z iv.(yjs.item.id').(yjs.id.clock'))) eqn:Hcmp1.
    + (* clk < middleClock: every covering cell sits strictly left of [mid] *)
      apply bool_decide_eq_true_1 in Hcmp1.
      wp_auto. wp_for_post.
      iFrame "HΦ". iExists lo, mid.
      iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
      iPureIntro. split.
      { lia. }
      move=> k c Hk Hcov1 Hcov2.
      have [Hlo Hhi] := Hwin k c Hk Hcov1 Hcov2.
      split; [exact Hlo |].
      destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
      * lia.
      * exfalso. subst k. rewrite Hcmid in Hk. injection Hk as <-.
        rewrite Hmcv in Hcov1. lia.
      * exfalso.
        have Hle := StronglySorted_lookup_le cell_le run (uint.nat mid) k cmid c Hsort Hcmid Hk Hgt.
        rewrite /cell_le Hmcv in Hle. lia.
    + apply bool_decide_eq_false_1 in Hcmp1.
      rewrite Hmcv in Hnw.
      wp_auto.
      case_bool_decide as Hcmp2.
      * (* clk >= middleEnd: every covering cell sits strictly right of [mid]
           (a left cell's range would have to swallow [mid]'s whole range,
           contradicting the index-wise disjointness) *)
        wp_auto. wp_for_post.
        iFrame "HΦ". iExists (word.add mid (W64 1)), hi.
        iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
        have Hmide : (uint.Z (w64_word_instance.(word.add) iv.(yjs.item.id').(yjs.id.clock') (W64 (length (ic_run cmid))))
                      = uint.Z iv.(yjs.item.id').(yjs.id.clock') + Z.of_nat (length (ic_run cmid)))%Z by word.
        rewrite Hmide in Hcmp2.
        iPureIntro. split.
        { word. }
        move=> k c Hk Hcov1 Hcov2.
        have [Hlo Hhi] := Hwin k c Hk Hcov1 Hcov2.
        split; [| exact Hhi].
        destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
        { exfalso.
          have Hle := StronglySorted_lookup_le cell_le run k (uint.nat mid) c cmid Hsort Hk Hcmid Hlt.
          rewrite /cell_le Hmcv in Hle.
          destruct (Hidisj k (uint.nat mid) c cmid Hk Hcmid ltac:(lia)) as [Hd | Hd];
            rewrite Hmcv in Hd; lia. }
        { exfalso. subst k. rewrite Hcmid in Hk. injection Hk as <-.
          rewrite Hmcv in Hcov2. lia. }
        word.
      * (* middleClock <= clk < middleEnd: the probe COVERS clk *)
        wp_auto. wp_for_post.
        iApply ("HΦ" $! mid). iFrame "Hsl Htypes".
        iExists cmid. iPureIntro. split; [exact Hcmid |].
        split; rewrite Hmcv; word.
  - (* [left >= right] never happens: the covering witness pins a nonempty window *)
    exfalso. have [Hf1 Hf2] := Hwin k0 c0 Hk0 Hc0le Hc0lt. lia.
Qed.

(** [store.GetNode], general covering form (issue #28 stage D1): the id may
    address ANY char of the witness cell's run; the returned node is pinned
    to [cw] by per-client clock-range disjointness (two same-client cells
    whose ranges both cover the id must share a location) instead of the
    all-singleton identification. Takes only the 2-conjunct big-sep (no
    [cell_unit]); additive alongside the unit fast path above, which it
    replaces at the C2 flip. *)
Lemma wp_store__GetNode_range (s mref : loc) (dq : dfrac) (idv : yjs.id.t)
    (types : gmap loc type_state) (cw : item_cell) :
  cw ∈ all_cells types ->
  cell_client cw = idv.(yjs.id.clientId') ->
  (uint.Z (cell_clock cw) <= uint.Z idv.(yjs.id.clock'))%Z ->
  (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
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
  move=> Hcw Hcwcc Hcwle Hcwlt Hrunfits Hnodup Hrangedisj.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  set (kc := idv.(yjs.id.clientId')).
  have Hcwkc : cell_client cw = kc := Hcwcc.
  iNamed "Hitemmap".
  have Hkcin : kc ∈ (cell_client <$> all_cells types).
  { rewrite -Hcwkc. apply list_elem_of_fmap_2. exact Hcw. }
  destruct (Hcomplete kc Hkcin) as [slk Hslk].
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Hmap"). iIntros "Hmap".
  rewrite Hslk /=.
  wp_auto.
  iDestruct (big_sepM_lookup_acc _ _ kc slk Hslk with "Hruns") as "[Hrun Hrunsback]".
  iNamed "Hrun".
  have Hcwrun : cw ∈ client_run types kc by (apply client_run_mem; split; [exact Hcw | exact Hcwcc]).
  apply list_elem_of_lookup_1 in Hcwrun. destruct Hcwrun as [kw Hkw].
  have Hrunfits' : ∀ c, c ∈ client_run types kc ->
      (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z.
  { move=> c Hc. exact (Hrunfits c (proj1 (proj1 (client_run_mem types kc c) Hc))). }
  (* index-wise disjointness of the run from the pool invariants *)
  have HndAll : NoDup (all_cells types) := NoDup_fmap_1 ic_loc _ Hnodup.
  have Hndrun : NoDup (client_run types kc).
  { rewrite /client_run (merge_sort_Permutation cell_le _). apply NoDup_filter. exact HndAll. }
  have Hinj : ∀ x y, x ∈ client_run types kc → y ∈ client_run types kc → ic_loc x = ic_loc y → x = y.
  { move=> x y Hx Hy Hxy.
    have Hxa : x ∈ all_cells types := proj1 (proj1 (client_run_mem types kc x) Hx).
    have Hya : y ∈ all_cells types := proj1 (proj1 (client_run_mem types kc y) Hy).
    apply list_elem_of_lookup_1 in Hxa as [ix Hix]. apply list_elem_of_lookup_1 in Hya as [iy Hiy].
    have Hlix : (ic_loc <$> all_cells types) !! ix = Some (ic_loc y) by (rewrite list_lookup_fmap Hix /= Hxy //).
    have Hliy : (ic_loc <$> all_cells types) !! iy = Some (ic_loc y) by (rewrite list_lookup_fmap Hiy //).
    have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnodup Hlix Hliy.
    congruence. }
  have Hidisj : ∀ (k1 k2 : nat) (c1 c2 : item_cell),
      client_run types kc !! k1 = Some c1 -> client_run types kc !! k2 = Some c2 -> k1 ≠ k2 ->
      (uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)) <= uint.Z (cell_clock c2))%Z ∨
      (uint.Z (cell_clock c2) + Z.of_nat (length (ic_run c2)) <= uint.Z (cell_clock c1))%Z.
  { move=> k1 k2 c1 c2 Hk1 Hk2 Hkne.
    have Hc1r : c1 ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hk1.
    have Hc2r : c2 ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hk2.
    have Hlocne : ic_loc c1 ≠ ic_loc c2.
    { move=> Heq. have Hceq : c1 = c2 := Hinj c1 c2 Hc1r Hc2r Heq.
      rewrite Hceq in Hk1. exact (Hkne (NoDup_lookup _ _ _ _ Hndrun Hk1 Hk2)). }
    apply (Hrangedisj c1 c2
             (proj1 (proj1 (client_run_mem types kc c1) Hc1r))
             (proj1 (proj1 (client_run_mem types kc c2) Hc2r)));
      [| exact Hlocne].
    rewrite (proj2 (proj1 (client_run_mem types kc c1) Hc1r))
            (proj2 (proj1 (client_run_mem types kc c2) Hc2r)) //. }
  wp_apply (wp_getNodeIndex_range slk dq types (client_run types kc) idv.(yjs.id.clock') kw cw
              (client_run_sorted types kc)
              (fun c Hc => proj1 (proj1 (client_run_mem types kc c) Hc))
              Hrunfits' Hidisj Hkw Hcwle Hcwlt
              with "[$Hslice $Htypes]").
  iIntros (i) "(Hslice & Htypes & %Hires)".
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
  (* both [cres] and [cw] cover the requested clock at the same client:
     range disjointness forces the same location *)
  have Hcresmem : cres ∈ all_cells types /\ cell_client cres = kc.
  { apply client_run_mem. exact (list_elem_of_lookup_2 _ _ _ Hcres). }
  have Hloceq : cres.(ic_loc) = cw.(ic_loc).
  { destruct (decide (cres.(ic_loc) = cw.(ic_loc))) as [He | Hne]; [exact He | exfalso].
    destruct (Hrangedisj cres cw (proj1 Hcresmem) Hcw
                ltac:(rewrite (proj2 Hcresmem) Hcwcc //) Hne) as [Hd | Hd]; lia. }
  rewrite Hloceq.
  iApply "HΦ".
  iFrame "Hitemsf".
  iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
  iSplitL "Hmap Hruns".
  { iExists gm. iFrame "Hmap Hruns". iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
  iFrame "Htypes".
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
      ⌜rloc ≠ null⌝ ∗ ⌜rloc ∉ ic_loc <$> all_cells types⌝ ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗
      own_item_map mref (DfracOwn 1) (<[parent := MkTypeState (split_cells cells k (uint.nat diff) rloc) arr]> types) ∗
      ([∗ map] p ↦ ts ∈ (<[parent := MkTypeState (split_cells cells k (uint.nat diff) rloc) arr]> types),
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗ ⌜YjsArrInvariant (ty_arr ts)⌝) }}}.
Proof using Type*.
  move=> Htypes Hcellk Hdiff Hrunfits Hnodup Hdisj Hrunlen.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  (* open [parent]'s [own_ytype_cells], peel node [k] out of the DLL *)
  iDestruct (big_sepM_delete _ _ parent _ Htypes with "Htypes") as "[(Hpc & %Harrinv) Hrestmap]".
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
  (* the fresh right node's location misses the whole pool (issue #28 D2a):
     the parent's cells conflict through the opened DLL segments, the other
     types' through the delete-map big-sep *)
  iDestruct (own_dll_fresh with "Hrs Hseg1") as %Hfr_pre.
  iDestruct (own_dll_fresh with "Hrs Hrest") as %Hfr_suf.
  iAssert (⌜rs ≠ ic_loc cw⌝)%I as %Hfr_cw.
  { destruct (decide (rs = ic_loc cw)) as [Heqloc | Hneloc]; last by iPureIntro.
    iEval (rewrite Heqloc) in "Hrs".
    iDestruct (item_pointsto_conflict with "Hrs Hval") as %[]. }
  iDestruct (big_sepM_sep with "Hrestmap") as "[Hrestown Hrestinv]".
  iDestruct (all_cells_fresh rs _ (DfracOwn 1) (delete parent types) with "Hrs Hrestown") as %Hfr_rest.
  iAssert ([∗ map] p0 ↦ ts0 ∈ delete parent types,
      own_ytype_cells p0 (DfracOwn 1) (ty_cells ts0) (ty_arr ts0) ∗
      ⌜YjsArrInvariant (ty_arr ts0)⌝)%I with "[Hrestown Hrestinv]" as "Hrestmap".
  { rewrite big_sepM_sep. iFrame "Hrestown Hrestinv". }
  have Hrsfresh : rs ∉ ic_loc <$> all_cells types.
  { move=> Hin.
    rewrite (all_cells_lookup types parent _ Htypes) /= in Hin.
    rewrite -Hsplit in Hin.
    rewrite fmap_app in Hin. apply elem_of_app in Hin as [Hin | Hin].
    - rewrite fmap_app in Hin. apply elem_of_app in Hin as [Hin | Hin].
      + exact (Hfr_pre Hin).
      + rewrite fmap_cons in Hin. apply elem_of_cons in Hin as [Heqc | Hin].
        * exact (Hfr_cw Heqc).
        * exact (Hfr_suf Hin).
    - exact (Hfr_rest Hin). }
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
    iAssert ([∗ map] p0 ↦ ts0 ∈ <[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types,
        own_ytype_cells p0 (DfracOwn 1) (ty_cells ts0) (ty_arr ts0) ∗
        ⌜YjsArrInvariant (ty_arr ts0)⌝)%I with "[Hyt2 Hrestmap]" as "Htypes2".
    { rewrite -insert_delete_eq big_sepM_insert_delete delete_delete_eq.
      iFrame "Hrestmap". simpl. iFrame "Hyt2". iPureIntro. exact Harrinv. }
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
    iPureIntro. split; [exact Hrsnn | exact Hrsfresh].
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
    iAssert ([∗ map] p0 ↦ ts0 ∈ <[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types,
        own_ytype_cells p0 (DfracOwn 1) (ty_cells ts0) (ty_arr ts0) ∗
        ⌜YjsArrInvariant (ty_arr ts0)⌝)%I with "[Hyt2 Hrestmap]" as "Htypes2".
    { rewrite -insert_delete_eq big_sepM_insert_delete delete_delete_eq.
      iFrame "Hrestmap". simpl. iFrame "Hyt2". iPureIntro. exact Harrinv. }
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
    iPureIntro. split; [exact Hrsnn | exact Hrsfresh].
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

(** [store.splitAtAndGetLeft], general splitting form (issue #28 stage D1b):
    the id may address ANY char of the witness cell's run. When it is the
    run's LAST char the node already ends there and nothing changes;
    otherwise the node is split just after the id ([splitNode] at offset+1)
    and the truncated-in-place left half comes back (same location). Either
    way the returned node's run ends exactly at [idv]: the clean-end
    boundary the C2 flip feeds to Integrate as the left cursor. Mutates the
    item map, hence [DfracOwn 1]; needs the pool invariants (run-fits,
    loc-NoDup, range disjointness) and the run-list capacity bound. *)
Lemma wp_store__splitAtAndGetLeft_range (s mref : loc) (idv : yjs.id.t)
    (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  cell_client cw = idv.(yjs.id.clientId') ->
  (uint.Z (cell_clock cw) <= uint.Z idv.(yjs.id.clock'))%Z ->
  (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  ((1 < length (ic_run cw))%nat ->
   (Z.of_nat (length (client_run types (cell_client cw))) + 1 < 2^63)%Z) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetLeft" #idv
  {{{ (types' : gmap loc type_state), RET (#(ic_loc cw), #true);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat = (length (ic_run cw) - 1)%nat ∧
        types' = types)
       ∨ (((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) < length (ic_run cw) - 1)%nat ∧
          ∃ rloc : loc, rloc ≠ null ∧ rloc ∉ (ic_loc <$> all_cells types) ∧
            types' = <[parent := MkTypeState
              (split_cells cells k ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc)
              arr]> types)⌝ }}}.
Proof using Type*.
  move=> Htypes Hcellk Hcwcc Hcwle Hcwlt Hrunfits Hnodup Hrangedisj Hrunlen.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  have Hcwmem : cw ∈ all_cells types.
  { apply all_cells_elem_of. exists parent, (MkTypeState cells arr).
    split; [exact Htypes | exact (list_elem_of_lookup_2 _ _ _ Hcellk)]. }
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_store__GetNode_range s mref (DfracOwn 1) idv types cw
              Hcwmem Hcwcc Hcwle Hcwlt Hrunfits Hnodup Hrangedisj
              with "[$Hitemsf $Hitemmap $Htypes]").
  iIntros "(Hitemsf & Hitemmap & Htypes)".
  wp_auto.
  iDestruct (types_cell_acc_gen types cw Hcwmem with "Htypes") as "Hacc".
  iNamed "Hacc".
  have Hnwcw := Hrunfits cw Hcwmem.
  have Hcwck : cell_clock cw = iv.(yjs.item.id').(yjs.id.clock')
    by (rewrite /cell_clock Hid /toYjsId /=; word).
  have HlenEq : length (iv.(yjs.item.content').(yjs.content.content')) = length (ic_run cw).
  { have H := f_equal length Hcontent.
    rewrite length_fmap explode_length /toContent in H. lia. }
  have Hlenpos : (1 <= Z.of_nat (length (ic_run cw)))%Z.
  { have [Hne0 _] := Hrun. destruct (ic_run cw) as [|? ?]; [done | simpl; lia]. }
  have Hosub : uint.Z (w64_word_instance.(word.sub) idv.(yjs.id.clock') iv.(yjs.item.id').(yjs.id.clock'))
             = Z.of_nat (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat.
  { rewrite -Hcwck. clear -Hcwle. word. }
  have Holt : ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) < length (ic_run cw))%nat.
  { clear -Hcwle Hcwlt. word. }
  wp_auto.
  wp_apply (wp_item__Len (ic_loc cw) (DfracOwn 1) iv with "[$Hval]"). iIntros "Hval".
  rewrite HlenEq.
  wp_auto.
  wp_if_destruct.
  - (* offset = Len-1: the run already ends at [idv]; no split *)
    iDestruct ("Hback" with "Hval") as "Htypes".
    iApply ("HΦ" $! types).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. left. split; [| reflexivity].
    word.
  - (* the id sits strictly inside the run: split just after it *)
    iDestruct ("Hback" with "Hval") as "Htypes".
    have Hnlt : ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) < length (ic_run cw) - 1)%nat.
    { word. }
    have Hdiffnat : uint.nat (w64_word_instance.(word.add)
                      (w64_word_instance.(word.sub) idv.(yjs.id.clock') iv.(yjs.item.id').(yjs.id.clock'))
                      (W64 1))
                  = ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1)%nat.
    { clear -Hosub Hnlt Hnwcw Hlenpos. word. }
    have Hdiffb : (0 < uint.nat (w64_word_instance.(word.add)
                      (w64_word_instance.(word.sub) idv.(yjs.id.clock') iv.(yjs.item.id').(yjs.id.clock'))
                      (W64 1)) < length (ic_run cw))%nat.
    { rewrite Hdiffnat. clear -Hnlt. lia. }
    have Hdisjcw : ∀ c, c ∈ all_cells types -> cell_client c = cell_client cw -> ic_loc c ≠ ic_loc cw ->
       (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z (cell_clock cw))%Z ∨
       (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) <= uint.Z (cell_clock c))%Z.
    { move=> c Hc Hcc Hlocne. exact (Hrangedisj c cw Hc Hcwmem Hcc Hlocne). }
    have Hrunlen' : (Z.of_nat (length (client_run types (cell_client cw))) + 1 < 2^63)%Z.
    { apply Hrunlen. clear -Hnlt. lia. }
    wp_apply (wp_store__splitNode s mref types parent cells arr k cw
                (w64_word_instance.(word.add)
                   (w64_word_instance.(word.sub) idv.(yjs.id.clock') iv.(yjs.item.id').(yjs.id.clock'))
                   (W64 1))
                Htypes Hcellk Hdiffb Hrunfits Hnodup Hdisjcw Hrunlen'
                with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
    iIntros (rloc) "(%Hrlocnn & %Hrlocfresh & Hitemsf & Hitemmap & Htypes)".
    wp_auto.
    iApply ("HΦ" $! (<[parent := MkTypeState (split_cells cells k (uint.nat (w64_word_instance.(word.add)
                   (w64_word_instance.(word.sub) idv.(yjs.id.clock') iv.(yjs.item.id').(yjs.id.clock'))
                   (W64 1))) rloc) arr]> types)).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. right. split.
    { exact Hnlt. }
    exists rloc. split_and!; [exact Hrlocnn | exact Hrlocfresh |].
    rewrite Hdiffnat //.
Qed.

(** [store.splitAtAndGetRight], general splitting form (issue #28 stage
    D1b): when the id addresses the HEAD of the witness cell's run nothing
    changes and the node itself comes back; otherwise the node is split at
    the id's offset and the fresh right half comes back. Either way the
    returned node's run STARTS exactly at [idv]: the clean-start boundary
    the C2 flip feeds to Integrate as the right cursor. *)
Lemma wp_store__splitAtAndGetRight_range (s mref : loc) (idv : yjs.id.t)
    (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  cell_client cw = idv.(yjs.id.clientId') ->
  (uint.Z (cell_clock cw) <= uint.Z idv.(yjs.id.clock'))%Z ->
  (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  ((1 < length (ic_run cw))%nat ->
   (Z.of_nat (length (client_run types (cell_client cw))) + 1 < 2^63)%Z) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetRight" #idv
  {{{ (rl : loc) (types' : gmap loc type_state), RET (#rl, #true);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat = 0%nat ∧
        rl = ic_loc cw ∧ types' = types)
       ∨ ((0 < (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)))%nat ∧
          rl ≠ null ∧ rl ∉ (ic_loc <$> all_cells types) ∧
          types' = <[parent := MkTypeState
            (split_cells cells k (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl)
            arr]> types)⌝ }}}.
Proof using Type*.
  move=> Htypes Hcellk Hcwcc Hcwle Hcwlt Hrunfits Hnodup Hrangedisj Hrunlen.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  have Hcwmem : cw ∈ all_cells types.
  { apply all_cells_elem_of. exists parent, (MkTypeState cells arr).
    split; [exact Htypes | exact (list_elem_of_lookup_2 _ _ _ Hcellk)]. }
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_store__GetNode_range s mref (DfracOwn 1) idv types cw
              Hcwmem Hcwcc Hcwle Hcwlt Hrunfits Hnodup Hrangedisj
              with "[$Hitemsf $Hitemmap $Htypes]").
  iIntros "(Hitemsf & Hitemmap & Htypes)".
  wp_auto.
  iDestruct (types_cell_acc_gen types cw Hcwmem with "Htypes") as "Hacc".
  iNamed "Hacc".
  have Hnwcw := Hrunfits cw Hcwmem.
  have Hcwck : cell_clock cw = iv.(yjs.item.id').(yjs.id.clock')
    by (rewrite /cell_clock Hid /toYjsId /=; word).
  have Hlenpos : (1 <= Z.of_nat (length (ic_run cw)))%Z.
  { have [Hne0 _] := Hrun. destruct (ic_run cw) as [|? ?]; [done | simpl; lia]. }
  have Hosub : uint.Z (w64_word_instance.(word.sub) idv.(yjs.id.clock') iv.(yjs.item.id').(yjs.id.clock'))
             = Z.of_nat (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat.
  { rewrite -Hcwck. clear -Hcwle. word. }
  have Holt : ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) < length (ic_run cw))%nat.
  { clear -Hcwle Hcwlt. word. }
  wp_auto.
  wp_if_destruct.
  - (* offset > 0: split at the offset, return the fresh right half *)
    iDestruct ("Hback" with "Hval") as "Htypes".
    have Hopos : (0 < (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)))%nat.
    { word. }
    have Hdiffnat : uint.nat (w64_word_instance.(word.sub) idv.(yjs.id.clock') iv.(yjs.item.id').(yjs.id.clock'))
                  = (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat.
    { clear -Hosub. word. }
    have Hdiffb : (0 < uint.nat (w64_word_instance.(word.sub) idv.(yjs.id.clock') iv.(yjs.item.id').(yjs.id.clock'))
                   < length (ic_run cw))%nat.
    { rewrite Hdiffnat. clear -Hopos Holt. lia. }
    have Hdisjcw : ∀ c, c ∈ all_cells types -> cell_client c = cell_client cw -> ic_loc c ≠ ic_loc cw ->
       (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z (cell_clock cw))%Z ∨
       (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) <= uint.Z (cell_clock c))%Z.
    { move=> c Hc Hcc Hlocne. exact (Hrangedisj c cw Hc Hcwmem Hcc Hlocne). }
    have Hrunlen' : (Z.of_nat (length (client_run types (cell_client cw))) + 1 < 2^63)%Z.
    { apply Hrunlen. clear -Hopos Holt. lia. }
    wp_apply (wp_store__splitNode s mref types parent cells arr k cw
                (w64_word_instance.(word.sub) idv.(yjs.id.clock') iv.(yjs.item.id').(yjs.id.clock'))
                Htypes Hcellk Hdiffb Hrunfits Hnodup Hdisjcw Hrunlen'
                with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
    iIntros (rloc) "(%Hrlocnn & %Hrlocfresh & Hitemsf & Hitemmap & Htypes)".
    wp_auto.
    iApply ("HΦ" $! rloc (<[parent := MkTypeState (split_cells cells k
                (uint.nat (w64_word_instance.(word.sub) idv.(yjs.id.clock') iv.(yjs.item.id').(yjs.id.clock')))
                rloc) arr]> types)).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. right. split.
    { exact Hopos. }
    split_and!; [exact Hrlocnn | exact Hrlocfresh |].
    rewrite Hdiffnat //.
  - (* offset = 0: the run already starts at [idv]; no split *)
    iDestruct ("Hback" with "Hval") as "Htypes".
    iApply ("HΦ" $! (ic_loc cw) types).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. left. split_and!; [| reflexivity | reflexivity].
    word.
Qed.

(* ----- split_cells pool bookkeeping (issue #28 stage D1c) -----------------
   The pool effect of a split: the covering cell [cw] is replaced by its two
   halves, everything else untouched ([split_pool_perm]). On top of it, the
   pointwise preservation of the store pool invariants: run-fits, range
   disjointness, origin-clock (the right half's origin telescopes inside
   [cw]'s own run), and loc-NoDup (given the right half's location is fresh).
   These are what the general [repair] uses to re-establish [store_inv]
   across its clean-end / clean-start splits at the C2 flip. *)

(** The two halves' head / length / client / clock facts, in one bundle. *)
Lemma split_cell_facts (cw : item_cell) (o : nat) (rloc : loc) :
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  run_head (split_cell_left cw o) = run_head cw ∧
  length (ic_run (split_cell_left cw o)) = o ∧
  length (ic_run (split_cell_right cw o rloc)) = (length (ic_run cw) - o)%nat ∧
  cell_client (split_cell_left cw o) = cell_client cw ∧
  cell_client (split_cell_right cw o rloc) = cell_client cw ∧
  cell_clock (split_cell_left cw o) = cell_clock cw ∧
  cell_clock (split_cell_right cw o rloc) = W64 (Z.of_nat (clock (item_id (run_head cw)) + o)%nat).
Proof.
  move=> Hrunwf [Hopos Holt].
  have Hrun0 : ic_run cw !! 0%nat = Some (run_head cw).
  { rewrite /run_head. destruct Hrunwf as [Hne _].
    destruct (ic_run cw) as [|a r']; [done | reflexivity]. }
  destruct (ic_run cw !! o) as [yo|] eqn:Hyo; last by (apply lookup_ge_None in Hyo; lia).
  have Hidy := run_wf_lookup_clock (ic_run cw) o (run_head cw) yo Hrunwf Hrun0 Hyo.
  have Hheadl : run_head (split_cell_left cw o) = run_head cw.
  { rewrite /run_head /split_cell_left /=. apply hd_inhabitant_take. lia. }
  have Hheadr : run_head (split_cell_right cw o rloc) = yo.
  { rewrite /run_head /split_cell_right /=. exact (hd_inhabitant_drop _ o yo Hyo). }
  split_and!.
  - exact Hheadl.
  - rewrite /split_cell_left /= length_take. lia.
  - rewrite /split_cell_right /= length_drop //.
  - rewrite /cell_client Hheadl //.
  - rewrite /cell_client Hheadr Hidy //=.
  - rewrite /cell_clock Hheadl //.
  - rewrite /cell_clock Hheadr Hidy //=.
Qed.

(** The pool permutation of a split: [cw] out, its two halves in. *)
Lemma split_pool_perm (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  ∃ rest : list item_cell,
    all_cells types ≡ₚ cw :: rest ∧
    all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types)
      ≡ₚ split_cell_left cw o :: split_cell_right cw o rloc :: rest.
Proof.
  move=> Htypes Hck.
  exists (take k cells ++ drop (S k) cells ++ all_cells (delete parent types)).
  split.
  - rewrite (all_cells_lookup types parent _ Htypes) /=.
    rewrite -{1}(take_drop_middle cells k cw Hck).
    rewrite -app_assoc /=.
    rewrite -Permutation_middle //.
  - rewrite (all_cells_insert types parent _ _ Htypes) /= /split_cells Hck.
    rewrite -!app_assoc /=.
    rewrite -Permutation_middle.
    rewrite -Permutation_middle //.
Qed.

(** Run-fits survives a split: each half's range is a sub-range of [cw]'s.
    [Hckbnd] (the head clock fits as a NAT, from [types_cells_id_bounds])
    makes the right half's [W64] clock exact. *)
Lemma split_pool_fits (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types) ->
     (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z).
Proof.
  move=> Htypes Hck Hrunwf Ho Hckbnd Hfits c Hc.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  have Hcwmem : cw ∈ all_cells types by (rewrite Hold; apply list_elem_of_here).
  have Hfitscw := Hfits cw Hcwmem.
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  have HclkZ : uint.Z (cell_clock cw) = Z.of_nat (clock (item_id (run_head cw))).
  { rewrite /cell_clock. word. }
  rewrite Hnew in Hc.
  apply elem_of_cons in Hc as [-> | Hc].
  - rewrite Hclockl Hlenl. lia.
  - apply elem_of_cons in Hc as [-> | Hc].
    + rewrite Hclockr Hlenr.
      have Hbo : (Z.of_nat (clock (item_id (run_head cw)) + o) < 2^64)%Z by lia.
      have -> : uint.Z (W64 (Z.of_nat (clock (item_id (run_head cw)) + o)%nat))
              = Z.of_nat (clock (item_id (run_head cw)) + o)%nat by word.
      lia.
    + apply Hfits. rewrite Hold. apply elem_of_cons. by right.
Qed.

(** Origin-clock survives a split: the left half keeps [cw]'s head (and so
    its origin fact); the right half's head is [cw]'s char at offset [o],
    whose origin is the previous char of the SAME run ([run_wf] chaining):
    same client, clock exactly one below. *)
Lemma split_pool_originclk (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (∀ c, c ∈ all_cells types -> cell_origin_clk c) ->
  (∀ c, c ∈ all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types) ->
     cell_origin_clk c).
Proof.
  move=> Htypes Hck Hrunwf Ho Hoclk c Hc.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  have Hcwmem : cw ∈ all_cells types by (rewrite Hold; apply list_elem_of_here).
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  rewrite Hnew in Hc.
  apply elem_of_cons in Hc as [-> | Hc].
  - rewrite /cell_origin_clk Hheadl. exact (Hoclk cw Hcwmem).
  - apply elem_of_cons in Hc as [-> | Hc].
    + (* the right half: its head's origin is the previous char of the run *)
      rewrite /cell_origin_clk.
      have Hrun0 : ic_run cw !! 0%nat = Some (run_head cw).
      { rewrite /run_head. destruct Hrunwf as [Hne _].
        destruct (ic_run cw) as [|a r']; [done | reflexivity]. }
      destruct (ic_run cw !! o) as [yo|] eqn:Hyo; last by (apply lookup_ge_None in Hyo; lia).
      destruct (ic_run cw !! (o - 1)%nat) as [yp|] eqn:Hyp; last by (apply lookup_ge_None in Hyp; lia).
      have Hheadr : run_head (split_cell_right cw o rloc) = yo.
      { rewrite /run_head /split_cell_right /=. exact (hd_inhabitant_drop _ o yo Hyo). }
      have Hso : S (o - 1)%nat = o by lia.
      have Hstep := proj2 Hrunwf (o - 1)%nat yp yo Hyp ltac:(rewrite Hso //).
      destruct Hstep as (Hidyo & Horigyo & _).
      have Hidyp := run_wf_lookup_clock (ic_run cw) (o - 1)%nat (run_head cw) yp Hrunwf Hrun0 Hyp.
      move=> oid Hoid Hcl.
      rewrite Hheadr Horigyo /= in Hoid.
      injection Hoid as <-.
      rewrite Hheadr Hidyo Hidyp /=. lia.
    + apply (Hoclk c). rewrite Hold. apply elem_of_cons. by right.
Qed.

(** Range disjointness survives a split: the halves' ranges partition [cw]'s,
    so any old cell disjoint from [cw] is disjoint from both halves, and the
    halves are disjoint from each other by construction. Needs loc-NoDup so
    an old cell at [cw]'s own location cannot survive into [rest]. *)
Lemma split_pool_rangedisj (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z ->
  (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) < 2^64)%Z ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  cells_range_disjoint (all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types)).
Proof.
  move=> Htypes Hck Hrunwf Ho Hckbnd Hfitscw Hnodup Hdisj.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  have Hcwmem : cw ∈ all_cells types by (rewrite Hold; apply list_elem_of_here).
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  have HclkZ : uint.Z (cell_clock cw) = Z.of_nat (clock (item_id (run_head cw))).
  { rewrite /cell_clock. word. }
  have Hbo : (Z.of_nat (clock (item_id (run_head cw)) + o) < 2^64)%Z by lia.
  have HclkrZ : uint.Z (cell_clock (split_cell_right cw o rloc))
              = (uint.Z (cell_clock cw) + Z.of_nat o)%Z.
  { rewrite Hclockr HclkZ. word. }
  (* an old cell in [rest] never sits at [cw]'s location (loc-NoDup) *)
  have Hrestloc : ∀ c, c ∈ rest -> ic_loc c ≠ ic_loc cw.
  { move=> c Hc Heq.
    have Hperm : ic_loc <$> all_cells types ≡ₚ ic_loc cw :: (ic_loc <$> rest)
      by rewrite Hold //.
    have Hnd2 : NoDup (ic_loc cw :: (ic_loc <$> rest)) by rewrite -Hperm //.
    apply NoDup_cons in Hnd2 as [Hnotin _].
    apply Hnotin. rewrite -Heq. apply list_elem_of_fmap_2. exact Hc.
  }
  (* disjointness of an old cell against [cw] transfers to both halves *)
  have Holdcase : ∀ c, c ∈ rest -> cell_client c = cell_client cw ->
    (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z (cell_clock cw))%Z ∨
    (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) <= uint.Z (cell_clock c))%Z.
  { move=> c Hc Hcc.
    apply (Hdisj c cw); [rewrite Hold; apply elem_of_cons; by right | exact Hcwmem | exact Hcc |].
    exact (Hrestloc c Hc). }
  move=> c1 c2 Hc1 Hc2 Hcc Hlocne.
  rewrite Hnew in Hc1 Hc2.
  apply elem_of_cons in Hc1 as [-> | Hc1];
    [| apply elem_of_cons in Hc1 as [-> | Hc1]];
    apply elem_of_cons in Hc2 as [-> | Hc2];
    try (apply elem_of_cons in Hc2 as [-> | Hc2]).
  - (* cl vs cl: same loc, guard is false *)
    exfalso. exact (Hlocne eq_refl).
  - (* cl vs cr: left half strictly below the right half *)
    left. rewrite Hclockl Hlenl HclkrZ. lia.
  - (* cl vs old *)
    have Hcc' : cell_client c2 = cell_client cw by rewrite -Hcc Hclientl //.
    destruct (Holdcase c2 Hc2 Hcc') as [Hd | Hd].
    + right. rewrite Hclockl. lia.
    + left. rewrite Hclockl Hlenl. lia.
  - (* cr vs cl *)
    right. rewrite Hclockl Hlenl HclkrZ. lia.
  - (* cr vs cr: same loc *)
    exfalso. exact (Hlocne eq_refl).
  - (* cr vs old *)
    have Hcc' : cell_client c2 = cell_client cw by rewrite -Hcc Hclientr //.
    destruct (Holdcase c2 Hc2 Hcc') as [Hd | Hd].
    + right. rewrite HclkrZ. lia.
    + left. rewrite HclkrZ Hlenr. lia.
  - (* old vs cl *)
    have Hcc' : cell_client c1 = cell_client cw by rewrite Hcc Hclientl //.
    destruct (Holdcase c1 Hc1 Hcc') as [Hd | Hd].
    + left. rewrite Hclockl. lia.
    + right. rewrite Hclockl Hlenl. lia.
  - (* old vs cr *)
    have Hcc' : cell_client c1 = cell_client cw by rewrite Hcc Hclientr //.
    destruct (Holdcase c1 Hc1 Hcc') as [Hd | Hd].
    + left. rewrite HclkrZ. lia.
    + right. rewrite HclkrZ Hlenr. lia.
  - (* old vs old *)
    apply (Hdisj c1 c2); [rewrite Hold; apply elem_of_cons; by right
                         | rewrite Hold; apply elem_of_cons; by right
                         | exact Hcc | exact Hlocne].
Qed.

(** Loc-NoDup survives a split, given the fresh right location: the pool's
    location multiset gains exactly [rloc]. *)
Lemma split_pool_locdup (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  rloc ∉ (ic_loc <$> all_cells types) ->
  NoDup (ic_loc <$> all_cells types) ->
  NoDup (ic_loc <$> all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types)).
Proof.
  move=> Htypes Hck Hfresh Hnodup.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  have Hpermnew : ic_loc <$> all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types)
                ≡ₚ ic_loc cw :: rloc :: (ic_loc <$> rest)
    by rewrite Hnew //.
  have Hpermold : ic_loc <$> all_cells types ≡ₚ ic_loc cw :: (ic_loc <$> rest)
    by rewrite Hold //.
  rewrite Hpermnew.
  have Hndold : NoDup (ic_loc cw :: (ic_loc <$> rest)) by rewrite -Hpermold //.
  apply NoDup_cons in Hndold as [Hcwnotin Hndrest].
  have Hrfresh2 : rloc ∉ ic_loc cw :: (ic_loc <$> rest) by rewrite -Hpermold //.
  apply not_elem_of_cons in Hrfresh2 as [Hrnecw Hrnotin].
  apply NoDup_cons. split.
  { apply not_elem_of_cons. split; [congruence | exact Hcwnotin]. }
  apply NoDup_cons. split; [exact Hrnotin | exact Hndrest].
Qed.

(** [split_cells] index bookkeeping (issue #28 stage D2b prep): length and
    the four lookup regions. The general [repair] uses these to relocate its
    second (clean-start) witness after the first (clean-end) split touched
    the same type. *)
Lemma split_cells_length (cells : list item_cell) (k o : nat) (rloc : loc) (cw : item_cell) :
  cells !! k = Some cw ->
  length (split_cells cells k o rloc) = S (length cells).
Proof.
  move=> Hck. rewrite /split_cells Hck !length_app /= length_take length_drop.
  have := lookup_lt_Some _ _ _ Hck. lia.
Qed.

Lemma split_cells_lookup_left (cells : list item_cell) (k o : nat) (rloc : loc) (cw : item_cell) :
  cells !! k = Some cw ->
  split_cells cells k o rloc !! k = Some (split_cell_left cw o).
Proof.
  move=> Hck. rewrite /split_cells Hck.
  have Hklen : (k < length cells)%nat := lookup_lt_Some _ _ _ Hck.
  have Htk : length (take k cells) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_r; last lia.
  rewrite Htk Nat.sub_diag //.
Qed.

Lemma split_cells_lookup_right (cells : list item_cell) (k o : nat) (rloc : loc) (cw : item_cell) :
  cells !! k = Some cw ->
  split_cells cells k o rloc !! (S k) = Some (split_cell_right cw o rloc).
Proof.
  move=> Hck. rewrite /split_cells Hck.
  have Hklen : (k < length cells)%nat := lookup_lt_Some _ _ _ Hck.
  have Htk : length (take k cells) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_r; last lia.
  rewrite Htk.
  have -> : (S k - k)%nat = 1%nat by lia.
  done.
Qed.

Lemma split_cells_lookup_before (cells : list item_cell) (k o : nat) (rloc : loc)
    (cw : item_cell) (j : nat) :
  cells !! k = Some cw -> (j < k)%nat ->
  split_cells cells k o rloc !! j = cells !! j.
Proof.
  move=> Hck Hj. rewrite /split_cells Hck.
  have Hklen : (k < length cells)%nat := lookup_lt_Some _ _ _ Hck.
  have Htk : length (take k cells) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_l; last lia.
  rewrite lookup_take_lt; [done | lia].
Qed.

Lemma split_cells_lookup_after (cells : list item_cell) (k o : nat) (rloc : loc)
    (cw : item_cell) (j : nat) :
  cells !! k = Some cw -> (k < j)%nat ->
  split_cells cells k o rloc !! (S j) = cells !! j.
Proof.
  move=> Hck Hj. rewrite /split_cells Hck.
  have Hklen : (k < length cells)%nat := lookup_lt_Some _ _ _ Hck.
  have Htk : length (take k cells) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_r; last lia.
  rewrite Htk /=.
  have -> : (S j - k)%nat = S (S (j - S k)) by lia.
  simpl. rewrite lookup_drop. f_equal. lia.
Qed.

(** A clock covered by [cw]'s range is covered by exactly one of the two
    halves; the dispatch is [clkZ < clock cw + o]. Relocates a covering
    witness across a split when both origins land in the same run. *)
Lemma split_cell_cover (cw : item_cell) (o : nat) (rloc : loc) (clkZ : Z) :
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z ->
  (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) < 2^64)%Z ->
  (uint.Z (cell_clock cw) <= clkZ)%Z ->
  (clkZ < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  ((clkZ < uint.Z (cell_clock cw) + Z.of_nat o)%Z ∧
   (uint.Z (cell_clock (split_cell_left cw o)) <= clkZ)%Z ∧
   (clkZ < uint.Z (cell_clock (split_cell_left cw o))
           + Z.of_nat (length (ic_run (split_cell_left cw o))))%Z)
  ∨ ((uint.Z (cell_clock cw) + Z.of_nat o <= clkZ)%Z ∧
     (uint.Z (cell_clock (split_cell_right cw o rloc)) <= clkZ)%Z ∧
     (clkZ < uint.Z (cell_clock (split_cell_right cw o rloc))
             + Z.of_nat (length (ic_run (split_cell_right cw o rloc))))%Z).
Proof.
  move=> Hrunwf Ho Hckbnd Hfitscw Hle Hlt.
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  have HclkZ : uint.Z (cell_clock cw) = Z.of_nat (clock (item_id (run_head cw))).
  { rewrite /cell_clock. word. }
  have Hbo : (Z.of_nat (clock (item_id (run_head cw)) + o) < 2^64)%Z by lia.
  have HclkrZ : uint.Z (cell_clock (split_cell_right cw o rloc))
              = (uint.Z (cell_clock cw) + Z.of_nat o)%Z.
  { rewrite Hclockr HclkZ. word. }
  destruct (decide (clkZ < uint.Z (cell_clock cw) + Z.of_nat o)%Z) as [Hd | Hd].
  - left. rewrite Hclockl Hlenl. split_and!; lia.
  - right. rewrite HclkrZ Hlenr. split_and!; lia.
Qed.

(** [types_cells_id_bounds] over the 2-conjunct big-sep (issue #28 stage D). *)
Lemma types_cells_id_bounds2 (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
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

(** A split preserves each type's model document, and the map's domain. *)
Lemma split_types_preserve (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k o : nat) (rloc : loc)
    (cw : item_cell) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  ∀ p ts', <[parent := MkTypeState (split_cells cells k o rloc) arr]> types !! p = Some ts' ->
    ∃ ts, types !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
          run_flatten (ty_cells ts') = run_flatten (ty_cells ts).
Proof.
  move=> Htypes Hck p ts' Hp.
  destruct (decide (p = parent)) as [-> | Hne].
  - rewrite lookup_insert_eq in Hp. injection Hp as <-.
    exists (MkTypeState cells arr). split_and!; [exact Htypes | done |].
    rewrite /= (split_cells_flatten cells k o rloc cw Hck) //.
  - rewrite lookup_insert_ne in Hp; last congruence.
    exists ts'. split_and!; done.
Qed.

(** Coverage transport across a split: a pool cell covering a clock is
    replaced by a covering pool cell of the split map (one of the halves
    when the covered cell IS the split one). *)
Lemma split_pool_cover (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) (ccl : w64) (clkZ : Z) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z ->
  (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) < 2^64)%Z ->
  rloc ∉ (ic_loc <$> all_cells types) ->
  ∀ c, c ∈ all_cells types ->
    cell_client c = ccl ->
    (uint.Z (cell_clock c) <= clkZ)%Z ->
    (clkZ < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z ->
    ∃ c', c' ∈ all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types) ∧
          cell_client c' = ccl ∧
          (uint.Z (cell_clock c') <= clkZ)%Z ∧
          (clkZ < uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')))%Z ∧
          ic_parent c' = ic_parent c ∧
          (c' = c ∨ (c = cw ∧ (1 < length (ic_run cw))%nat ∧
                     (ic_loc c' = ic_loc cw ∨
                      ic_loc c' ∉ (ic_loc <$> all_cells types)))).
Proof.
  move=> Htypes Hck Hrunwf Ho Hckbnd Hfitscw Hfresh c Hc Hccl Hle Hlt.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  rewrite Hold in Hc. apply elem_of_cons in Hc as [-> | Hc].
  - destruct (split_cell_cover cw o rloc clkZ Hrunwf Ho Hckbnd Hfitscw Hle Hlt)
      as [(Hd & Hle' & Hlt') | (Hd & Hle' & Hlt')].
    + exists (split_cell_left cw o). split_and!;
        [rewrite Hnew; apply list_elem_of_here | rewrite Hclientl; exact Hccl | exact Hle' | exact Hlt' | done |].
      right. split_and!; [done | lia | by left].
    + exists (split_cell_right cw o rloc). split_and!;
        [rewrite Hnew; apply elem_of_cons; right; apply list_elem_of_here
        | rewrite Hclientr; exact Hccl | exact Hle' | exact Hlt' | done |].
      right. split_and!; [done | lia | by right].
  - exists c. split_and!;
      [rewrite Hnew; apply elem_of_cons; right; apply elem_of_cons; by right
      | exact Hccl | exact Hle | exact Hlt | done | by left].
Qed.

(** Cells away from the split location survive a split verbatim. *)
Lemma split_pool_stable (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k o : nat) (rloc : loc)
    (cw : item_cell) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  ∀ c, c ∈ all_cells types -> ic_loc c ≠ ic_loc cw ->
    c ∈ all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types).
Proof.
  move=> Htypes Hck c Hc Hlocne.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  rewrite Hold in Hc. apply elem_of_cons in Hc as [-> | Hc].
  { exfalso. exact (Hlocne eq_refl). }
  rewrite Hnew. apply elem_of_cons; right. apply elem_of_cons; by right.
Qed.

(** A split grows only the split client's run list, by one. *)
Lemma split_pool_client_run_len (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) (kc : w64) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (length (client_run (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types) kc)
   <= S (length (client_run types kc)))%nat.
Proof.
  move=> Htypes Hck Hrunwf Ho.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  rewrite /client_run.
  have Hmsl : ∀ l : list item_cell, length (merge_sort cell_le l) = length l.
  { move=> l. apply Permutation_length. apply merge_sort_Permutation. }
  rewrite !Hmsl.
  have -> : length (filter (λ c, cell_client c = kc)
              (all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types)))
          = length (filter (λ c, cell_client c = kc)
              (split_cell_left cw o :: split_cell_right cw o rloc :: rest)).
  { apply Permutation_length. by rewrite Hnew. }
  have -> : length (filter (λ c, cell_client c = kc) (all_cells types))
          = length (filter (λ c, cell_client c = kc) (cw :: rest)).
  { apply Permutation_length. by rewrite Hold. }
  rewrite !filter_cons Hclientl Hclientr.
  case_decide; simpl; lia.
Qed.

(* ----- invariant-carrying split wrappers (issue #28 stage D2b) ------------
   The D1b heap specs packaged with the D1c/D2a pool bookkeeping: pool
   invariants out for pool invariants in, plus the transport facts [repair]
   needs to sequence two splits (document/domain preservation, coverage
   transport with provenance, stability away from the split location, run
   list growth) and the boundary cell itself. *)

Definition pool_invs (types : gmap loc type_state) : Prop :=
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ∧
  NoDup (ic_loc <$> all_cells types) ∧
  cells_range_disjoint (all_cells types) ∧
  (∀ c, c ∈ all_cells types -> cell_origin_clk c).

Definition split_step_facts (types types' : gmap loc type_state) (w : item_cell) : Prop :=
  (∀ p ts', types' !! p = Some ts' ->
     ∃ ts, types !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
           run_flatten (ty_cells ts') = run_flatten (ty_cells ts)) ∧
  (∀ p, is_Some (types !! p) -> is_Some (types' !! p)) ∧
  (∀ kc, (length (client_run types' kc) <= S (length (client_run types kc)))%nat) ∧
  (∀ c, c ∈ all_cells types -> ic_loc c ≠ ic_loc w -> c ∈ all_cells types') ∧
  (∀ (ccl : w64) (clkZ : Z) (c : item_cell), c ∈ all_cells types ->
     cell_client c = ccl -> (uint.Z (cell_clock c) <= clkZ)%Z ->
     (clkZ < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z ->
     ∃ c', c' ∈ all_cells types' ∧ cell_client c' = ccl ∧
           (uint.Z (cell_clock c') <= clkZ)%Z ∧
           (clkZ < uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')))%Z ∧
           ic_parent c' = ic_parent c ∧
           (c' = c ∨ (c = w ∧ (1 < length (ic_run w))%nat ∧
                      (ic_loc c' = ic_loc w ∨
                       ic_loc c' ∉ (ic_loc <$> all_cells types))))) ∧
  (∀ p ts ts', types !! p = Some ts -> types' !! p = Some ts' ->
     Forall cell_unit (ty_cells ts) -> ts' = ts).

Lemma wp_store__splitAtAndGetLeft_inv (s mref : loc) (idv : yjs.id.t)
    (types : gmap loc type_state) (cw : item_cell) :
  cw ∈ all_cells types ->
  cell_client cw = idv.(yjs.id.clientId') ->
  (uint.Z (cell_clock cw) <= uint.Z idv.(yjs.id.clock'))%Z ->
  (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  pool_invs types ->
  ((1 < length (ic_run cw))%nat ->
   (Z.of_nat (length (client_run types (cell_client cw))) + 1 < 2^63)%Z) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetLeft" #idv
  {{{ (types' : gmap loc type_state), RET (#(ic_loc cw), #true);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜pool_invs types'⌝ ∗ ⌜split_step_facts types types' cw⌝ ∗
      ⌜∃ cL, cL ∈ all_cells types' ∧ ic_loc cL = ic_loc cw ∧
             cell_client cL = idv.(yjs.id.clientId') ∧
             (uint.Z (cell_clock cL) + Z.of_nat (length (ic_run cL))
              = uint.Z idv.(yjs.id.clock') + 1)%Z ∧
             ic_parent cL = ic_parent cw⌝ }}}.
Proof using Type*.
  move=> Hcwmem Hcwcc Hcwle Hcwlt [Hfits [Hnodup [Hrangedisj Horiginclk]]] Hrunlen.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  have Hcoords := Hcwmem.
  apply all_cells_elem_of in Hcoords.
  destruct Hcoords as (parent & ts & Htypes0 & Hcts).
  destruct ts as [cells arr]. simpl in Hcts.
  apply list_elem_of_lookup_1 in Hcts as [k Hck].
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds.
  have Hckbnd : (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z := proj2 (Hbnds cw Hcwmem).
  iDestruct (types_cell_acc_gen types cw Hcwmem with "Htypes") as "Hacc".
  iNamed "Hacc".
  iDestruct ("Hback" with "Hval") as "Htypes".
  have Hrunwf := Hrun.
  have Hfitscw := Hfits cw Hcwmem.
  have Hlenpos : (1 <= Z.of_nat (length (ic_run cw)))%Z.
  { destruct Hrunwf as [Hne0 _]. destruct (ic_run cw) as [|? ?]; [done | simpl; lia]. }
  wp_apply (wp_store__splitAtAndGetLeft_range s mref idv types parent cells arr k cw
              Htypes0 Hck Hcwcc Hcwle Hcwlt Hfits Hnodup Hrangedisj Hrunlen
              with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
  iIntros (types') "(Hitemsf & Hitemmap & Htypes & %Hbranch)".
  destruct Hbranch as [[Hoeq ->] | [Holt2 (rloc & Hrnn & Hrfresh & ->)]].
  - (* no split: the run already ends at the id *)
    iApply ("HΦ" $! types).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. split_and!.
    + split_and!; [exact Hfits | exact Hnodup | exact Hrangedisj | exact Horiginclk].
    + split_and!.
      * move=> p ts' Hp. exists ts'. split_and!; done.
      * move=> p Hp. exact Hp.
      * move=> kc. lia.
      * move=> c Hc _. exact Hc.
      * move=> ccl clkZ c Hc Hccl Hle2 Hlt2. exists c. split_and!; try done. by left.
      * move=> p ts0 ts0' Hp Hp' _. congruence.
    + exists cw. split_and!; [exact Hcwmem | done | exact Hcwcc | | done].
      clear -Hoeq Hcwle Hcwlt Hlenpos. word.
  - (* split just after the id *)
    have Ho2 : (0 < (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1
                < length (ic_run cw))%nat by lia.
    iApply ("HΦ" $! (<[parent := MkTypeState
        (split_cells cells k ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc)
        arr]> types)).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. split_and!.
    + split_and!.
      * exact (split_pool_fits types parent cells arr k cw _ rloc Htypes0 Hck Hrunwf Ho2 Hckbnd Hfits).
      * exact (split_pool_locdup types parent cells arr k cw _ rloc Htypes0 Hck Hrfresh Hnodup).
      * exact (split_pool_rangedisj types parent cells arr k cw _ rloc Htypes0 Hck Hrunwf Ho2 Hckbnd Hfitscw Hnodup Hrangedisj).
      * exact (split_pool_originclk types parent cells arr k cw _ rloc Htypes0 Hck Hrunwf Ho2 Horiginclk).
    + split_and!.
      * exact (split_types_preserve types parent cells arr k _ rloc cw Htypes0 Hck).
      * move=> p Hp. destruct (decide (p = parent)) as [-> | Hne].
        { rewrite lookup_insert_eq. eauto. }
        { rewrite lookup_insert_ne; [exact Hp | congruence]. }
      * move=> kc. exact (split_pool_client_run_len types parent cells arr k cw _ rloc kc Htypes0 Hck Hrunwf Ho2).
      * move=> c Hc Hlocne. exact (split_pool_stable types parent cells arr k _ rloc cw Htypes0 Hck c Hc Hlocne).
      * move=> ccl clkZ c Hc Hccl Hle2 Hlt2.
        exact (split_pool_cover types parent cells arr k cw _ rloc ccl clkZ Htypes0 Hck Hrunwf Ho2 Hckbnd Hfitscw Hrfresh c Hc Hccl Hle2 Hlt2).
      * move=> p ts0 ts0' Hp Hp' Hunit0.
        destruct (decide (p = parent)) as [-> | Hnep].
        { rewrite Htypes0 in Hp. injection Hp as <-.
          rewrite lookup_insert_eq in Hp'. injection Hp' as <-.
          exfalso. simpl in Hunit0.
          have Hu := Forall_lookup_1 _ _ _ _ Hunit0 Hck.
          rewrite /cell_unit in Hu. lia. }
        { rewrite lookup_insert_ne in Hp'; last congruence. congruence. }
    + destruct (split_pool_perm types parent cells arr k cw
                  ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc Htypes0 Hck)
        as (rest & Hold & Hnew).
      destruct (split_cell_facts cw
                  ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc Hrunwf Ho2)
        as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
      exists (split_cell_left cw ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1)).
      split_and!.
      * rewrite Hnew. apply list_elem_of_here.
      * done.
      * rewrite Hclientl. exact Hcwcc.
      * rewrite Hclockl Hlenl. clear -Hcwle Hcwlt Hlenpos. word.
      * done.
Qed.

Lemma wp_store__splitAtAndGetRight_inv (s mref : loc) (idv : yjs.id.t)
    (types : gmap loc type_state) (cw : item_cell) :
  cw ∈ all_cells types ->
  cell_client cw = idv.(yjs.id.clientId') ->
  (uint.Z (cell_clock cw) <= uint.Z idv.(yjs.id.clock'))%Z ->
  (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  pool_invs types ->
  ((1 < length (ic_run cw))%nat ->
   (Z.of_nat (length (client_run types (cell_client cw))) + 1 < 2^63)%Z) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetRight" #idv
  {{{ (rl : loc) (types' : gmap loc type_state), RET (#rl, #true);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜pool_invs types'⌝ ∗ ⌜split_step_facts types types' cw⌝ ∗
      ⌜∃ cR, cR ∈ all_cells types' ∧ ic_loc cR = rl ∧
             cell_client cR = idv.(yjs.id.clientId') ∧
             (uint.Z (cell_clock cR) = uint.Z idv.(yjs.id.clock'))%Z ∧
             ic_parent cR = ic_parent cw⌝ }}}.
Proof using Type*.
  move=> Hcwmem Hcwcc Hcwle Hcwlt [Hfits [Hnodup [Hrangedisj Horiginclk]]] Hrunlen.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  have Hcoords := Hcwmem.
  apply all_cells_elem_of in Hcoords.
  destruct Hcoords as (parent & ts & Htypes0 & Hcts).
  destruct ts as [cells arr]. simpl in Hcts.
  apply list_elem_of_lookup_1 in Hcts as [k Hck].
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds.
  have Hckbnd : (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z := proj2 (Hbnds cw Hcwmem).
  iDestruct (types_cell_acc_gen types cw Hcwmem with "Htypes") as "Hacc".
  iNamed "Hacc".
  iDestruct ("Hback" with "Hval") as "Htypes".
  have Hrunwf := Hrun.
  have Hfitscw := Hfits cw Hcwmem.
  have Hlenpos : (1 <= Z.of_nat (length (ic_run cw)))%Z.
  { destruct Hrunwf as [Hne0 _]. destruct (ic_run cw) as [|? ?]; [done | simpl; lia]. }
  wp_apply (wp_store__splitAtAndGetRight_range s mref idv types parent cells arr k cw
              Htypes0 Hck Hcwcc Hcwle Hcwlt Hfits Hnodup Hrangedisj Hrunlen
              with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
  iIntros (rl types') "(Hitemsf & Hitemmap & Htypes & %Hbranch)".
  destruct Hbranch as [[Hoeq [-> ->]] | [Hopos (Hrlnn & Hrlfresh & ->)]].
  - (* no split: the run already starts at the id *)
    iApply ("HΦ" $! (ic_loc cw) types).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. split_and!.
    + split_and!; [exact Hfits | exact Hnodup | exact Hrangedisj | exact Horiginclk].
    + split_and!.
      * move=> p ts' Hp. exists ts'. split_and!; done.
      * move=> p Hp. exact Hp.
      * move=> kc. lia.
      * move=> c Hc _. exact Hc.
      * move=> ccl clkZ c Hc Hccl Hle2 Hlt2. exists c. split_and!; try done. by left.
      * move=> p ts0 ts0' Hp Hp' _. congruence.
    + exists cw. split_and!; [exact Hcwmem | done | exact Hcwcc | | done].
      clear -Hoeq Hcwle. word.
  - (* split at the offset: the fresh right half starts at the id *)
    have Ho2 : (0 < (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))
                < length (ic_run cw))%nat.
    { split; [exact Hopos |]. clear -Hcwle Hcwlt. word. }
    iApply ("HΦ" $! rl (<[parent := MkTypeState
        (split_cells cells k (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl)
        arr]> types)).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. split_and!.
    + split_and!.
      * exact (split_pool_fits types parent cells arr k cw _ rl Htypes0 Hck Hrunwf Ho2 Hckbnd Hfits).
      * exact (split_pool_locdup types parent cells arr k cw _ rl Htypes0 Hck Hrlfresh Hnodup).
      * exact (split_pool_rangedisj types parent cells arr k cw _ rl Htypes0 Hck Hrunwf Ho2 Hckbnd Hfitscw Hnodup Hrangedisj).
      * exact (split_pool_originclk types parent cells arr k cw _ rl Htypes0 Hck Hrunwf Ho2 Horiginclk).
    + split_and!.
      * exact (split_types_preserve types parent cells arr k _ rl cw Htypes0 Hck).
      * move=> p Hp. destruct (decide (p = parent)) as [-> | Hne].
        { rewrite lookup_insert_eq. eauto. }
        { rewrite lookup_insert_ne; [exact Hp | congruence]. }
      * move=> kc. exact (split_pool_client_run_len types parent cells arr k cw _ rl kc Htypes0 Hck Hrunwf Ho2).
      * move=> c Hc Hlocne. exact (split_pool_stable types parent cells arr k _ rl cw Htypes0 Hck c Hc Hlocne).
      * move=> ccl clkZ c Hc Hccl Hle2 Hlt2.
        exact (split_pool_cover types parent cells arr k cw _ rl ccl clkZ Htypes0 Hck Hrunwf Ho2 Hckbnd Hfitscw Hrlfresh c Hc Hccl Hle2 Hlt2).
      * move=> p ts0 ts0' Hp Hp' Hunit0.
        destruct (decide (p = parent)) as [-> | Hnep].
        { rewrite Htypes0 in Hp. injection Hp as <-.
          rewrite lookup_insert_eq in Hp'. injection Hp' as <-.
          exfalso. simpl in Hunit0.
          have Hu := Forall_lookup_1 _ _ _ _ Hunit0 Hck.
          rewrite /cell_unit in Hu. lia. }
        { rewrite lookup_insert_ne in Hp'; last congruence. congruence. }
    + destruct (split_pool_perm types parent cells arr k cw
                  (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl Htypes0 Hck)
        as (rest & Hold & Hnew).
      destruct (split_cell_facts cw
                  (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl Hrunwf Ho2)
        as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
      have HclkZ : uint.Z (cell_clock cw) = Z.of_nat (clock (item_id (run_head cw))).
      { rewrite /cell_clock. word. }
      exists (split_cell_right cw (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl).
      split_and!.
      * rewrite Hnew. apply elem_of_cons; right. apply list_elem_of_here.
      * done.
      * rewrite Hclientr. exact Hcwcc.
      * rewrite Hclockr.
        have Hbo : (Z.of_nat (clock (item_id (run_head cw))
                    + (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))) < 2^64)%Z.
        { clear -HclkZ Hfitscw Hcwlt Hcwle. lia. }
        clear -HclkZ Hbo Hcwle. word.
      * done.
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

(* ----- the general repair (issue #28 stage D2b) ---------------------------
   [store.repair] over the invariant-carrying split wrappers: the origin ids
   may address ANY char of their covering cells' runs; the clean-end /
   clean-start splits put them on run boundaries. The two splits are
   sequenced by the wrappers' transport records. *)

(** Loc-NoDup makes the location injective on the pool. *)
Lemma pool_loc_inj (pool : list item_cell) :
  NoDup (ic_loc <$> pool) ->
  ∀ x y, x ∈ pool → y ∈ pool → ic_loc x = ic_loc y → x = y.
Proof.
  move=> Hnd x y Hx Hy Hxy.
  apply list_elem_of_lookup_1 in Hx as [ix Hix].
  apply list_elem_of_lookup_1 in Hy as [iy Hiy].
  have Hlix : (ic_loc <$> pool) !! ix = Some (ic_loc y) by (rewrite list_lookup_fmap Hix /= Hxy //).
  have Hliy : (ic_loc <$> pool) !! iy = Some (ic_loc y) by (rewrite list_lookup_fmap Hiy //).
  have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnd Hlix Hliy.
  congruence.
Qed.

(** What [repair] guarantees about the type map: per-type model documents and
    the domain survive, and each client's run list grows by at most the two
    possible splits. *)
Definition repair_types_facts (types types2 : gmap loc type_state) : Prop :=
  (∀ p ts', types2 !! p = Some ts' ->
     ∃ ts, types !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
           run_flatten (ty_cells ts') = run_flatten (ty_cells ts)) ∧
  (∀ p, is_Some (types !! p) -> is_Some (types2 !! p)) ∧
  (∀ kc, (length (client_run types2 kc) <= 2 + length (client_run types kc))%nat) ∧
  (∀ p ts ts', types !! p = Some ts -> types2 !! p = Some ts' ->
     Forall cell_unit (ty_cells ts) -> ts' = ts).

Lemma repair_types_facts_refl (types : gmap loc type_state) :
  repair_types_facts types types.
Proof.
  split_and!.
  - move=> p ts' Hp. exists ts'. split_and!; done.
  - move=> p Hp. exact Hp.
  - move=> kc. lia.
  - move=> p ts ts' Hp Hp' _. congruence.
Qed.

Lemma split_step_facts_single (types types1 : gmap loc type_state) (w : item_cell) :
  split_step_facts types types1 w -> repair_types_facts types types1.
Proof.
  move=> H. destruct H as (Hp & Hd & Hr & _ & _ & Hu).
  split_and!; [exact Hp | exact Hd | move=> kc; have := Hr kc; lia | exact Hu].
Qed.

Lemma split_step_facts_compose (types types1 types2 : gmap loc type_state) (w1 w2 : item_cell) :
  split_step_facts types types1 w1 -> split_step_facts types1 types2 w2 ->
  repair_types_facts types types2.
Proof.
  move=> H1 H2.
  destruct H1 as (Hp1 & Hd1 & Hr1 & _ & _ & Hu1).
  destruct H2 as (Hp2 & Hd2 & Hr2 & _ & _ & Hu2).
  split_and!.
  - move=> p ts2 Hp.
    destruct (Hp2 p ts2 Hp) as (ts1 & Hp1' & Ha2 & Hf2).
    destruct (Hp1 p ts1 Hp1') as (ts0 & Hp0 & Ha1 & Hf1).
    exists ts0. split_and!; [exact Hp0 | congruence | congruence].
  - move=> p Hp. exact (Hd2 p (Hd1 p Hp)).
  - move=> kc. have := Hr1 kc. have := Hr2 kc. lia.
  - move=> p ts ts2 Hpa Hpb Hunit.
    destruct (Hd1 p (mk_is_Some _ _ Hpa)) as [ts1 Hpm].
    have Hts1 : ts1 = ts := Hu1 p ts ts1 Hpa Hpm Hunit.
    subst ts1.
    exact (Hu2 p ts ts2 Hpm Hpb Hunit).
Qed.

(** [store.repair], general splitting form (issue #28 stage D2b): the origin
    ids address arbitrary chars of their covering witness cells; repair puts
    both on run boundaries by splitting, and the item comes back linked to
    the boundary cells. The same-run premise (equal witnesses force the left
    origin strictly below the right one in clock) is what item validity
    provides: within one run, doc order is clock order, and an item's origin
    precedes its right origin. *)
Lemma wp_store__repair_split (s mref tref item_l pname : loc)
    (input : IntegrateInput (A := A)) (opn : option go_string)
    (types : gmap loc type_state) (bind : gmap P loc)
    (ocL ocR : option item_cell) (p_t : loc) :
  match in_originId input, ocL with
  | Some oid, Some c => c ∈ all_cells types ∧
      clientId (item_id (run_head c)) = clientId oid ∧
      (clock (item_id (run_head c)) <= clock oid)%nat ∧
      (clock oid < clock (item_id (run_head c)) + length (ic_run c))%nat
  | None, None => True
  | _, _ => False
  end ->
  match in_rightOriginId input, ocR with
  | Some oid, Some c => c ∈ all_cells types ∧
      clientId (item_id (run_head c)) = clientId oid ∧
      (clock (item_id (run_head c)) <= clock oid)%nat ∧
      (clock oid < clock (item_id (run_head c)) + length (ic_run c))%nat
  | None, None => True
  | _, _ => False
  end ->
  match in_originId input, in_rightOriginId input, ocL, ocR with
  | Some a, Some b, Some cL0, Some cR0 => cL0 = cR0 -> (clock a < clock b)%nat
  | _, _, _, _ => True
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
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  (∀ c, c ∈ all_cells types -> cell_origin_clk c) ->
  (∀ c, c ∈ all_cells types -> (1 < length (ic_run c))%nat ->
     (Z.of_nat (length (client_run types (cell_client c))) + 2 < 2^63)%Z) ->
  {{{ is_pkg_init yjs ∗
      own_linked_item item_l input null null null ∗
      is_parent_name pname opn ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "repair" #item_l #pname
  {{{ (lft rgt : loc) (types2 : gmap loc type_state), RET #();
      own_linked_item item_l input p_t lft rgt ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types2 ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types2,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜pool_invs types2⌝ ∗
      ⌜repair_types_facts types types2⌝ ∗
      ⌜match in_originId input, ocL with
       | Some oid, Some c0 => lft = ic_loc c0 ∧
           ∃ cL', cL' ∈ all_cells types2 ∧ ic_loc cL' = lft ∧
             cell_client cL' = W64 (clientId oid) ∧
             (uint.Z (cell_clock cL') + Z.of_nat (length (ic_run cL'))
              = Z.of_nat (clock oid) + 1)%Z ∧
             ic_parent cL' = ic_parent c0
       | None, None => lft = null
       | _, _ => False
       end⌝ ∗
      ⌜match in_rightOriginId input, ocR with
       | Some oid, Some c0 =>
           ∃ cR', cR' ∈ all_cells types2 ∧ ic_loc cR' = rgt ∧
             cell_client cR' = W64 (clientId oid) ∧
             (uint.Z (cell_clock cR') = Z.of_nat (clock oid))%Z ∧
             ic_parent cR' = ic_parent c0
       | None, None => rgt = null
       | _, _ => False
       end⌝ }}}.
Proof using Type*.
  move=> HwL HwR Hsame Hwpar Hfits Hnodup Hrangedisj Horiginclk Hrunlen.
  iIntros (Φ) "(#Hpkg & Hlinked & #HisPN & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes) HΦ".
  iDestruct "Hlinked" as (iv oleft oright) "(Hraw & %Hfl & %Hfr & %Hfpar & %Hflags & %Hrunc)".
  iNamed "Hraw".
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds0.
  have Hpinvs : pool_invs types by (split_and!; assumption).

  wp_method_call. wp_call. wp_call. wp_auto.
  destruct oleft as [idvL|].
  - (* left origin present: clean-end split *)
    have HinlS : input.(in_originId) = Some (toYjsId idvL) by rewrite -Hin_l //.
    rewrite HinlS in HwL. destruct ocL as [cL|]; last done.
    destruct HwL as (HcLmem & HcLcl & HcLle & HcLlt).
    iDestruct "Holeft" as "[%HnnL #HolC]".
    rewrite (bool_decide_eq_false_2 (iv.(yjs.item.originLeftId') = null) HnnL) /=.
    wp_auto.
    have HcLbnd := proj2 (Hbnds0 cL HcLmem).
    have HcLccw : cell_client cL = idvL.(yjs.id.clientId').
    { rewrite /cell_client. move: HcLcl. rewrite /toYjsId /=. move=> ->. word. }
    have HcLleZ : (uint.Z (cell_clock cL) <= uint.Z idvL.(yjs.id.clock'))%Z.
    { move: HcLle. rewrite /toYjsId /= /cell_clock. move=> H. word. }
    have HcLltZ : (uint.Z idvL.(yjs.id.clock') < uint.Z (cell_clock cL) + Z.of_nat (length (ic_run cL)))%Z.
    { move: HcLlt. rewrite /toYjsId /= /cell_clock. move=> H. word. }
    have HrunlenL : (1 < length (ic_run cL))%nat ->
        (Z.of_nat (length (client_run types (cell_client cL))) + 1 < 2^63)%Z.
    { move=> Hgt. have := Hrunlen cL HcLmem Hgt. lia. }
    wp_apply (wp_store__splitAtAndGetLeft_inv s mref idvL types cL
                HcLmem HcLccw HcLleZ HcLltZ Hpinvs HrunlenL
                with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
    iIntros (types1) "(Hitemsf & Hitemmap & Htypes & %Hpinvs1 & %Hstep1 & %HbdL)".
    destruct HbdL as (cL1 & HcL1mem & HcL1loc & HcL1cl & HcL1end & HcL1par).
    wp_auto.
    destruct oright as [idvR|].
    + (* right origin present: relocate the witness, clean-start split *)
      have HinrS : input.(in_rightOriginId) = Some (toYjsId idvR) by rewrite -Hin_r //.
      rewrite HinrS in HwR. destruct ocR as [cR|]; last done.
      destruct HwR as (HcRmem & HcRcl & HcRle & HcRlt).
      rewrite HinlS HinrS in Hsame.
      have Hsame' : cL = cR -> (clock (toYjsId idvL) < clock (toYjsId idvR))%nat := Hsame.
      iDestruct "Horight" as "[%HnnR #HorC]".
      rewrite (bool_decide_eq_false_2 (iv.(yjs.item.originRightId') = null) HnnR) /=.
      wp_auto.
      have HcRbnd := proj2 (Hbnds0 cR HcRmem).
      have HcRccw : cell_client cR = idvR.(yjs.id.clientId').
      { rewrite /cell_client. move: HcRcl. rewrite /toYjsId /=. move=> ->. word. }
      have HcRleZ : (uint.Z (cell_clock cR) <= uint.Z idvR.(yjs.id.clock'))%Z.
      { move: HcRle. rewrite /toYjsId /= /cell_clock. move=> H. word. }
      have HcRltZ : (uint.Z idvR.(yjs.id.clock') < uint.Z (cell_clock cR) + Z.of_nat (length (ic_run cR)))%Z.
      { move: HcRlt. rewrite /toYjsId /= /cell_clock. move=> H. word. }
      have Hstep1' := Hstep1.
      destruct Hstep1' as (Hpres1 & Hdom1 & Hrl1 & Hstable1 & Hcover1 & Hunitp1).
      destruct (Hcover1 idvR.(yjs.id.clientId') (uint.Z idvR.(yjs.id.clock')) cR HcRmem HcRccw HcRleZ HcRltZ)
        as (cR1 & HcR1mem & HcR1cc & HcR1le & HcR1lt & HcR1parw & Hprov).
      destruct Hpinvs1 as (Hfits1 & Hnodup1 & Hrangedisj1 & Horiginclk1).
      have Hlocne : ic_loc cL1 ≠ ic_loc cR1.
      { move=> Heqloc.
        have Hceq : cL1 = cR1 := pool_loc_inj (all_cells types1) Hnodup1 _ _ HcL1mem HcR1mem Heqloc.
        have HleRL : (uint.Z idvR.(yjs.id.clock') <= uint.Z idvL.(yjs.id.clock'))%Z.
        { rewrite -Hceq in HcR1lt. clear -HcR1lt HcL1end. lia. }
        have Hfire : cL = cR -> False.
        { move=> HeqLR. have := Hsame' HeqLR. rewrite /toYjsId /=. move=> H.
          clear -H HleRL. word. }
        destruct Hprov as [Hc'c | [HcRcw _]].
        - have HlocRL : ic_loc cR = ic_loc cL.
          { rewrite -Hc'c -Hceq HcL1loc //. }
          exact (Hfire (eq_sym (pool_loc_inj (all_cells types) Hnodup _ _ HcRmem HcLmem HlocRL))).
        - exact (Hfire (eq_sym HcRcw)). }
      have HrunlenR : (1 < length (ic_run cR1))%nat ->
          (Z.of_nat (length (client_run types1 (cell_client cR1))) + 1 < 2^63)%Z.
      { move=> Hgt.
        have Hb : (Z.of_nat (length (client_run types (cell_client cR1))) + 2 < 2^63)%Z.
        { destruct Hprov as [Hc'c | [HcRcw [HgtL _]]].
          - rewrite Hc'c in Hgt HcR1cc |- *. rewrite HcR1cc.
            rewrite -HcRccw. exact (Hrunlen cR HcRmem Hgt).
          - rewrite HcR1cc.
            have Hcleq : idvR.(yjs.id.clientId') = cell_client cL.
            { rewrite -HcRccw HcRcw //. }
            rewrite Hcleq. exact (Hrunlen cL HcLmem HgtL). }
        have := Hrl1 (cell_client cR1). lia. }
      have Hpinvs1' : pool_invs types1 by (split_and!; assumption).
      wp_apply (wp_store__splitAtAndGetRight_inv s mref idvR types1 cR1
                  HcR1mem HcR1cc HcR1le HcR1lt Hpinvs1' HrunlenR
                  with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
      iIntros (rl types2) "(Hitemsf & Hitemmap & Htypes & %Hpinvs2 & %Hstep2 & %HbdR)".
      destruct HbdR as (cR2 & HcR2mem & HcR2loc & HcR2cl & HcR2clk & HcR2par).
      wp_auto.
      have Hstep2' := Hstep2.
      destruct Hstep2' as (Hpres2 & Hdom2 & Hrl2 & Hstable2 & Hcover2 & Hunitp2).
      have HcL2mem : cL1 ∈ all_cells types2 := Hstable2 cL1 HcL1mem Hlocne.
      have HparR : ic_parent cR2 = ic_parent cR by rewrite HcR2par HcR1parw //.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType s tref (DfracOwn 1) bind nm p_t Hwpar
                    with "[$Htypesf $Htypesmap]").
        iIntros "(Htypesf & Htypesmap)".
        wp_auto.
        iApply ("HΦ" $! (ic_loc cL) rl types2).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, (Some idvL), (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs2 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_compose types types1 types2 cL cR1 Hstep1 Hstep2). }
        { rewrite HinlS /=. split; [done |].
          exists cL1. split_and!;
            [exact HcL2mem | rewrite HcL1loc // | | | rewrite HcL1par //].
          - rewrite HcL1cl /toYjsId /=. word.
          - move: HcL1end. rewrite /toYjsId /=. move=> H. word. }
        { rewrite HinrS /=.
          exists cR2. split_and!;
            [exact HcR2mem | exact HcR2loc | | | exact HparR].
          - rewrite HcR2cl /toYjsId /=. word.
          - move: HcR2clk. rewrite /toYjsId /=. move=> H. word. }
      * (* Parent::None: borrow from the resolved left neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        iDestruct (types_cell_acc_gen types2 cL1 HcL2mem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCL.
        iEval (rewrite HcL1loc) in "Hval".
        wp_auto.
        rewrite (bool_decide_eq_false_2 (cL.(ic_loc) = null) ltac:(rewrite -HcL1loc; exact HnnCL)) /=.
        wp_auto.
        iEval (rewrite -HcL1loc) in "Hval".
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar HcL1par Hwpar.
        iApply ("HΦ" $! (ic_loc cL) rl types2).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, (Some idvL), (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs2 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_compose types types1 types2 cL cR1 Hstep1 Hstep2). }
        { rewrite HinlS /=. split; [done |].
          exists cL1. split_and!;
            [exact HcL2mem | rewrite HcL1loc // | | | rewrite HcL1par //].
          - rewrite HcL1cl /toYjsId /=. word.
          - move: HcL1end. rewrite /toYjsId /=. move=> H. word. }
        { rewrite HinrS /=.
          exists cR2. split_and!;
            [exact HcR2mem | exact HcR2loc | | | exact HparR].
          - rewrite HcR2cl /toYjsId /=. word.
          - move: HcR2clk. rewrite /toYjsId /=. move=> H. word. }
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
        wp_apply (wp_store__getOrCreateYType s tref (DfracOwn 1) bind nm p_t Hwpar
                    with "[$Htypesf $Htypesmap]").
        iIntros "(Htypesf & Htypesmap)".
        wp_auto.
        iApply ("HΦ" $! (ic_loc cL) null types1).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, (Some idvL), None. rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs1 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_single types types1 cL Hstep1). }
        { rewrite HinlS /=. split; [done |].
          exists cL1. split_and!;
            [exact HcL1mem | rewrite HcL1loc // | | | rewrite HcL1par //].
          - rewrite HcL1cl /toYjsId /=. word.
          - move: HcL1end. rewrite /toYjsId /=. move=> H. word. }
        { rewrite HinrN //. }
      * (* Parent::None: borrow from the resolved left neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        iDestruct (types_cell_acc_gen types1 cL1 HcL1mem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCL.
        iEval (rewrite HcL1loc) in "Hval".
        wp_auto.
        rewrite (bool_decide_eq_false_2 (cL.(ic_loc) = null) ltac:(rewrite -HcL1loc; exact HnnCL)) /=.
        wp_auto.
        iEval (rewrite -HcL1loc) in "Hval".
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar HcL1par Hwpar.
        iApply ("HΦ" $! (ic_loc cL) null types1).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, (Some idvL), None. rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs1 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_single types types1 cL Hstep1). }
        { rewrite HinlS /=. split; [done |].
          exists cL1. split_and!;
            [exact HcL1mem | rewrite HcL1loc // | | | rewrite HcL1par //].
          - rewrite HcL1cl /toYjsId /=. word.
          - move: HcL1end. rewrite /toYjsId /=. move=> H. word. }
        { rewrite HinrN //. }
  - (* no left origin *)
    have HinlN : input.(in_originId) = None by rewrite -Hin_l //.
    rewrite HinlN in HwL. destruct ocL as [cL|]; first done.
    iDestruct "Holeft" as "%HnL".
    rewrite (bool_decide_eq_true_2 (iv.(yjs.item.originLeftId') = null) HnL) /=.
    wp_auto.
    destruct oright as [idvR|].
    + (* right origin present: clean-start split, no relocation *)
      have HinrS : input.(in_rightOriginId) = Some (toYjsId idvR) by rewrite -Hin_r //.
      rewrite HinrS in HwR. destruct ocR as [cR|]; last done.
      destruct HwR as (HcRmem & HcRcl & HcRle & HcRlt).
      iDestruct "Horight" as "[%HnnR #HorC]".
      rewrite (bool_decide_eq_false_2 (iv.(yjs.item.originRightId') = null) HnnR) /=.
      wp_auto.
      have HcRbnd := proj2 (Hbnds0 cR HcRmem).
      have HcRccw : cell_client cR = idvR.(yjs.id.clientId').
      { rewrite /cell_client. move: HcRcl. rewrite /toYjsId /=. move=> ->. word. }
      have HcRleZ : (uint.Z (cell_clock cR) <= uint.Z idvR.(yjs.id.clock'))%Z.
      { move: HcRle. rewrite /toYjsId /= /cell_clock. move=> H. word. }
      have HcRltZ : (uint.Z idvR.(yjs.id.clock') < uint.Z (cell_clock cR) + Z.of_nat (length (ic_run cR)))%Z.
      { move: HcRlt. rewrite /toYjsId /= /cell_clock. move=> H. word. }
      have HrunlenR0 : (1 < length (ic_run cR))%nat ->
          (Z.of_nat (length (client_run types (cell_client cR))) + 1 < 2^63)%Z.
      { move=> Hgt. have := Hrunlen cR HcRmem Hgt. lia. }
      wp_apply (wp_store__splitAtAndGetRight_inv s mref idvR types cR
                  HcRmem HcRccw HcRleZ HcRltZ Hpinvs HrunlenR0
                  with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
      iIntros (rl types2) "(Hitemsf & Hitemmap & Htypes & %Hpinvs2 & %Hstep2 & %HbdR)".
      destruct HbdR as (cR2 & HcR2mem & HcR2loc & HcR2cl & HcR2clk & HcR2par).
      wp_auto.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType s tref (DfracOwn 1) bind nm p_t Hwpar
                    with "[$Htypesf $Htypesmap]").
        iIntros "(Htypesf & Htypesmap)".
        wp_auto.
        iApply ("HΦ" $! null rl types2).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, None, (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs2 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_single types types2 cR Hstep2). }
        { rewrite HinlN //. }
        { rewrite HinrS /=.
          exists cR2. split_and!;
            [exact HcR2mem | exact HcR2loc | | | exact HcR2par].
          - rewrite HcR2cl /toYjsId /=. word.
          - move: HcR2clk. rewrite /toYjsId /=. move=> H. word. }
      * (* Parent::None: borrow from the resolved right neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        have Hfl' : (iv <| yjs.item.right' := rl |>).(yjs.item.left') = null
          by simpl; exact Hfl.
        iDestruct (types_cell_acc_gen types2 cR2 HcR2mem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCR.
        iEval (rewrite HcR2loc) in "Hval".
        wp_auto.
        rewrite (bool_decide_eq_true_2 _ Hfl') /=.
        wp_auto.
        rewrite (bool_decide_eq_false_2 (rl = null) ltac:(rewrite -HcR2loc; exact HnnCR)) /=.
        wp_auto.
        iEval (rewrite -HcR2loc) in "Hval".
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar HcR2par Hwpar.
        iApply ("HΦ" $! null rl types2).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, None, (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs2 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_single types types2 cR Hstep2). }
        { rewrite HinlN //. }
        { rewrite HinrS /=.
          exists cR2. split_and!;
            [exact HcR2mem | exact HcR2loc | | | exact HcR2par].
          - rewrite HcR2cl /toYjsId /=. word.
          - move: HcR2clk. rewrite /toYjsId /=. move=> H. word. }
    + (* no origins at all: Parent::None is ruled out by the premise *)
      have HinrN : input.(in_rightOriginId) = None by rewrite -Hin_r //.
      rewrite HinrN in HwR. destruct ocR as [cR|]; first done.
      iDestruct "Horight" as "%HnR".
      rewrite (bool_decide_eq_true_2 (iv.(yjs.item.originRightId') = null) HnR) /=.
      wp_auto.
      destruct opn as [nm|]; last done.
      iDestruct "HisPN" as "[%HnnP #HpnC]".
      rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
      wp_auto.
      wp_apply (wp_store__getOrCreateYType s tref (DfracOwn 1) bind nm p_t Hwpar
                  with "[$Htypesf $Htypesmap]").
      iIntros "(Htypesf & Htypesmap)".
      wp_auto.
      iApply ("HΦ" $! null null types).
      iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
      iSplitL "Hitem".
      { iExists _, None, None. rewrite /own_fresh_item_raw. simpl.
        iFrame "Hitem".
        iPureIntro. split_and!; try done. }
      iPureIntro. split_and!.
      { split_and!; assumption. }
      { exact (repair_types_facts_refl types). }
      { rewrite HinlN //. }
      { rewrite HinrN //. }
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
    + exact Hlocdup.
    + exact Hrangedisj.
    + exact Hrunfits.
    + exact Horiginclk.
  - iIntros "H". iDestruct "H" as (c h m) "H". iNamed "H". subst c.
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
    iExists client, k, items_mref, types_mref, dset, types, bind, h, m.
    iSplitR "Hseq Htypes"; last by iFrame "Hseq Htypes".
    iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset HtypesAuth Hbinds Hhist".
    iPureIntro. split_and!;
      [exact Hctrt | exact Hcellctr | exact Hlocdup | exact Hrangedisj
      | exact Hrunfits | exact Horiginclk | exact Hbindtypes | exact Hbindinj
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
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  (∀ c, c ∈ all_cells types -> cell_origin_clk c) ->
  {{{ is_pkg_init yjs ∗ own_update sl dq inputs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "applyUpdate" #sl
  {{{ (types' : gmap loc type_state), RET #();
      own_update sl dq inputs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) ∗
      ⌜dom types' = dom types⌝ ∗
      ⌜∀ nm p ts', bind !! nm = Some p -> types' !! p = Some ts' ->
         docm_get m' (RootId nm) = ty_arr ts'⌝ ∗
      ⌜∀ c, c ∈ all_cells types' -> c ∈ all_cells types ∨
         ∃ i ti, inputs !! i = Some ti /\
            cell_client c = W64 (clientId (in_id ti.2)) /\
            cell_clock c = W64 (clock (in_id ti.2))⌝ ∗
      ⌜NoDup (ic_loc <$> all_cells types')⌝ ∗
      ⌜cells_range_disjoint (all_cells types')⌝ ∗
      ⌜∀ c, c ∈ all_cells types' -> cell_origin_clk c⌝ }}}.
Proof using Type*.
  move=> Hreplay Hbindtypes Hbindinj Hmtypes Hbatchbnd Hfresh Hcausal Hnowrap Hnowrapb Hlocdup0 Hrangedisj0 Horiginclk0.
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
        ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
        ⌜Forall cell_unit (ty_cells ts)⌝) ∗
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
           cell_clock c0 = W64 (clock (in_id ti.2))⌝ ∗
    "%Hlocdupj" ∷ ⌜NoDup (ic_loc <$> all_cells typesj)⌝ ∗
    "%Hrangedisjj" ∷ ⌜cells_range_disjoint (all_cells typesj)⌝ ∗
    "%Horiginclkj" ∷ ⌜∀ c0, c0 ∈ all_cells typesj -> cell_origin_clk c0⌝)%I
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
    - move=> c0 Hc0. by left.
    - exact Hlocdup0.
    - exact Hrangedisj0.
    - exact Horiginclk0. }
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
      "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hulen & %Htid & %Hborrow)".
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
    iDestruct (types_entry_pures typesj pj _ Htsj with "Htypes") as %(Hreprj & Hcparj & Hunitcj).
    simpl in Hreprj, Hcparj.
    (* uniform repair witnesses: present origins resolve inside this type's own
       cells (that is where [toItem] found them), so the borrow's parent IS
       [pj]; a named parent is [nmj]'s binding *)
    have Hwits : ∃ (ocL ocR : option item_cell),
      (match in_originId input, ocL with
       | Some oid, Some c => c ∈ all_cells typesj /\ item_id (run_head c) = oid
       | None, None => True
       | _, _ => False
       end) /\
      (match in_rightOriginId input, ocR with
       | Some oid, Some c => c ∈ all_cells typesj /\ item_id (run_head c) = oid
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
        ∃ c, cellsj !! kn = Some c /\ run_head c = it.
      { move=> kn it Hkn. rewrite /cells_repr in Hreprj.
        rewrite Hreprj (run_flatten_singletons cellsj Hunitcj) list_lookup_fmap in Hkn.
        destruct (cellsj !! kn) as [c|] eqn:Hc; last done.
        injection Hkn as <-. by exists c. }
      have HocL : ∃ ocL,
        (match in_originId input, ocL with
         | Some oid, Some c => c ∈ all_cells typesj /\ item_id (run_head c) = oid
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
         | Some oid, Some c => c ∈ all_cells typesj /\ item_id (run_head c) = oid
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
          { rewrite /cells_repr in Hreprj.
            rewrite Hreprj (run_flatten_singletons cellsj Hunitcj) length_fmap //. }
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
        | reflexivity | reflexivity | reflexivity | reflexivity | exact Hulen]. }
    (* general-repair premises (issue #28 U1): covering witnesses from the
       head-exact ones, pool invariants from the loop, and the run-length
       guard vacuous under the unit scaffold *)
    iDestruct (types_unit_all with "Htypes") as %Hunitall0.
    iDestruct (types_cells_id_bounds with "Htypes") as %Hbnds0.
    have Hcellunit : ∀ c, c ∈ all_cells typesj -> cell_unit c.
    { move=> c Hc. apply all_cells_elem_of in Hc. destruct Hc as (p0 & ts0 & Hp0 & Hcts0).
      exact (proj1 (Forall_forall _ _) (Hunitall0 p0 ts0 Hp0) c Hcts0). }
    have Hfitsg : ∀ c, c ∈ all_cells typesj ->
        (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z.
    { move=> c Hc. have Hu := Hcellunit c Hc. rewrite /cell_unit in Hu.
      rewrite Hu. have := Hnowrapj c Hc. lia. }
    have Hrunleng : ∀ c, c ∈ all_cells typesj -> (1 < length (ic_run c))%nat ->
        (Z.of_nat (length (client_run typesj (cell_client c))) + 2 < 2^63)%Z.
    { move=> c Hc Hgt. have Hu := Hcellunit c Hc. rewrite /cell_unit in Hu. lia. }
    have HwLc : ((match in_originId input, ocL with
      | Some oid, Some c => c ∈ all_cells typesj ∧
          clientId (item_id (run_head c)) = clientId oid ∧
          (clock (item_id (run_head c)) <= clock oid)%nat ∧
          (clock oid < clock (item_id (run_head c)) + length (ic_run c))%nat
      | None, None => True | _, _ => False end : Prop)).
    { move: HwL. destruct (in_originId input); destruct ocL as [c0|]; try done.
      move=> [Hmem Hid0]. have Hu := Hcellunit c0 Hmem. rewrite /cell_unit in Hu.
      split_and!; [exact Hmem | rewrite Hid0 // | rewrite Hid0; lia | rewrite Hid0 Hu; lia]. }
    have HwRc : ((match in_rightOriginId input, ocR with
      | Some oid, Some c => c ∈ all_cells typesj ∧
          clientId (item_id (run_head c)) = clientId oid ∧
          (clock (item_id (run_head c)) <= clock oid)%nat ∧
          (clock oid < clock (item_id (run_head c)) + length (ic_run c))%nat
      | None, None => True | _, _ => False end : Prop)).
    { move: HwR. destruct (in_rightOriginId input); destruct ocR as [c0|]; try done.
      move=> [Hmem Hid0]. have Hu := Hcellunit c0 Hmem. rewrite /cell_unit in Hu.
      split_and!; [exact Hmem | rewrite Hid0 // | rewrite Hid0; lia | rewrite Hid0 Hu; lia]. }
    have Huniqj := yai_unique _ Hinvj.
    have HfLpj : findPtrIdx (origin nit) arrj = Some leftIdx.
    { rewrite -(toitem_lemmas.findLeftIdx_findPtrIdx_eq input nit arrj Huniqj Htoit). exact HfindL. }
    have HfRpj : findPtrIdx (rightOrigin nit) arrj = Some rightIdx.
    { rewrite -(toitem_lemmas.findRightIdx_findPtrIdx_eq input nit arrj Huniqj Htoit). exact HfindR. }
    have HorigAj := findptridx_getelem.findPtrIdx_ArrSet arrj (origin nit) leftIdx HfLpj.
    have HrorAj := findptridx_getelem.findPtrIdx_ArrSet arrj (rightOrigin nit) rightIdx HfRpj.
    have Hlrj := findptridx_order2.YjsLt'_findPtrIdx_lt arrj (origin nit) (rightOrigin nit)
                  leftIdx rightIdx Hinvj HorigAj HrorAj (iiv_origin_lt _ Hvld) HfLpj HfRpj.
    have Hsameg : ((match in_originId input, in_rightOriginId input, ocL, ocR with
      | Some a, Some b, Some cL0, Some cR0 => cL0 = cR0 -> (clock a < clock b)%nat
      | _, _, _, _ => True end : Prop)).
    { move: HwL HwR HfindL HfindR.
      destruct (in_originId input) as [oidL|] eqn:HoinL2; try done.
      destruct (in_rightOriginId input) as [oidR|] eqn:HoinR2; try done.
      destruct ocL as [cL0|]; try done. destruct ocR as [cR0|]; try done.
      move=> [_ HidL0] [_ HidR0] HfindL2 HfindR2 Heq. exfalso.
      have Hoideq : oidL = oidR by rewrite -HidL0 -HidR0 Heq //.
      destruct (findLeftIdx_inv oidL arrj leftIdx HfindL2) as (knL & itL & HeqL & HknL & HidL2).
      destruct (findRightIdx_inv oidR arrj rightIdx HfindR2) as (knR & itR & HeqR & HknR & HidR2).
      have Hiteq : item_id itL = item_id itR by rewrite HidL2 HidR2 Hoideq //.
      have Hkeq : knL = knR.
      { destruct (Nat.lt_trichotomy knL knR) as [Hlt2 | [Heq2 | Hgt2]]; [| exact Heq2 |].
        - exact (False_ind _ (uniqueId_lookup_ne arrj knL knR itL itR Huniqj HknL HknR Hlt2 Hiteq)).
        - exact (False_ind _ (uniqueId_lookup_ne arrj knR knL itR itL Huniqj HknR HknL Hgt2 (eq_sym Hiteq))). }
      subst knR. lia. }
    iAssert (([∗ map] p0 ↦ ts0 ∈ typesj,
        own_ytype_cells p0 (DfracOwn 1) (ty_cells ts0) (ty_arr ts0) ∗
        ⌜YjsArrInvariant (ty_arr ts0)⌝))%I with "[Htypes]" as "Htypes".
    { iApply (big_sepM_impl with "Htypes").
      iIntros "!#" (p0 ts0 Hp0) "($ & $ & _)". }
    wp_apply (wp_store__repair_split s mref tref itv (uiv.(yjs.updateItem.parentName'))
                input opn typesj bind ocL ocR pj
                HwLc HwRc Hsameg Hwpar Hfitsg Hlocdupj Hrangedisjj Horiginclkj Hrunleng
                with "[$Hfresh $HisPN $Hitemsf $Hitemmap $Htypesf $Htypesmap $Htypes]").
    iIntros (lft rgt types2) "(Hlinked & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes & %Hpinv2 & %Hrtf & %HbdL & %HbdR)".
    (* under the unit scaffold no split fires: the map is unchanged *)
    have Htyeq : types2 = typesj.
    { destruct Hrtf as (Hpres & Hdom2m & _ & Hunitpres).
      apply map_eq => p0.
      destruct (typesj !! p0) as [ts0|] eqn:Hp0.
      - destruct (Hdom2m p0 (mk_is_Some _ _ Hp0)) as [ts2 Hp2].
        rewrite Hp2.
        f_equal. exact (Hunitpres p0 ts0 ts2 Hp0 Hp2 (Hunitall0 p0 ts0 Hp0)).
      - destruct (types2 !! p0) as [ts2|] eqn:Hp2; [| done].
        destruct (Hpres p0 ts2 Hp2) as (ts0 & Hp0' & _). congruence. }
    subst types2.
    iAssert (([∗ map] p0 ↦ ts0 ∈ typesj,
        own_ytype_cells p0 (DfracOwn 1) (ty_cells ts0) (ty_arr ts0) ∗
        ⌜YjsArrInvariant (ty_arr ts0)⌝ ∗
        ⌜Forall cell_unit (ty_cells ts0)⌝))%I with "[Htypes]" as "Htypes".
    { iApply (big_sepM_impl with "Htypes").
      iIntros "!#" (p0 ts0 Hp0) "($ & $)". iPureIntro. exact (Hunitall0 p0 ts0 Hp0). }
    (* the boundary locations collapse to the witness locations *)
    have HlftEq : lft = (match ocL with Some c => ic_loc c | None => null end).
    { move: HbdL. destruct (in_originId input); destruct ocL as [c0|]; try done.
      by move=> [-> _]. }
    have HrgtEq : rgt = (match ocR with Some c => ic_loc c | None => null end).
    { move: HbdR HwR. destruct (in_rightOriginId input) as [oidR|]; destruct ocR as [c0|]; try done.
      move=> [cR' [HcR'mem [HcR'loc [HcR'cl [HcR'clk _]]]]] [Hmem0 Hid0].
      have Hu' := Hcellunit cR' HcR'mem.
      have Hu0 := Hcellunit c0 Hmem0.
      rewrite /cell_unit in Hu' Hu0.
      have Hb0 := proj2 (Hbnds0 c0 Hmem0).
      rewrite Hid0 in Hb0.
      have Hc0cl : cell_client c0 = W64 (clientId oidR) by rewrite /cell_client Hid0 //.
      have Hc0clk : (uint.Z (cell_clock c0) = Z.of_nat (clock oidR))%Z.
      { rewrite /cell_clock Hid0. word. }
      destruct (decide (ic_loc cR' = ic_loc c0)) as [He | Hne].
      - rewrite -HcR'loc He //.
      - exfalso.
        destruct (Hrangedisjj cR' c0 HcR'mem Hmem0
                    ltac:(rewrite HcR'cl Hc0cl //) Hne) as [Hd | Hd].
        + rewrite Hu' /= in Hd. lia.
        + rewrite Hu0 /= in Hd. lia. }
    iEval (rewrite HlftEq HrgtEq HlocLeq HlocReq) in "Hlinked".
    iDestruct (linked_item_fresh with "Hlinked Htypes") as %Hfreshloc.
    iDestruct (types_unit_all with "Htypes") as %Hunitallj.
    iDestruct (types_repr_all with "Htypes") as %Hreprallj.
    iDestruct (types_cells_id_bounds with "Htypes") as %Hcellbndj.
    wp_auto.
    have Hidnit : item_id nit = in_id input := commutativity.toItem_id input arrj nit Htoit.
    have Hgmaxj : ∀ c0, c0 ∈ all_cells typesj → cell_client c0 = W64 (clientId (item_id nit)) →
                    (uint.Z (cell_clock c0) < uint.Z (W64 (clock (item_id nit))))%Z.
    { intros c0 Hc0 Hcc0. rewrite Hidnit in Hcc0 |- *.
      exact (Hbndj c0 Hc0 j (RootId nmj, input) ltac:(lia) Hinput Hcc0). }
    iDestruct (big_sepM_delete _ _ pj _ Htsj with "Htypes") as "[[Hyt _] Htypesrest]".
    have Hfitscj : ∀ c0, c0 ∈ cellsj -> cell_fits c0.
    { move=> c0 Hc0.
      have Hmem : c0 ∈ all_cells typesj.
      { rewrite (all_cells_lookup _ _ _ Htsj). apply elem_of_app. left. exact Hc0. }
      have Hu : cell_unit c0 := proj1 (Forall_forall _ _) Hunitcj c0 Hc0.
      have Hnw := Hnowrapj c0 Hmem.
      rewrite /cell_fits. rewrite /cell_unit in Hu. rewrite Hu. lia. }
    have Hoclkcj : ∀ c0, c0 ∈ cellsj -> cell_origin_clk c0.
    { move=> c0 Hc0. apply Horiginclkj.
      rewrite (all_cells_lookup _ _ _ Htsj). apply elem_of_app. by left. }
    (* place the boundary cursors for the C1e Integrate spec: under the unit
       scaffold every model index is a run boundary, so [Z.to_nat] of the
       resolved neighbour indices works *)
    have Huniq2 := yai_unique _ Hinvj.
    have HfLp2 : findPtrIdx (origin nit) arrj = Some leftIdx.
    { rewrite -(toitem_lemmas.findLeftIdx_findPtrIdx_eq input nit arrj Huniq2 Htoit). exact HfindL. }
    have HfRp2 : findPtrIdx (rightOrigin nit) arrj = Some rightIdx.
    { rewrite -(toitem_lemmas.findRightIdx_findPtrIdx_eq input nit arrj Huniq2 Htoit). exact HfindR. }
    have HlB2 := insert_lemmas.findPtrIdx_ge_minus_1 arrj (origin nit) leftIdx HfLp2.
    have HorigA2 := findptridx_getelem.findPtrIdx_ArrSet arrj (origin nit) leftIdx HfLp2.
    have HrorA2 := findptridx_getelem.findPtrIdx_ArrSet arrj (rightOrigin nit) rightIdx HfRp2.
    have Hlr2 := findptridx_order2.YjsLt'_findPtrIdx_lt arrj (origin nit) (rightOrigin nit)
                  leftIdx rightIdx Hinvj HorigA2 HrorA2 (iiv_origin_lt _ Hvld) HfLp2 HfRp2.
    have HrUB2 := insert_lemmas.findPtrIdx_le_size arrj (rightOrigin nit) rightIdx HfRp2.
    have Hreprj2 : cells_repr arrj cellsj arrj := Hreprallj pj _ Htsj.
    have Hnecj2 := Forall_cell_unit_nonempty cellsj Hunitcj.
    have Hcelllen2 : length cellsj = length arrj := cells_repr_length _ _ _ Hunitcj Hreprj2.
    set curL2 := Z.to_nat (leftIdx + 1).
    set curR2 := Z.to_nat rightIdx.
    have HcurL2b : (curL2 <= length cellsj)%nat by rewrite /curL2 Hcelllen2; lia.
    have HcurR2b : (curR2 <= length cellsj)%nat by rewrite /curR2 Hcelllen2; lia.
    have HcurL2 : (Z.of_nat (length (run_flatten (take curL2 cellsj))) = leftIdx + 1)%Z.
    { rewrite (run_flatten_take_length_unit cellsj curL2 Hunitcj) (Nat.min_l _ _ HcurL2b) /curL2 Z2Nat.id; lia. }
    have HcurR2 : (Z.of_nat (length (run_flatten (take curR2 cellsj))) = rightIdx)%Z.
    { rewrite (run_flatten_take_length_unit cellsj curR2 Hunitcj) (Nat.min_l _ _ HcurR2b) /curR2 Z2Nat.id; lia. }
    have HnlL2 : node_loc cellsj leftIdx = node_loc cellsj (Z.of_nat curL2 - 1).
    { f_equal. rewrite /curL2 Z2Nat.id; lia. }
    have HnlR2 : node_loc cellsj rightIdx = node_loc cellsj (Z.of_nat curR2).
    { f_equal. rewrite /curR2 Z2Nat.id; lia. }
    iEval (rewrite HnlL2 HnlR2) in "Hlinked".
    wp_apply (wp_Store__Integrate_nil s pj itv arrj input nit cellsj typesj mref leftIdx rightIdx
                curL2 curR2
                Hinvj Htoit Hvld Hmaxj HfindL HfindR Htsj Hgmaxj Hnecj2 Hfitscj Hoclkcj
                HcurL2 HcurL2b HcurR2 HcurR2b
                with "[$Hyt $Hlinked $Hitemsf $Hitemmap]").
    iIntros (arr2' idx2 iidx2 cells'' c2)
      "(%Hile2 & %Harr2eq & %Hinv2 & Htext2 & Hitemsf & Hitemmap & %Hperm2 & %Hsi2 & %Hsplice2 & %Hidx2b & %Hcoup2 & %Harrsp2 & %Hc2look & %Hc2loc & %Hc2id & %Hc2del & %Hc2unit)".
    rewrite Hsi2 in Hsi. injection Hsi as Harr22. subst arr2'.
    have Hunitcells'' : Forall cell_unit cells''
      by (rewrite Hsplice2; exact (Forall_cell_unit_splice cellsj idx2 c2 Hunitcj Hc2unit)).
    (* the pool grows by exactly [c2] *)
    have Hac_step : all_cells (<[pj := MkTypeState cells'' arr2]> typesj)
                  ≡ₚ all_cells typesj ++ [c2]
      by apply (all_cells_insert_snoc typesj pj cellsj arrj cells'' arr2 c2 Htsj Hperm2).
    have Hcc2 : cell_client c2 = W64 (clientId (in_id input))
      by rewrite /cell_client Hc2id Hidnit //.
    have Hclk2 : cell_clock c2 = W64 (clock (in_id input))
      by rewrite /cell_clock Hc2id Hidnit //.
    have Hlocdup' : NoDup (ic_loc <$> all_cells (<[pj := MkTypeState cells'' arr2]> typesj)).
    { apply (nodup_locs_snoc (all_cells typesj) _ c2 Hac_step);
        [rewrite Hc2loc; exact Hfreshloc | exact Hlocdupj]. }
    have Hrangedisj' : cells_range_disjoint (all_cells (<[pj := MkTypeState cells'' arr2]> typesj)).
    { apply (rangedisj_snoc (all_cells typesj) _ c2 Hac_step); [| exact Hrangedisjj].
      move=> c0 Hc0 Hcc0.
      have Hc0m := Hc0. apply all_cells_elem_of in Hc0m.
      destruct Hc0m as (p0 & ts0 & Hp0 & Hcts0).
      have Hunit0 : cell_unit c0 := proj1 (Forall_forall _ _) (Hunitallj p0 ts0 Hp0) c0 Hcts0.
      rewrite /cell_unit in Hunit0.
      have Hccnit : cell_client c0 = W64 (clientId (item_id nit)).
      { rewrite Hcc0 Hcc2 Hidnit //. }
      have Hlt := Hgmaxj c0 Hc0 Hccnit.
      rewrite Hidnit in Hlt.
      rewrite Hclk2 Hunit0. clear -Hlt. lia. }
    (* origin-clock for the grown pool: the new cell's head is [nit], whose
       resolved same-client origin is an existing doc item strictly below the
       batch id's clock (per-client causal freshness, Hbndj) *)
    have Horiginclk' : ∀ c0, c0 ∈ all_cells (<[pj := MkTypeState cells'' arr2]> typesj) ->
        cell_origin_clk c0.
    { apply (originclk_snoc (all_cells typesj) _ c2 Hac_step); [| exact Horiginclkj].
      move=> oid Hoid Hcl.
      rewrite Hc2id in Hoid Hcl.
      rewrite Hc2id.
      rewrite (in_originId_origin_id arrj nit input Htoit) in Hoid.
      have [o0 [r0 [id0 [c0x [Hnitdef [HoLp [_ [_ _]]]]]]]]
        := proj1 (toItem_ok_iff input arrj nit) Htoit.
      rewrite Hoid /isLeftIdPtr in HoLp.
      destruct HoLp as (x & Ho & Hfind).
      have Hxid : item_id x = oid by apply (find_by_id_id oid arrj x Hfind).
      have Hxmem : x ∈ arrj by apply (find_by_id_mem oid arrj x Hfind).
      (* the origin item is a run head of a cell of this type *)
      have Hrepr_pj : cells_repr arrj cellsj arrj := Hreprallj pj _ Htsj.
      have Hunit_pj : Forall cell_unit cellsj := Hunitallj pj _ Htsj.
      have Hxcell := unit_cells_arr_head cellsj arrj x Hrepr_pj Hunit_pj Hxmem.
      destruct Hxcell as (c0' & Hc0'mem & Hxhead).
      have Hc0'all : c0' ∈ all_cells typesj.
      { rewrite (all_cells_lookup _ _ _ Htsj). apply elem_of_app. by left. }
      have Hcl' : cell_client c0' = W64 (clientId (in_id input)).
      { rewrite /cell_client -Hxhead Hxid Hcl Hidnit //. }
      have Hbnd := Hbndj c0' Hc0'all j (RootId nmj, input) ltac:(lia) Hinput Hcl'.
      have Hck' : cell_clock c0' = W64 (clock oid).
      { rewrite /cell_clock -Hxhead Hxid //. }
      have [_ Hkb] := Hcellbndj c0' Hc0'all.
      have Hnwb := Hnowrapb j (RootId nmj, input) Hinput. simpl in Hnwb.
      rewrite Hck' in Hbnd.
      rewrite Hidnit.
      have Hkb' : (Z.of_nat (clock oid) < 2^64)%Z by rewrite -Hxid Hxhead; exact Hkb.
      have Ha : uint.Z (W64 (clock oid)) = Z.of_nat (clock oid).
      { clear -Hkb'. word. }
      have Hb : uint.Z (W64 (clock (in_id input))) = Z.of_nat (clock (in_id input)).
      { clear -Hnwb. word. }
      rewrite Ha Hb in Hbnd. lia. }
    (* rebuild the per-type big-sep over the grown map *)
    iAssert ([∗ map] p ↦ ts ∈ <[pj := MkTypeState cells'' arr2]> typesj,
        own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
        ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
        ⌜Forall cell_unit (ty_cells ts)⌝)%I
      with "[Htext2 Htypesrest]" as "Htypes".
    { rewrite -insert_delete_eq.
      rewrite big_sepM_insert; last apply lookup_delete_eq.
      iFrame "Htypesrest". simpl. rewrite Harr22. iFrame "Htext2".
      iPureIntro. split; [rewrite -Harr22; exact Hinv2 | exact Hunitcells'']. }
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
    + exact Hlocdup'.
    + exact Hrangedisj'.
    + exact Horiginclk'.
  - (* loop exit: the whole batch is integrated, [mj = m'] *)
    have Hjeq : (j = length uivs)%nat by word.
    rewrite Hjeq Hlen_ui drop_all in Hreplayj.
    inversion Hreplayj; subst.
    wp_auto.
    iApply ("HΦ" $! typesj).
    iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
    iSplitL "Hsl Hcap".
    { iExists uivs. iFrame "Hsl Hcap Hitems". }
    iPureIntro. split_and!; [exact Hdomj | exact Hmtypesj | exact Hprovj | exact Hlocdupj | exact Hrangedisjj | exact Horiginclkj].
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
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  (∀ c, c ∈ all_cells types -> cell_origin_clk c) ->
  {{{ is_pkg_init yjs ∗ is_history (A := A) (P := P) γh ∗
      own_client_history γh c h ∗
      ([∗ list] ti;D ∈ inputs;Ds, is_op_cert γh (ti.1, OpInsert ti.2) D) ∗
      own_update sl dq inputs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "applyUpdate" #sl
  {{{ (types' : gmap loc type_state) (m' : DocM), RET #();
      own_update sl dq inputs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
          ⌜Forall cell_unit (ty_cells ts)⌝) ∗
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
            cell_clock c0 = W64 (clock (in_id ti.2))⌝ ∗
      ⌜NoDup (ic_loc <$> all_cells types')⌝ ∗
      ⌜cells_range_disjoint (all_cells types')⌝ ∗
      ⌜∀ c, c ∈ all_cells types' -> cell_origin_clk c⌝ }}}.
Proof using Type*.
  move=> Hbatch Hcoh Hcohreg Hbatchbnd Hnowrap Hnowrapb Hlocdup0 Hrangedisj0 Horiginclk0.
  destruct Hcohreg as (Hbindtypes & Hbindinj & Htypesbound & Hmtypes & Hmdom).
  iIntros (Φ) "(#Hpkg & #Hhist & Hown & #Hcerts & Hupd & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes) HΦ".
  iDestruct (types_arr_inv with "Htypes") as %Htsinv.
  iDestruct (types_repr_all with "Htypes") as %Hreprall.
    iDestruct (types_unit_all with "Htypes") as %Hunitall.
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
    have Hitemmem : run_head c0 ∈ ty_arr ts.
    { rewrite (Hreprall p ts Hts).
        apply run_head_in_flatten; [exact Hcts |].
        exact (proj1 (Forall_forall _ _) (Hunitall p ts Hts) _ Hcts). }
    destruct (Htypesbound p (ex_intro _ ts Hts)) as [nm Hbnm].
    have Hdg : docm_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
    have Hmem : run_head c0 ∈ docm_get m (RootId nm) by rewrite Hdg.
    have [Hcb Hkb] := Hcellbnd c0 Hc0.
    have [Hicb Hikb] := Hidbnd i ti Hi.
    have Hceq : clientId (item_id (run_head c0)) = clientId (in_id ti.2).
    { move: Hcc. rewrite /cell_client. move=> Hcc.
      have Hz : uint.Z (W64 (clientId (item_id (run_head c0))))
              = uint.Z (W64 (clientId (in_id ti.2))) by rewrite Hcc.
      word. }
    have Hlt := ValidReplay_arr_fresh inputs m m' Hvr i ti Hi (RootId nm) (run_head c0) Hmem Hceq.
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
              Hlocdup0 Hrangedisj0 Horiginclk0
              with "[$Hupd $Hitemsf $Hitemmap $Htypesf $Htypesmap $Htypes]").
  iIntros (types') "(Hupd & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes & %Hdom' & %Hmtypes' & %Hprov' & %Hlocdup' & %Hrangedisj' & %Horiginclk')".
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
  - exact Hlocdup'.
  - exact Hrangedisj'.
  - exact Horiginclk'.
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
    iDestruct (types_unit_all with "Htypes") as %Hunitall.
  iDestruct (types_cells_id_bounds with "Htypes") as %Hcellbnd.
  have Hregcohd := Hregcoh.
  destruct Hregcohd as (Hbindtypes & Hbindinj & Htypesbound & Hmtypes & Hmdom).
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
  (* run the internal certificate lemma; keep a fupd after the call for the
     item-set authority update *)
  iApply wp_fupd.
  wp_apply (wp_store__applyUpdate_certs_aux s sl dq γh c h inputs Ds m types bind
              items_mref types_mref Hbatch Hhcoh Hregcoh Hbatchbnd Hnowrap Hnowrapb
              Hlocdup Hrangedisj Horiginclk
              with "[$Hpkg $Hishist $Hhist $Hcerts $Hupd $Hitemsf $Hitemmap $Htypesf $Htypesmap $Htypes]").
  iIntros (types' m') "(Hupd & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes & Hhist & #Hlbnew & %Hcoh' & %Hregcoh' & %Hdom' & %Hvr & %Hnoc & %Hprov' & %Hlocdup' & %Hrangedisj' & %Horiginclk')".
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
  (* the run-fits pool invariant survives: old cells keep their value, batch
     cells are singleton runs at a batch id whose clock has the no-wrap bound *)
  iDestruct (types_unit_all with "Htypes") as %Hunitall'.
  have Hrunfits' : ∀ c0, c0 ∈ all_cells types' -> cell_fits c0.
  { move=> c0 Hc0.
    destruct (Hprov' c0 Hc0) as [Hold | (i & ti & Hi & Hcc & Hck)].
    - exact (Hrunfits c0 Hold).
    - have Hc0m := Hc0. apply all_cells_elem_of in Hc0m.
      destruct Hc0m as (p & ts & Hts & Hcts).
      have Hu : cell_unit c0 := proj1 (Forall_forall _ _) (Hunitall' p ts Hts) _ Hcts.
      rewrite /cell_unit in Hu.
      rewrite /cell_fits Hck Hu.
      have := Hnowrapb i ti Hi. word. }
  iModIntro. iApply ("HΦ" $! m').
  iFrame "Hupd". iFrame "Hlbnew". iFrame "Hlbs".
  iSplitL "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hseq Htypes HtypesAuth Hhist";
    last by iPureIntro.
  iExists client, k, items_mref, types_mref, dset, types', bind.
  iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hseq Htypes HtypesAuth Hbinds Hhist".
  iPureIntro. split_and!;
    [exact Hclientc | exact Hregcoh' | exact Hcoh' | exact Hctr'
    | exact Hlocdup' | exact Hrangedisj' | exact Hrunfits' | exact Horiginclk'].
Qed.

End store_update.
