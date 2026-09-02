(** The [yType] container, PURE model layer: the document SEQUENCE a [yType]
    denotes, and the theory of inserting into it. No Go values, no Iris.

    It defines nothing: the sequence and its invariant ([YjsArrInvariant],
    [IsItemValid]) are rocq-yjs's. What lives here is the theory the insert
    paths need.

    Laws
    - validity at a straddle point: an item whose origins are the neighbours at
      position [p] is valid, in each of the four boundary cases and in the
      unified form ([item_valid_empty] / [_head] / [_tail] / [_adjacent],
      [item_valid_at]).
    - [insert_item_valid] repackages that over the exact origin facts
      [yType.findPos] yields (a neighbour by id, or the [First] / [Last]
      boundary), so a WP proof discharges [IsItemValid] in one application.
    - [insert_maximalId]: inserting a fresh item keeps the per-client clock
      bound.
    - [integrate_ready]: the premises of an integrate, as one predicate.
    - [sorted_subseteq_sublist]: set inclusion between two sorted document
      lists is a [sublist].

    Second section ([ytype_run_model], plan-item-run-split stage 2):
    [type_model], the type at run granularity: its runs as data ([tm_runs])
    and the per-char document list they flatten to ([tm_arr]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
From stdpp Require Import sorting.
From New.proof.item Require Import run_theory model value heap.

Section ytype_model.

Set Default Proof Using "Type*".

Notation A := go_string.

(** Public top-level spec — [Store.Integrate] inserts the item and preserves the
    document invariant. The result [arr'] is the model document with [newItem]
    spliced in at *some* in-bounds position [i] (the position is existential, so
    the conflict-resolution algorithm is not exposed — only the abstract effect
    "the item was inserted somewhere, and the document stays valid"). The
    document invariant [is_valid_ytype] already carries [YjsArrInvariant], so it
    pins [arr'] uniquely given the item set; the caller's item is encapsulated in
    [own_fresh_item]; the document/input side conditions are the only premises.
    Proven from [wp_Store__Integrate_aux]: integration succeeds ([integrate_some]),
    bridges to [setintegrate] ([setintegrate_eq_integrate]); the insertion
    position and the post-state's validity come from the rocq-yjs preservation
    theorem [YjsArrInvariant_integrate]. *)

(** [integrate_ready arr input newItem]: the wire item [input] resolves in
    the document [arr] to the valid, clock-maximal item [newItem]: with
    [YjsArrInvariant arr] (a fact about the document alone, carried by the
    type pool), exactly the premises under which rocq-yjs's set integrate and
    scanning integrate agree ([setintegrate_eq_integrate]). What every
    Integrate spec asks of its input. *)
Definition integrate_ready (arr : list (YjsItem A)) (input : IntegrateInput (A := A))
    (newItem : YjsItem A) : Prop :=
  toItem input arr = Some newItem ∧ IsItemValid newItem ∧ maximalId newItem arr.

(** [item_valid_adjacent]: the pure (model-level) heart of the Text.Insert proof.
    An item whose origin / right-origin are two *adjacent* elements of a valid
    document array is [IsItemValid]. [iiv_origin_lt] is immediate from the array
    being sorted ([yai_sorted]); [iiv_reachable] follows from
    [origins_adjacent_in_reachable] plus the fact that nothing in a sorted array lies
    strictly between adjacent elements (the index lemmas). This isolates the only
    hard obligation of an insert into the order theory, so the WP side only has
    to maintain that the chosen left/right neighbours are adjacent. *)
(** [inserted_run L L' ins cs client k0 originLeft originRight]: what one
    [Text.Insert] of the bytes [cs] did to the list: it grew from [L] to [L']
    (a sublist), and [ins] lists the new items, one per byte unless nothing was
    inserted: the [i]-th carries byte [cs !! i], id [(client, k0 + i)] and right
    origin [originRight]; its left origin is [originLeft] for the first item and
    the previous new item for the others (the chain of one insert). *)
Definition inserted_run (L L' ins : list (YjsItem A)) (cs : A) (client k0 : nat)
    (originLeft originRight : YjsPtr A) : Prop :=
  sublist L L' ∧
  (ins = [] ∨ length ins = length cs) ∧
  (∀ (i : nat) (it : YjsItem A) (b : w8),
     ins !! i = Some it → cs !! i = Some b →
       it ∈ L' ∧ it ∉ L ∧
       content it = [b] ∧
       item_id it = MkYjsId client (k0 + i)%nat ∧
       rightOrigin it = originRight ∧
       (i = 0%nat → origin it = originLeft) ∧
       (∀ (j : nat) (itj : YjsItem A),
          i = S j → ins !! j = Some itj → origin it = itemPtr itj)).

(** A ready item's same-client origin is older than it: the origin resolves
    to a document item ([toItem]) and the item is its client's newest
    ([maximalId]). What [cell_origin_clk] asks of the cell it lands in. *)
Lemma integrate_ready_origin_clk (arr : list (YjsItem A)) (input : IntegrateInput (A := A))
    (newItem : YjsItem A) :
  integrate_ready arr input newItem ->
  ∀ originId, origin_id (origin newItem) = Some originId ->
    clientId originId = clientId (item_id newItem) ->
    (clock originId < clock (item_id newItem))%nat.
Proof.
  move=> [Htoit [_ Hmax]] originId Hoid Hcl.
  rewrite (insert_set.in_originId_origin_id arr newItem input Htoit) in Hoid.
  have [o [r [id [c [Hdef [HoL _]]]]]] := proj1 (toitem_lemmas.toItem_ok_iff input arr newItem) Htoit.
  rewrite Hoid /toitem_lemmas.isLeftIdPtr in HoL.
  destruct HoL as (x & Ho & Hfind).
  have Hxid : item_id x = originId by apply (toitem_lemmas.find_by_id_id originId arr x Hfind).
  have Hxmem : x ∈ arr by apply (toitem_lemmas.find_by_id_mem originId arr x Hfind).
  have Hlt := Hmax x Hxmem. rewrite Hxid in Hlt. exact (Hlt Hcl).
Qed.

Lemma item_valid_adjacent (arr : list (YjsItem A)) (i : nat) (a b : YjsItem A)
    (newid : YjsId) (c : A) :
  YjsArrInvariant arr ->
  base.lookup i arr = Some a ->
  base.lookup (S i) arr = Some b ->
  IsItemValid (Item (itemPtr a) (itemPtr b) newid c).
Proof.
  intros Hinv Ha Hb.
  destruct a as [oa ra ida ca]. destruct b as [ob rb idb cb].
  pose proof (yai_item_set_inv _ Hinv) as Hisi.
  pose proof (yai_closed _ Hinv) as Hclosed.
  assert (HaIn : ArrSet arr (Item oa ra ida ca)) by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Ha).
  assert (HbIn : ArrSet arr (Item ob rb idb cb)) by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hb).
  assert (Hab : YjsLt' (Item oa ra ida ca) (Item ob rb idb cb))
    by exact (invariant_yjsarray_idx.getElem_lt_YjsLt' arr i (S i) _ _ Hinv Ha Hb ltac:(lia)).
  assert (Hlo : forall p, ArrSet arr p -> YjsLt' p (Item ob rb idb cb) -> YjsLeq' p (Item oa ra ida ca)).
  { intros p Hp Hpb. destruct p as [q | | ].
    - destruct (list_basics.list.list_elem_of_lookup_1 _ _ Hp) as [iq Hiq].
      assert (iq < S i)%nat by exact (findptridx_order2.getElem_YjsLt'_index_lt arr iq (S i) q (Item ob rb idb cb) Hinv Hiq Hb Hpb).
      apply (invariant_yjsarray_idx.getElem_leq_YjsLeq' arr iq i q (Item oa ra ida ca) Hinv Hiq Ha). lia.
    - exact (YjsLeq'_leqLt _ _ (YjsLt'_ltOriginOrder _ _ (lt_first (Item oa ra ida ca)))).
    - exfalso. destruct Hpb as [h Hh]. exact (not_last_lt_ptr Hclosed Hisi h _ HbIn Hh). }
  assert (Hhi : forall p, ArrSet arr p -> YjsLt' (Item oa ra ida ca) p -> YjsLeq' (Item ob rb idb cb) p).
  { intros p Hp Hap. destruct p as [q | | ].
    - destruct (list_basics.list.list_elem_of_lookup_1 _ _ Hp) as [iq Hiq].
      assert (i < iq)%nat by exact (findptridx_order2.getElem_YjsLt'_index_lt arr i iq (Item oa ra ida ca) q Hinv Ha Hiq Hap).
      apply (invariant_yjsarray_idx.getElem_leq_YjsLeq' arr (S i) iq (Item ob rb idb cb) q Hinv Hb Hiq). lia.
    - exfalso. exact (not_ptr_lt'_first Hclosed Hisi _ HaIn Hap).
    - exact (YjsLeq'_leqLt _ _ (YjsLt'_ltOriginOrder _ _ (lt_last (Item ob rb idb cb)))). }
  assert (HF1 : YjsLeq' (Item ob rb idb cb) ra)
    by exact (Hhi ra (closedRight _ Hclosed oa ra ida ca HaIn) (item_lt_rightOrigin (Item oa ra ida ca))).
  assert (HF2 : YjsLeq' ob (Item oa ra ida ca))
    by exact (Hlo ob (closedLeft _ Hclosed ob rb idb cb HbIn) (item_origin_lt (Item ob rb idb cb))).
  apply Build_IsItemValid.
  - exact Hab.
  - intros x Hreach.
    inversion Hreach as [p1 q1 Hstep | p1 q1 r1 Hstep Hrest]; subst.
    + inversion Hstep; subst; [ left | right ]; apply YjsLeq'_leqSame.
    + inversion Hstep; subst.
      * pose proof (reachable_in arr (Item oa ra ida ca) Hclosed x Hrest HaIn) as HxIn.
        pose proof (origins_adjacent_in_reachable (ArrSet arr) Hisi oa ra ca ida x HaIn Hrest) as [Hxoa | Hrax].
        -- left. apply YjsLeq'_leqLt.
           exact (transitivity.yjs_leq'_p_trans1 Hisi x oa (Item oa ra ida ca) HxIn (closedLeft _ Hclosed oa ra ida ca HaIn) HaIn Hclosed Hxoa (item_origin_lt (Item oa ra ida ca))).
        -- right.
           exact (transitivity.yjs_leq'_p_trans Hisi (Item ob rb idb cb) ra x HbIn (closedRight _ Hclosed oa ra ida ca HaIn) HxIn Hclosed HF1 Hrax).
      * pose proof (reachable_in arr (Item ob rb idb cb) Hclosed x Hrest HbIn) as HxIn.
        pose proof (origins_adjacent_in_reachable (ArrSet arr) Hisi ob rb cb idb x HbIn Hrest) as [Hxob | Hrbx].
        -- left.
           exact (transitivity.yjs_leq'_p_trans Hisi x ob (Item oa ra ida ca) HxIn (closedLeft _ Hclosed ob rb idb cb HbIn) HaIn Hclosed Hxob HF2).
        -- right.
           exact (transitivity.yjs_leq'_p_trans Hisi (Item ob rb idb cb) rb x HbIn (closedRight _ Hclosed ob rb idb cb HbIn) HxIn Hclosed (YjsLeq'_leqLt _ _ (item_lt_rightOrigin (Item ob rb idb cb))) Hrbx).
Qed.

(** Boundary variants of [item_valid_adjacent] for the ends of the document:
    inserting before the head ([First] origin), after the tail ([Last]
    right-origin), or into an empty document ([First]/[Last]). *)
Lemma item_valid_empty (newid : YjsId) (c : A) : IsItemValid (Item First Last newid c).
Proof.
  apply Build_IsItemValid.
  - exact (YjsLt'_ltOriginOrder _ _ lt_first_last).
  - intros x Hreach.
    inversion Hreach as [p1 q1 Hstep | p1 q1 r1 Hstep Hrest]; subst.
    + inversion Hstep; subst; [left|right]; apply YjsLeq'_leqSame.
    + exfalso. inversion Hstep; subst; inversion Hrest as [u v Hs | u v w Hs Hr]; inversion Hs.
Qed.

Lemma item_valid_head (arr : list (YjsItem A)) (b : YjsItem A) (newid : YjsId) (c : A) :
  YjsArrInvariant arr -> base.lookup 0%nat arr = Some b ->
  IsItemValid (Item First (itemPtr b) newid c).
Proof.
  intros Hinv Hb. destruct b as [ob rb idb cb].
  pose proof (yai_item_set_inv _ Hinv) as Hisi.
  pose proof (yai_closed _ Hinv) as Hclosed.
  assert (HbIn : ArrSet arr (Item ob rb idb cb)) by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hb).
  assert (Hob : ob = First).
  { pose proof (closedLeft _ Hclosed ob rb idb cb HbIn) as Hobin.
    pose proof (item_origin_lt (Item ob rb idb cb)) as Hoblt.
    destruct ob as [q | | ].
    - exfalso. destruct (list_basics.list.list_elem_of_lookup_1 _ _ Hobin) as [iq Hiq].
      assert (iq < 0)%nat by exact (findptridx_order2.getElem_YjsLt'_index_lt arr iq 0 q (Item (itemPtr q) rb idb cb) Hinv Hiq Hb Hoblt). lia.
    - reflexivity.
    - exfalso. destruct Hoblt as [h Hh]. exact (not_last_lt_ptr Hclosed Hisi h _ HbIn Hh). }
  subst ob.
  apply Build_IsItemValid.
  - exact (YjsLt'_ltOriginOrder _ _ (lt_first (Item First rb idb cb))).
  - intros x Hreach.
    inversion Hreach as [p1 q1 Hstep | p1 q1 r1 Hstep Hrest]; subst.
    + inversion Hstep; subst; [left|right]; apply YjsLeq'_leqSame.
    + inversion Hstep; subst.
      * exfalso. inversion Hrest as [u v Hs | u v w Hs Hr]; inversion Hs.
      * pose proof (origins_adjacent_in_reachable (ArrSet arr) Hisi First rb cb idb x HbIn Hrest) as [Hxob | Hrbx].
        -- left. exact Hxob.
        -- right.
           pose proof (reachable_in arr (Item First rb idb cb) Hclosed x Hrest HbIn) as HxIn.
           exact (transitivity.yjs_leq'_p_trans Hisi (Item First rb idb cb) rb x HbIn (closedRight _ Hclosed First rb idb cb HbIn) HxIn Hclosed (YjsLeq'_leqLt _ _ (item_lt_rightOrigin (Item First rb idb cb))) Hrbx).
Qed.

Lemma item_valid_tail (arr : list (YjsItem A)) (a : YjsItem A) (newid : YjsId) (c : A) :
  YjsArrInvariant arr -> base.lookup (length arr - 1)%nat arr = Some a ->
  IsItemValid (Item (itemPtr a) Last newid c).
Proof.
  intros Hinv Ha. destruct a as [oa ra ida ca].
  pose proof (yai_item_set_inv _ Hinv) as Hisi.
  pose proof (yai_closed _ Hinv) as Hclosed.
  assert (HaIn : ArrSet arr (Item oa ra ida ca)) by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Ha).
  assert (Hra : ra = Last).
  { pose proof (closedRight _ Hclosed oa ra ida ca HaIn) as Hrain.
    pose proof (item_lt_rightOrigin (Item oa ra ida ca)) as Hralt.
    destruct ra as [q | | ].
    - exfalso. destruct (list_basics.list.list_elem_of_lookup_1 _ _ Hrain) as [iq Hiq].
      assert (length arr - 1 < iq)%nat by exact (findptridx_order2.getElem_YjsLt'_index_lt arr (length arr - 1) iq (Item oa (itemPtr q) ida ca) q Hinv Ha Hiq Hralt).
      pose proof (list_basics.list.lookup_lt_Some _ _ _ Hiq) as Hbound. lia.
    - exfalso. exact (not_ptr_lt'_first Hclosed Hisi _ HaIn Hralt).
    - reflexivity. }
  subst ra.
  apply Build_IsItemValid.
  - exact (YjsLt'_ltOriginOrder _ _ (lt_last (Item oa Last ida ca))).
  - intros x Hreach.
    inversion Hreach as [p1 q1 Hstep | p1 q1 r1 Hstep Hrest]; subst.
    + inversion Hstep; subst; [left|right]; apply YjsLeq'_leqSame.
    + inversion Hstep; subst.
      * pose proof (origins_adjacent_in_reachable (ArrSet arr) Hisi oa Last ca ida x HaIn Hrest) as [Hxoa | Hrax].
        -- left.
           pose proof (reachable_in arr (Item oa Last ida ca) Hclosed x Hrest HaIn) as HxIn.
           apply YjsLeq'_leqLt.
           exact (transitivity.yjs_leq'_p_trans1 Hisi x oa (Item oa Last ida ca) HxIn (closedLeft _ Hclosed oa Last ida ca HaIn) HaIn Hclosed Hxoa (item_origin_lt (Item oa Last ida ca))).
        -- right. exact Hrax.
      * exfalso. inversion Hrest as [u v Hs | u v w Hs Hr]; inversion Hs.
Qed.

(** Unified validity for an insert straddling position [p]: the new item's
    origin is either [First] (at the head, [p = 0]) or the element at [p-1], and
    its right-origin is either [Last] (at the tail, [p = length arr]) or the
    element at [p]. Dispatches to the four boundary lemmas. This is what a
    general [Text.Insert] needs: the loop only has to know the [findPos]
    neighbours straddle [p]. *)
Lemma item_valid_at (arr : list (YjsItem A)) (p : nat) (newid : YjsId) (c : A) (o r : YjsPtr A) :
  YjsArrInvariant arr ->
  (p = 0%nat /\ o = First \/ (1 <= p)%nat /\ ∃ a, base.lookup (p-1)%nat arr = Some a /\ o = itemPtr a) ->
  (p = length arr /\ r = Last \/ ∃ b, base.lookup p arr = Some b /\ r = itemPtr b) ->
  IsItemValid (Item o r newid c).
Proof.
  intros Hinv Hleft Hright.
  destruct Hleft as [[Hp0 ->] | [Hp1 [a [Ha ->]]]].
  - destruct Hright as [[Hplen ->] | [b [Hb ->]]].
    + exact (item_valid_empty newid c).
    + subst p. exact (item_valid_head arr b newid c Hinv Hb).
  - destruct Hright as [[Hplen ->] | [b [Hb ->]]].
    + subst p. exact (item_valid_tail arr a newid c Hinv Ha).
    + have Hb' : base.lookup (S (p-1)) arr = Some b by (replace (S (p-1)) with p by lia; exact Hb).
      exact (item_valid_adjacent arr (p-1) a b newid c Hinv Ha Hb').
Qed.

(** The item [Text.Insert] builds at the straddle point is valid. Repackages
    [item_valid_at] over the exact origin facts [findPos] yields (a left/right
    neighbour by id, or the [First]/[Last] boundary), so the WP proof discharges
    [IsItemValid] in one application. *)
Lemma insert_item_valid (arr : list (YjsItem A)) (p : nat) (newid : YjsId) (c : A)
    (o r : YjsPtr A) (originIdLeft originIdRight : option YjsId) :
  YjsArrInvariant arr ->
  (originIdLeft = None /\ o = First /\ p = 0%nat
     \/ ∃ li, (1 <= p)%nat /\ arr !! (p - 1)%nat = Some li /\ originIdLeft = Some (item_id li) /\ o = itemPtr li) ->
  (originIdRight = None /\ r = Last /\ p = length arr
     \/ ∃ ri, arr !! p = Some ri /\ originIdRight = Some (item_id ri) /\ r = itemPtr ri) ->
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

End ytype_model.

(* ===== the type's run-granular model (plan-item-run-split stage 2) ========
   [type_model] is [type_state] without locations: the type's runs as data
   and its flattened document list. The projection [type_model_of] and the
   pool ([store/model.v]'s [pool]) sit on top; the heap side pairs it with
   the node-address list ([locs]). [runs_model] reads a run list as the
   abstract per-char sequence, the loc-free form of [ytype/value]'s
   [cells_model]. *)

Section ytype_run_model.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== definitions ======================================================== *)

(** [type_model]: one registered type, loc-free: its list of runs and the
    per-char document list they flatten to ([tm_arr = runs_flatten tm_runs]
    wherever the heap holds it; the equation is [cells_repr]'s projection,
    kept as a fact rather than folded away until stage 4). *)
Record type_model := MkTypeModel {
  tm_runs : list ItemRun;
  tm_arr  : list (YjsItem A);
}.

(** [run_models r] / [runs_model runs]: a run list read as the abstract
    per-char sequence [list (YjsItem A * bool)], each document item paired
    with its run's tombstone bit. The loc-free form of [ytype/value]'s
    [cell_models] / [cells_model] ([cells_model_runs] is the projection),
    which is what the run-granular specs state their content over. *)
Definition run_models (r : ItemRun) : list (YjsItem A * bool) :=
  (λ x, (x, run_deleted r)) <$> run_items r.

Definition runs_model (runs : list ItemRun) : list (YjsItem A * bool) :=
  mjoin (run_models <$> runs).

End ytype_run_model.
