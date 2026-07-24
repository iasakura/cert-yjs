(** Pure run theory for issue #28 (M4).

    The model-side heart of run integration: integrating an item whose left
    origin is a SUCCESSOR-FREE element [x] (no element of the document has
    [x] as its origin yet) lands immediately after [x]. Consequently the n
    chained per-char inputs of a multi-element wire item (each char's origin
    is the previous char, [run_wf]) integrate contiguously, and the heap's
    single-node splice refines n model steps.

    Iris-free and goose-free: everything here is about the pure [integrate]
    of rocq-yjs ([yjs.algorithm.insert_basic]). Sits between [yjs_core] and
    [yjs_store] in the Require chain; a candidate for upstreaming into
    rocq-yjs next to [insert_basic] once stable. *)
From stdpp Require Import base numbers list sorting gmap sets.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From New.proof Require Import yjs_core.

Section run_theory.
Context {A : Type} `{EqDecision A}.

Implicit Types (arr : list (YjsItem A)).

(** Distinct positions of a [uniqueId] array carry distinct ids (also proved
    in [yjs_store]; duplicated here to keep this file below the WP layer,
    fold there once this file is upstreamed). *)
Lemma uniqueId_lookup_ne' arr (i j : nat) (x y : YjsItem A) :
  uniqueId arr -> arr !! i = Some x -> arr !! j = Some y -> (i < j)%nat ->
  item_id x ≠ item_id y.
Proof.
  rewrite /uniqueId. move=> Hss Hi Hj Hij.
  have Hss' : StronglySorted (λ a b : YjsItem A, item_id a ≠ item_id b)
                (take (S i) arr ++ drop (S i) arr)
    by rewrite take_drop.
  apply (StronglySorted_app_1_elem_of _ (take (S i) arr) (drop (S i) arr) x y Hss').
  - apply (list_elem_of_lookup_2 _ i). rewrite lookup_take_lt; [exact Hi | lia].
  - apply (list_elem_of_lookup_2 _ (j - S i)%nat). rewrite lookup_drop.
    have -> : (S i + (j - S i))%nat = j by lia. exact Hj.
Qed.

(** A [uniqueId] array has no duplicate elements, so [find_item_idx] pins the
    known position. *)
Lemma find_item_idx_lookup arr (j : nat) (x : YjsItem A) :
  uniqueId arr -> arr !! j = Some x -> find_item_idx x arr = Some j.
Proof.
  move=> Huniq Hj. rewrite /find_item_idx.
  destruct (list_find (fun i => i = x) arr) as [[k y]|] eqn:Hfind; last first.
  { exfalso. move: Hfind. rewrite list_find_None Forall_lookup => Hnone.
    exact (Hnone j x Hj eq_refl). }
  apply list_find_Some in Hfind. destruct Hfind as (Hk & -> & Hfirst).
  simpl. f_equal.
  destruct (Nat.lt_trichotomy k j) as [Hlt | [-> | Hgt]]; [| done |].
  - exfalso. exact (uniqueId_lookup_ne' arr k j x x Huniq Hk Hj Hlt eq_refl).
  - exfalso. exact (Hfirst j x Hj Hgt eq_refl).
Qed.

Lemma findPtrIdx_item arr (j : nat) (x : YjsItem A) :
  uniqueId arr -> arr !! j = Some x ->
  findPtrIdx (itemPtr x) arr = Some (Z.of_nat j).
Proof.
  move=> Huniq Hj. rewrite /findPtrIdx (find_item_idx_lookup arr j x Huniq Hj) //.
Qed.

(** [findLeftIdx] by the id of a known element resolves to its position. *)
Lemma findLeftIdx_at arr (j : nat) (x : YjsItem A) :
  uniqueId arr -> arr !! j = Some x ->
  findLeftIdx (Some (item_id x)) arr = Some (Z.of_nat j).
Proof.
  move=> Huniq Hj. rewrite /findLeftIdx.
  destruct (list_find (fun it => item_id it = item_id x) arr) as [[k y]|] eqn:Hfind; last first.
  { exfalso. move: Hfind. rewrite list_find_None Forall_lookup => Hnone.
    exact (Hnone j x Hj eq_refl). }
  apply list_find_Some in Hfind. destruct Hfind as (Hk & Hid & Hfirst).
  simpl. do 2 f_equal.
  destruct (Nat.lt_trichotomy k j) as [Hlt | [-> | Hgt]]; [| done |].
  - exfalso. exact (uniqueId_lookup_ne' arr k j y x Huniq Hk Hj Hlt Hid).
  - exfalso. exact (Hfirst j x Hj Hgt eq_refl).
Qed.

(** Any pointer of the document (an element, or a sentinel) has an index. *)
Lemma findPtrIdx_closed arr (p : YjsPtr A) :
  YjsArrInvariant arr ->
  (∀ z : YjsItem A, p = itemPtr z -> z ∈ arr) ->
  ∃ i : Z, findPtrIdx p arr = Some i /\ (-1 <= i <= Z.of_nat (length arr))%Z.
Proof.
  move=> Hinv Hp. destruct p as [z | |].
  - have Hz : z ∈ arr := Hp z eq_refl.
    apply list_elem_of_lookup_1 in Hz. destruct Hz as [k Hk].
    exists (Z.of_nat k).
    split; [exact (findPtrIdx_item arr k z (yai_unique _ Hinv) Hk) |].
    apply lookup_lt_Some in Hk. lia.
  - exists (-1)%Z. split; [done | lia].
  - exists (Z.of_nat (length arr)). split; [done | lia].
Qed.

(** The adjacency kernel: when no element of the window right of [j] has the
    element at [j] as its origin, the very first scan step exits, so the
    integrated index is [j + 1]. *)
Lemma findIntegratedIndex_adjacent arr (j : nat) (x : YjsItem A)
    (input : IntegrateInput (A := A)) (rightIdx : Z) :
  YjsArrInvariant arr ->
  arr !! j = Some x ->
  (Z.of_nat j < rightIdx <= Z.of_nat (length arr))%Z ->
  (∀ z, z ∈ arr -> origin z ≠ itemPtr x) ->
  findIntegratedIndex (Z.of_nat j) rightIdx input arr = Some (S j).
Proof.
  move=> Hinv Hj Hri Hnosucc.
  rewrite /findIntegratedIndex.
  destruct (Z.to_nat (rightIdx - Z.of_nat j) - 1)%nat as [|count'] eqn:Hfuel.
  - (* window empty: rightIdx = j + 1 *)
    simpl. f_equal. lia.
  - (* first step: the window head's origin is strictly left of j *)
    have HSj : (S j < length arr)%nat by lia.
    destruct (arr !! S j) as [other|] eqn:Hother; last by (apply lookup_ge_None in Hother; lia).
    simpl.
    have -> : Z.to_nat (Z.of_nat j + Z.of_nat 1) = S j by lia.
    rewrite /getElemExcept Hother /=.
    have Hoin : other ∈ arr := list_elem_of_lookup_2 _ _ _ Hother.
    have Hoclosed : ∀ z : YjsItem A, origin other = itemPtr z -> z ∈ arr.
    { have Hclosed := yai_closed _ Hinv.
      move=> z Heq.
      destruct other as [o r id c]. simpl in Heq. subst o.
      exact (closedLeft _ Hclosed _ _ _ _ Hoin). }
    destruct (findPtrIdx_closed arr (origin other) Hinv Hoclosed) as (originLeftIdx & HoL & HoLb).
    rewrite HoL /=.
    have Horclosed : ∀ z : YjsItem A, rightOrigin other = itemPtr z -> z ∈ arr.
    { have Hclosed := yai_closed _ Hinv.
      move=> z Heq.
      destruct other as [o r id c]. simpl in Heq. subst r.
      exact (closedRight _ Hclosed _ _ _ _ Hoin). }
    destruct (findPtrIdx_closed arr (rightOrigin other) Hinv Horclosed) as (originRightIdx & HoR & HoRb).
    rewrite HoR /=.
    (* origin other sits strictly left of S j ... *)
    have Hlt : YjsLt' (origin other) (itemPtr other).
    { destruct other as [o r id c]. exists 1%nat. simpl.
      apply (ltOrigin 0). apply leqSame. }
    have HotherIdx : findPtrIdx (itemPtr other) arr = Some (Z.of_nat (S j))
      := findPtrIdx_item arr (S j) other (yai_unique _ Hinv) Hother.
    have HoLlt : (originLeftIdx < Z.of_nat (S j))%Z.
    { exact (findptridx_order2.YjsLt'_findPtrIdx_lt arr (origin other) (itemPtr other)
               originLeftIdx (Z.of_nat (S j)) Hinv
               ltac:(exact (findptridx_getelem.findPtrIdx_ArrSet arr _ originLeftIdx HoL))
               ltac:(exact (findptridx_getelem.findPtrIdx_ArrSet arr _ (Z.of_nat (S j)) HotherIdx))
               Hlt HoL HotherIdx). }
    (* ... and not AT j (no successor), so strictly below j: the loop exits *)
    have HoLne : originLeftIdx <> Z.of_nat j.
    { move=> HoLj. subst originLeftIdx.
      destruct (origin other) as [z | |] eqn:Horig;
        rewrite /findPtrIdx /= in HoL.
      - (* the element at index j is x itself: contradicts no-successor *)
        destruct (find_item_idx z arr) as [kz|] eqn:Hkz; simpl in HoL; last done.
        move: HoL => [= Hkzj].
        have Hkj : kz = j by lia.
        subst kz.
        move: Hkz. rewrite /find_item_idx.
        destruct (list_find (fun i => i = z) arr) as [[k' z']|] eqn:Hfind; last done.
        apply list_find_Some in Hfind. destruct Hfind as (Hk' & -> & _).
        move=> [= Hk'j]. subst k'.
        rewrite Hj in Hk'. injection Hk' as ->.
        exact (Hnosucc other Hoin Horig).
      - move: HoL => [= HoLj']. lia.
      - move: HoL => [= HoLj']. lia. }
    rewrite decide_True; last lia.
    simpl. f_equal. lia.
Qed.

(** Adjacency, packaged for [integrate]: with a successor-free origin [x] at
    [j] and a resolvable right origin strictly right of [j], integration is
    exactly the splice at [j + 1] of the item built from the input. *)
Lemma integrate_after_no_successor arr (j : nat) (x : YjsItem A)
    (input : IntegrateInput (A := A)) (rightIdx : Z) :
  YjsArrInvariant arr ->
  arr !! j = Some x ->
  in_originId input = Some (item_id x) ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  (Z.of_nat j < rightIdx)%Z ->
  (∀ z, z ∈ arr -> origin z ≠ itemPtr x) ->
  ∃ (rptr : YjsPtr A),
    getPtrExcept arr rightIdx = Some rptr /\
    integrate input arr
      = Some (take (S j) arr ++ Item (itemPtr x) rptr (in_id input) (in_content input) :: drop (S j) arr).
Proof.
  move=> Hinv Hj Hoin Hri Hjr Hnosucc.
  have Huniq := yai_unique _ Hinv.
  have HriUB : (rightIdx <= Z.of_nat (length arr))%Z.
  { move: Hri. rewrite /findRightIdx.
    destruct (in_rightOriginId input) as [rightOriginId|].
    - destruct (list_find _ arr) as [[k y]|] eqn:Hf; last done.
      move=> [=] <-. apply list_find_Some in Hf. destruct Hf as (Hk & _ & _).
      apply lookup_lt_Some in Hk. lia.
    - move=> [=] <-. lia. }
  have Hrptr : ∃ rptr, getPtrExcept arr rightIdx = Some rptr.
  { rewrite /getPtrExcept.
    destruct (decide (rightIdx = -1)%Z); first lia.
    destruct (decide (rightIdx = Z.of_nat (length arr))%Z); first by eexists.
    have Hlt : (Z.to_nat rightIdx < length arr)%nat by lia.
    destruct (arr !! Z.to_nat rightIdx) as [ri|] eqn:Hriv;
      [by eexists | apply lookup_ge_None in Hriv; lia]. }
  destruct Hrptr as [rptr Hrptr]. exists rptr. split; first exact Hrptr.
  rewrite /integrate.
  rewrite Hoin (findLeftIdx_at arr j x Huniq Hj) /=.
  rewrite Hri /=.
  rewrite (findIntegratedIndex_adjacent arr j x input rightIdx Hinv Hj
             (conj Hjr HriUB) Hnosucc) /=.
  rewrite /mkItemByIndex.
  have HgetJ : getPtrExcept arr (Z.of_nat j) = Some (itemPtr x).
  { rewrite /getPtrExcept.
    have Hjlt : (j < length arr)%nat by (apply lookup_lt_Some in Hj).
    destruct (decide (Z.of_nat j = -1)%Z); first lia.
    destruct (decide (Z.of_nat j = Z.of_nat (length arr))%Z); first lia.
    rewrite Nat2Z.id Hj //. }
  rewrite HgetJ /= Hrptr /=.
  rewrite /insertIdxIfInBounds decide_True; last first.
  { apply lookup_lt_Some in Hj. lia. }
  done.
Qed.


(* ===== the chained fold: a run integrates contiguously ==================== *)

(** [chained_after xid rightOriginId inputs]: each input's left origin is the id of the
    previous input (starting from [xid]) and all inputs share the right origin
    [rightOriginId]. This is the wire shape of a multi-element run seen per-char
    ([run_wf] on the heap side). *)
Fixpoint chained_after (xid : YjsId) (rightOriginId : option YjsId)
    (inputs : list (IntegrateInput (A := A))) : Prop :=
  match inputs with
  | [] => True
  | i :: rest =>
      i.(in_originId) = Some xid ∧ i.(in_rightOriginId) = rightOriginId ∧
      chained_after i.(in_id) rightOriginId rest
  end.

(** Monadic fold of [integrate]. *)
Fixpoint integrate_all (inputs : list (IntegrateInput (A := A)))
    (arr : list (YjsItem A)) : option (list (YjsItem A)) :=
  match inputs with
  | [] => Some arr
  | i :: rest => arr' ← integrate i arr; integrate_all rest arr'
  end.

(** The ids an input list mints. *)
Definition input_ids (inputs : list (IntegrateInput (A := A))) : list YjsId :=
  (fun i => i.(in_id)) <$> inputs.

(** Fresh ids: none of the minted ids occurs in the document, and they are
    pairwise distinct (consecutive clocks in practice). *)
Definition ids_fresh (arr : list (YjsItem A))
    (inputs : list (IntegrateInput (A := A))) : Prop :=
  (forall z, z ∈ arr -> forall i inp, inputs !! i = Some inp ->
     item_id z ≠ inp.(in_id)) ∧
  NoDup (input_ids inputs).

(** Origin-reachability stays inside a closed set. *)
Lemma reachable_in_set (P : YjsPtr A -> Prop) (x p : YjsPtr A) :
  IsClosedItemSet P -> P x -> OriginReachable x p -> P p.
Proof.
  move=> Hc Hx Hr. move: Hr Hx. elim.
  - move=> x' y' Hstep Hx'.
    inversion Hstep; subst;
      [exact (closedLeft _ Hc _ _ _ _ Hx') | exact (closedRight _ Hc _ _ _ _ Hx')].
  - move=> x' y' z' Hstep _ IH Hx'. apply IH.
    inversion Hstep; subst;
      [exact (closedLeft _ Hc _ _ _ _ Hx') | exact (closedRight _ Hc _ _ _ _ Hx')].
Qed.

(** The telescoping heart of run validity: if [cur] is a valid member of a
    valid closed set and its right origin is [rptr], then the next chain link
    (origin [cur], right origin [rptr]) is a valid item too. Everything the
    new link can reach goes through [cur] or through [rptr]; the paths through
    [rptr] are also paths of [cur], so [cur]'s own validity bounds them. *)
Lemma chain_link_valid (P : YjsPtr A -> Prop) (cur : YjsItem A) (rptr : YjsPtr A)
    (id' : YjsId) (c' : A) :
  IsClosedItemSet P -> ItemSetInvariant P ->
  P (itemPtr cur) ->
  rightOrigin cur = rptr ->
  IsItemValid cur ->
  IsItemValid (Item (itemPtr cur) rptr id' c').
Proof.
  move=> Hc Hinv Hcur Hror Hvalid.
  have Hcur_lt_r : YjsLt' (itemPtr cur) rptr.
  { rewrite -Hror. destruct cur as [o r id c]. exists 1%nat.
    apply (ltRightOrigin 0). apply leqSame. }
  have Horigin_cur : P (origin cur).
  { destruct cur as [o r id c]. exact (closedLeft _ Hc _ _ _ _ Hcur). }
  have Hstep_right : OriginReachableStep (itemPtr cur) rptr.
  { rewrite -Hror. destruct cur as [o r id c]. apply reachable_right. }
  constructor.
  - (* origin < rightOrigin *)
    simpl. exact Hcur_lt_r.
  - (* reachability *)
    move=> p Hreach. simpl.
    have Hvia_cur : forall q, OriginReachable (itemPtr cur) q ->
        YjsLeq' q (itemPtr cur) \/ YjsLeq' rptr q.
    { move=> q Hq.
      have Hpq : P q := reachable_in_set P (itemPtr cur) q Hc Hcur Hq.
      case: (iiv_reachable _ Hvalid q Hq) => [Hle | Hge].
      - left.
        have Holt : YjsLt' (origin cur) (itemPtr cur) := item_origin_lt cur.
        apply YjsLeq'_leqLt.
        exact (transitivity.yjs_leq'_p_trans1 Hinv q (origin cur) (itemPtr cur)
                 Hpq Horigin_cur Hcur Hc Hle Holt).
      - right. rewrite -Hror. exact Hge. }
    (* the two edges out of the new link *)
    inversion Hreach as [x0 y0 Hstep | x0 y0 z0 Hstep Hr']; subst.
    + (* single step: origin or right origin of the new link itself *)
      inversion Hstep; subst.
      * left. exists 0%nat. apply leqSame.
      * right. exists 0%nat. apply leqSame.
    + (* longer path: through [cur] or through [rptr] *)
      inversion Hstep; subst.
      * (* via the origin edge = via [cur] *)
        exact (Hvia_cur p Hr').
      * (* via the right-origin edge: also a path of [cur] *)
        exact (Hvia_cur p (reachable_head _ _ _ Hstep_right Hr')).
Qed.

(* ----- splice arithmetic -------------------------------------------------- *)

Lemma splice_length arr (j : nat) (newit : YjsItem A) :
  (j < length arr)%nat ->
  length (take (S j) arr ++ newit :: drop (S j) arr) = S (length arr).
Proof.
  move=> Hj. rewrite length_app /= length_take length_drop. lia.
Qed.

Lemma splice_lookup arr (j : nat) (newit : YjsItem A) (i : nat) :
  (j < length arr)%nat ->
  (take (S j) arr ++ newit :: drop (S j) arr) !! i
  = if decide (i < S j)%nat then arr !! i
    else if decide (i = S j) then Some newit
    else arr !! (i - 1)%nat.
Proof.
  move=> Hj.
  have Hlt : length (take (S j) arr) = S j by (rewrite length_take; lia).
  destruct (decide (i < S j)%nat) as [Hi | Hi].
  - rewrite lookup_app_l; last lia. rewrite lookup_take_lt //.
  - rewrite lookup_app_r; last lia. rewrite Hlt.
    destruct (decide (i = S j)) as [-> | Hne].
    + rewrite Nat.sub_diag //.
    + have Hpos : (0 < i - S j)%nat by lia.
      destruct (i - S j)%nat as [|d] eqn:Hd; first lia.
      simpl. rewrite lookup_drop. f_equal. lia.
Qed.

(* ----- [toItem] over resolved ids ------------------------------------------ *)

Lemma find_by_id_at arr (j : nat) (x : YjsItem A) :
  uniqueId arr -> arr !! j = Some x ->
  find_by_id (item_id x) arr = Some x.
Proof.
  move=> Huniq Hj. rewrite /find_by_id.
  destruct (list_find (fun it => item_id it = item_id x) arr) as [[k y]|] eqn:Hfind; last first.
  { exfalso. move: Hfind. rewrite list_find_None Forall_lookup => Hnone.
    exact (Hnone j x Hj eq_refl). }
  apply list_find_Some in Hfind. destruct Hfind as (Hk & Hid & Hfirst).
  simpl. f_equal.
  destruct (Nat.lt_trichotomy k j) as [Hlt | [-> | Hgt]].
  - exfalso. exact (uniqueId_lookup_ne' arr k j y x Huniq Hk Hj Hlt Hid).
  - rewrite Hj in Hk. by injection Hk.
  - exfalso. exact (Hfirst j x Hj Hgt eq_refl).
Qed.

(** [toItem] with a resolved left origin and the right origin as
    [findRightIdx]/[getPtrExcept] see it. *)
Lemma toItem_resolved arr (j : nat) (x : YjsItem A)
    (rightIdx : Z) (rptr : YjsPtr A) (input : IntegrateInput (A := A)) :
  YjsArrInvariant arr ->
  arr !! j = Some x ->
  input.(in_originId) = Some (item_id x) ->
  findRightIdx input.(in_rightOriginId) arr = Some rightIdx ->
  getPtrExcept arr rightIdx = Some rptr ->
  toItem input arr = Some (Item (itemPtr x) rptr input.(in_id) input.(in_content)).
Proof.
  move=> Hinv Hj Hoin Hri Hgp.
  have Huniq := yai_unique _ Hinv.
  rewrite /toItem Hoin (find_by_id_at arr j x Huniq Hj) /=.
  move: Hri Hgp. rewrite /findRightIdx.
  destruct (input.(in_rightOriginId)) as [r_id|] eqn:Hrid.
  - destruct (list_find (fun it => item_id it = r_id) arr) as [[k R]|] eqn:Hfind; last done.
    move=> [= <-].
    apply list_find_Some in Hfind. destruct Hfind as (Hk & HidR & _).
    rewrite /getPtrExcept.
    destruct (decide (Z.of_nat k = -1)%Z); first lia.
    have Hklt : (k < length arr)%nat by (apply lookup_lt_Some in Hk).
    destruct (decide (Z.of_nat k = Z.of_nat (length arr))%Z); first lia.
    rewrite Nat2Z.id Hk /=.
    move=> [= <-].
    rewrite /find_by_id.
    destruct (list_find (fun it => item_id it = r_id) arr) as [[k' R']|] eqn:Hfind'; last first.
    { exfalso. move: Hfind'. rewrite list_find_None Forall_lookup => Hnone.
      exact (Hnone k R Hk HidR). }
    apply list_find_Some in Hfind'. destruct Hfind' as (Hk' & HidR' & Hfirst').
    simpl.
    have HkR : k' = k /\ R' = R.
    { destruct (Nat.lt_trichotomy k' k) as [Hlt | [-> | Hgt]].
      - exfalso.
        (* both carry id r_id at distinct positions: unique ids *)
        exact (uniqueId_lookup_ne' arr k' k R' R Huniq Hk' Hk Hlt
                 (eq_trans HidR' (eq_sym HidR))).
      - rewrite Hk in Hk'. split; [done | by injection Hk'].
      - exfalso. exact (Hfirst' k R Hk Hgt HidR). }
    destruct HkR as [-> ->]. done.
  - move=> [= <-].
    rewrite /getPtrExcept.
    destruct (decide (Z.of_nat (length arr) = -1)%Z); first lia.
    destruct (decide (Z.of_nat (length arr) = Z.of_nat (length arr))%Z); last lia.
    move=> [= <-]. done.
Qed.

(* ----- the splice shifts the right-origin index by one --------------------- *)

Lemma findRightIdx_splice_shift arr (j : nat) (newit : YjsItem A)
    (rightOriginId : option YjsId) (rightIdx : Z) :
  (j < length arr)%nat ->
  (Z.of_nat j < rightIdx)%Z ->
  uniqueId arr ->
  findRightIdx rightOriginId arr = Some rightIdx ->
  (forall z, z ∈ arr -> item_id z ≠ item_id newit) ->
  findRightIdx rightOriginId (take (S j) arr ++ newit :: drop (S j) arr) = Some (rightIdx + 1)%Z.
Proof.
  move=> Hj Hjr Huniq Hri Hfresh.
  move: Hri. rewrite /findRightIdx.
  destruct rightOriginId as [r_id|]; last first.
  { move=> [= <-]. rewrite (splice_length arr j newit Hj). f_equal. lia. }
  destruct (list_find (fun it => item_id it = r_id) arr) as [[k R]|] eqn:Hfind; last done.
  move=> [= HrIdx].
  apply list_find_Some in Hfind. destruct Hfind as (Hk & HidR & Hfirst).
  have Hkarr : (k < length arr)%nat by (apply lookup_lt_Some in Hk).
  have Hjk : (j < k)%nat by lia.
  have Hfind' : list_find (fun it => item_id it = r_id)
                  (take (S j) arr ++ newit :: drop (S j) arr) = Some (S k, R).
  { apply list_find_Some. split_and!.
    - rewrite (splice_lookup arr j newit (S k) Hj).
      destruct (decide (S k < S j)%nat); first lia.
      destruct (decide (S k = S j)); first lia.
      rewrite /= Nat.sub_0_r //.
    - exact HidR.
    - move=> i y Hlook Hilt.
      rewrite (splice_lookup arr j newit i Hj) in Hlook.
      destruct (decide (i < S j)%nat) as [Hij | Hij].
      + (* an old element strictly before the old first match *)
        apply (Hfirst i y Hlook). lia.
      + destruct (decide (i = S j)) as [-> | Hne].
        * (* the fresh element: its id is fresh, in particular not [r_id] *)
          injection Hlook as <-.
          move=> HidN.
          have HRin : R ∈ arr := list_elem_of_lookup_2 _ _ _ Hk.
          exact (Hfresh R HRin (eq_trans HidR (eq_sym HidN))).
        * (* an old element shifted by one, still before the old match *)
          apply (Hfirst (i - 1)%nat y Hlook). lia. }
  rewrite Hfind' /=. f_equal. lia.
Qed.

Lemma getPtrExcept_splice_shift arr (j : nat) (newit : YjsItem A)
    (rightIdx : Z) (rptr : YjsPtr A) :
  (j < length arr)%nat ->
  (Z.of_nat j < rightIdx)%Z ->
  getPtrExcept arr rightIdx = Some rptr ->
  getPtrExcept (take (S j) arr ++ newit :: drop (S j) arr) (rightIdx + 1) = Some rptr.
Proof.
  move=> Hj Hjr.
  rewrite /getPtrExcept.
  destruct (decide (rightIdx = -1)%Z); first lia.
  rewrite (splice_length arr j newit Hj).
  destruct (decide (rightIdx = Z.of_nat (length arr))%Z) as [-> | Hne].
  - move=> [= <-].
    destruct (decide (Z.of_nat (length arr) + 1 = -1)%Z); first lia.
    destruct (decide (Z.of_nat (length arr) + 1 = Z.of_nat (S (length arr)))%Z); last lia.
    done.
  - destruct (arr !! Z.to_nat rightIdx) as [R|] eqn:HR; last done.
    move=> [= <-].
    have Hrlt : (Z.to_nat rightIdx < length arr)%nat by (apply lookup_lt_Some in HR).
    destruct (decide (rightIdx + 1 = -1)%Z); first lia.
    destruct (decide (rightIdx + 1 = Z.of_nat (S (length arr)))%Z); first lia.
    rewrite (splice_lookup arr j newit (Z.to_nat (rightIdx + 1)) Hj).
    destruct (decide (Z.to_nat (rightIdx + 1) < S j)%nat); first lia.
    destruct (decide (Z.to_nat (rightIdx + 1) = S j)); first lia.
    have -> : (Z.to_nat (rightIdx + 1) - 1)%nat = Z.to_nat rightIdx by lia.
    rewrite HR //.
Qed.

(* ----- the run integrates contiguously ------------------------------------- *)

Lemma splice_elem_of arr (j : nat) (newit z : YjsItem A) :
  z ∈ (take (S j) arr ++ newit :: drop (S j) arr) -> z = newit \/ z ∈ arr.
Proof.
  move=> Hz. apply elem_of_app in Hz. destruct Hz as [Hz | Hz].
  - right. apply list_elem_of_lookup_1 in Hz. destruct Hz as [i Hi].
    apply lookup_take_Some in Hi. destruct Hi as [Hi _].
    exact (list_elem_of_lookup_2 _ _ _ Hi).
  - apply elem_of_cons in Hz. destruct Hz as [-> | Hz]; [by left | right].
    apply list_elem_of_lookup_1 in Hz. destruct Hz as [i Hi].
    rewrite lookup_drop in Hi.
    exact (list_elem_of_lookup_2 _ _ _ Hi).
Qed.

(** THE run theorem: a chained input list with fresh ids, a valid head, and
    per-char clock maximality integrates as ONE contiguous splice right after
    its anchor. This is what lets the heap integrate a multi-element node in a
    single splice while the model steps per char (issue #28 M4). *)
Lemma integrate_chain (inputs : list (IntegrateInput (A := A))) :
  forall arr (j : nat) (x : YjsItem A) (rightOriginId : option YjsId) (rightIdx : Z) (rptr : YjsPtr A),
  YjsArrInvariant arr ->
  arr !! j = Some x ->
  chained_after (item_id x) rightOriginId inputs ->
  ids_fresh arr inputs ->
  (forall i inp, inputs !! i = Some inp -> item_id x ≠ inp.(in_id)) ->
  findRightIdx rightOriginId arr = Some rightIdx ->
  (Z.of_nat j < rightIdx)%Z ->
  getPtrExcept arr rightIdx = Some rptr ->
  (forall z, z ∈ arr -> origin z ≠ itemPtr x) ->
  (forall i0 rest0, inputs = i0 :: rest0 ->
     IsItemValid (Item (itemPtr x) rptr i0.(in_id) i0.(in_content))) ->
  (forall k inp, inputs !! k = Some inp ->
     forall z, z ∈ arr -> clientId (item_id z) = clientId inp.(in_id) ->
       (clock (item_id z) < clock inp.(in_id))%nat) ->
  (forall i k inpi inpk, (i < k)%nat -> inputs !! i = Some inpi -> inputs !! k = Some inpk ->
     clientId inpi.(in_id) = clientId inpk.(in_id) ->
     (clock inpi.(in_id) < clock inpk.(in_id))%nat) ->
  exists news : list (YjsItem A),
    integrate_all inputs arr = Some (take (S j) arr ++ news ++ drop (S j) arr) ∧
    length news = length inputs ∧
    YjsArrInvariant (take (S j) arr ++ news ++ drop (S j) arr) ∧
    (forall k inp, inputs !! k = Some inp -> exists it, news !! k = Some it ∧
       item_id it = inp.(in_id) ∧ content it = inp.(in_content) ∧
       rightOrigin it = rptr ∧
       (k = 0%nat -> origin it = itemPtr x) ∧
       (forall k' itp, k = S k' -> news !! k' = Some itp -> origin it = itemPtr itp)).
Proof.
  induction inputs as [|input rest IH];
    intros arr j x rightOriginId rightIdx rptr
      Hinv Hj Hchain Hfresh Hxid Hri Hjr Hrptr Hnosucc Hvalid0 Hmaxs Hchainclk.
  - (* empty chain *)
    exists []. simpl. rewrite take_drop.
    split_and!; [done | done | exact Hinv | by move=> k inp Hk].
  - (* input :: rest *)
    destruct Hchain as (Hoin & Hrin & Hchain').
    destruct Hfresh as [Hfresh Hnodup].
    have Hjlen : (j < length arr)%nat by (apply lookup_lt_Some in Hj).
    (* the head integrates right after the anchor *)
    have Hri' : findRightIdx input.(in_rightOriginId) arr = Some rightIdx
      by rewrite Hrin.
    destruct (integrate_after_no_successor arr j x input rightIdx
                Hinv Hj Hoin Hri' Hjr Hnosucc) as (rptr0 & Hrptr0 & Hint0).
    have Heqr : rptr0 = rptr.
    { rewrite Hrptr in Hrptr0. by injection Hrptr0. }
    subst rptr0.
    set (newit := Item (itemPtr x) rptr input.(in_id) input.(in_content)).
    set (arr1 := take (S j) arr ++ newit :: drop (S j) arr).
    have Hvalid0' : IsItemValid newit := Hvalid0 input rest eq_refl.
    have Htoit : toItem input arr = Some newit
      := toItem_resolved arr j x rightIdx rptr input Hinv Hj Hoin Hri' Hrptr.
    have Hmax0 : maximalId newit arr.
    { move=> z Hz Hcz. exact (Hmaxs 0%nat input eq_refl z Hz Hcz). }
    destruct (YjsArrInvariant_integrate input arr arr1 newit Hinv Htoit Hvalid0' Hmax0 Hint0)
      as (i0 & _ & _ & Hinv1).
    (* facts for the tail at the new anchor [newit] *)
    have Hj1 : arr1 !! S j = Some newit.
    { rewrite /arr1 (splice_lookup arr j newit (S j) Hjlen).
      destruct (decide (S j < S j)%nat); first lia.
      destruct (decide (S j = S j)); [done | lia]. }
    have Hidnew : item_id newit = input.(in_id) by done.
    have Hheadfresh : forall z, z ∈ arr -> item_id z ≠ item_id newit.
    { move=> z Hz. exact (Hfresh z Hz 0%nat input eq_refl). }
    have Hnodup' : input.(in_id) ∉ input_ids rest /\ NoDup (input_ids rest).
    { move: Hnodup. rewrite /input_ids fmap_cons NoDup_cons. done. }
    destruct Hnodup' as [Hnotin Hnodup'].
    have Hidtail : forall i inp, rest !! i = Some inp -> input.(in_id) ≠ inp.(in_id).
    { move=> i inp Hi Heq. apply Hnotin. rewrite Heq /input_ids.
      apply list_elem_of_fmap_2. exact (list_elem_of_lookup_2 _ _ _ Hi). }
    have Hfresh1 : ids_fresh arr1 rest.
    { split; last exact Hnodup'.
      move=> z Hz i inp Hinp.
      case: (splice_elem_of arr j newit z Hz) => [-> | Hz'].
      - rewrite Hidnew. exact (Hidtail i inp Hinp).
      - exact (Hfresh z Hz' (S i) inp Hinp). }
    have Hxid1 : forall i inp, rest !! i = Some inp -> item_id newit ≠ inp.(in_id).
    { move=> i inp Hi. rewrite Hidnew. exact (Hidtail i inp Hi). }
    have Hri1 : findRightIdx rightOriginId arr1 = Some (rightIdx + 1)%Z
      := findRightIdx_splice_shift arr j newit rightOriginId rightIdx Hjlen Hjr
           (yai_unique _ Hinv) Hri Hheadfresh.
    have Hjr1 : (Z.of_nat (S j) < rightIdx + 1)%Z by lia.
    have Hrptr1 : getPtrExcept arr1 (rightIdx + 1) = Some rptr
      := getPtrExcept_splice_shift arr j newit rightIdx rptr Hjlen Hjr Hrptr.
    have Hnosucc1 : forall z, z ∈ arr1 -> origin z ≠ itemPtr newit.
    { move=> z Hz.
      case: (splice_elem_of arr j newit z Hz) => [-> | Hz'].
      - (* [newit]'s own origin is [x], which has a non-fresh id *)
        rewrite /newit /=. move=> Heq.
        have Hxeq : x = newit by (injection Heq).
        apply (Hxid 0%nat input eq_refl). rewrite Hxeq //.
      - (* an old element: its origin lives in [arr] by closedness, but
           [newit]'s id is fresh *)
        move=> Horig.
        have Hcl := yai_closed _ Hinv.
        destruct z as [oz rz idz cz]. simpl in Horig. subst oz.
        have Hznew : ArrSet arr (itemPtr newit)
          := closedLeft _ Hcl _ _ _ _ Hz'.
        simpl in Hznew.
        exact (Hheadfresh newit Hznew eq_refl). }
    have Hvalid1 : forall i1 rest1, rest = i1 :: rest1 ->
        IsItemValid (Item (itemPtr newit) rptr i1.(in_id) i1.(in_content)).
    { move=> i1 rest1 _.
      apply (chain_link_valid (ArrSet arr1) newit rptr i1.(in_id) i1.(in_content)
               (yai_closed _ Hinv1) (yai_item_set_inv _ Hinv1)).
      - simpl. exact (list_elem_of_lookup_2 _ _ _ Hj1).
      - done.
      - exact Hvalid0'. }
    have Hmaxs1 : forall k inp, rest !! k = Some inp ->
        forall z, z ∈ arr1 -> clientId (item_id z) = clientId inp.(in_id) ->
          (clock (item_id z) < clock inp.(in_id))%nat.
    { move=> k inp Hk z Hz Hcz.
      case: (splice_elem_of arr j newit z Hz) => [Heq | Hz']; [subst z |].
      - rewrite Hidnew. rewrite Hidnew in Hcz.
        exact (Hchainclk 0%nat (S k) input inp ltac:(lia) eq_refl Hk Hcz).
      - exact (Hmaxs (S k) inp Hk z Hz' Hcz). }
    have Hchainclk1 : forall i k inpi inpk, (i < k)%nat ->
        rest !! i = Some inpi -> rest !! k = Some inpk ->
        clientId inpi.(in_id) = clientId inpk.(in_id) ->
        (clock inpi.(in_id) < clock inpk.(in_id))%nat.
    { move=> i k inpi inpk Hik Hi Hk.
      exact (Hchainclk (S i) (S k) inpi inpk ltac:(lia) Hi Hk). }
    have Hchain1 : chained_after (item_id newit) rightOriginId rest by rewrite Hidnew.
    (* the tail integrates contiguously after [newit] *)
    destruct (IH arr1 (S j) newit rightOriginId (rightIdx + 1)%Z rptr
                Hinv1 Hj1 Hchain1 Hfresh1 Hxid1 Hri1 Hjr1 Hrptr1 Hnosucc1 Hvalid1
                Hmaxs1 Hchainclk1)
      as (news' & Hint' & Hlen' & Hinv' & Hfacts').
    (* compose the two splices *)
    have Hlentake : length (take (S j) arr) = S j by (rewrite length_take; lia).
    have Htake1 : take (S (S j)) arr1 = take (S j) arr ++ [newit].
    { rewrite /arr1 take_app_ge; last lia.
      rewrite Hlentake.
      have -> : (S (S j) - S j)%nat = 1%nat by lia.
      done. }
    have Hdrop1 : drop (S (S j)) arr1 = drop (S j) arr.
    { rewrite /arr1 drop_app_ge; last lia.
      rewrite Hlentake.
      have -> : (S (S j) - S j)%nat = 1%nat by lia.
      done. }
    exists (newit :: news').
    have Hcompose : take (S (S j)) arr1 ++ news' ++ drop (S (S j)) arr1
                  = take (S j) arr ++ (newit :: news') ++ drop (S j) arr.
    { rewrite Htake1 Hdrop1 -app_assoc //. }
    split_and!.
    + simpl. rewrite Hint0 /=. rewrite Hint' Hcompose //.
    + simpl. rewrite Hlen' //.
    + rewrite -Hcompose. exact Hinv'.
    + move=> k inp Hk.
      destruct k as [|k'].
      * injection Hk as <-.
        exists newit. split_and!; try done.
      * simpl in Hk.
        destruct (Hfacts' k' inp Hk) as (it & Hit & Hitid & Hitc & Hitr & Hit0 & Hitchain).
        exists it. split_and!; try done.
        move=> k'' itp Hk'' Hitp.
        injection Hk'' as Hkeq. subst k''.
        destruct k' as [|k'''].
        -- (* the second char's origin is the head char *)
           simpl in Hitp. injection Hitp as Hitp'. subst itp.
           exact (Hit0 eq_refl).
        -- simpl in Hitp.
           exact (Hitchain k''' itp eq_refl Hitp).
Qed.

(* ===== the run-block scan bridge (issue #28 M4, part 3) ===================
   The heap scan steps NODE by node while [setfii_loop] steps char by char.
   A [run_wf] block behaves as one unit inside the scan: the head char decides
   the outcome exactly as the node-level Go does, and the tail chars cascade
   deterministically (their origin is always the previous char, which was just
   scanned). [setfii_block_step] below packages one whole block as a single
   rewrite, so a node-stepping WP loop invariant can couple to [setfii_loop]
   at block boundaries only. *)

Definition char_ids (r : list (YjsItem A)) : gset YjsId :=
  list_to_set (item_id <$> r).

Lemma char_ids_cons (c : YjsItem A) (r : list (YjsItem A)) :
  char_ids (c :: r) = {[item_id c]} ∪ char_ids r.
Proof. rewrite /char_ids fmap_cons list_to_set_cons //. Qed.

(** The chaining discipline of a run's chars, as this module consumes it (the
    WP layer's [run_wf] destructs to exactly this; stated inline so this file
    stays below the heap layer). *)
Definition run_step (r : list (YjsItem A)) : Prop :=
  forall (k : nat) (x y : YjsItem A), r !! k = Some x -> r !! S k = Some y ->
    item_id y = MkYjsId (clientId (item_id x)) (S (clock (item_id x))) ∧
    origin y = itemPtr x ∧
    rightOrigin y = rightOrigin x.

(** Along a chained run, each char's origin id is the previous char's id, and
    consecutive ids differ (the clock strictly increments). *)
Lemma run_step_tail_origin (r : list (YjsItem A)) (k : nat) (x y : YjsItem A) :
  run_step r -> r !! k = Some x -> r !! S k = Some y ->
  origin_id (origin y) = Some (item_id x) ∧ item_id x ≠ item_id y.
Proof.
  move=> Hstep Hx Hy.
  destruct (Hstep k x y Hx Hy) as (Hid & Horig & _).
  split.
  - rewrite Horig //.
  - rewrite Hid. move=> Heq.
    have : clock (item_id x) = clock (MkYjsId (clientId (item_id x)) (S (clock (item_id x))))
      by rewrite -Heq.
    simpl. lia.
Qed.

Lemma run_step_tail (x : YjsItem A) (l : list (YjsItem A)) :
  run_step (x :: l) -> run_step l.
Proof.
  move=> Hstep k a b Ha Hb. exact (Hstep (S k) a b Ha Hb).
Qed.

(** Tail cascade, STAY flavor: with the previous char's id in both
    accumulators, every tail char takes the continue-unchanged branch and the
    accumulators absorb the block. *)
Lemma setfii_tail_stay (tail : list (YjsItem A)) :
  forall (prev : YjsItem A) (restfuel offset : nat) (leftIdx rightIdx : Z)
    (oLeftId oRightId : option YjsId) (newId : YjsId)
    (arr : list (YjsItem A)) (idsBeforeOrigin ci : gset YjsId) (destIdx : Z),
  run_step (prev :: tail) ->
  (forall k c, tail !! k = Some c ->
     arr !! (Z.to_nat (leftIdx + Z.of_nat (offset + k))) = Some c) ->
  (forall c, c ∈ prev :: tail -> Some (item_id c) ≠ oLeftId) ->
  item_id prev ∈ idsBeforeOrigin ->
  item_id prev ∈ ci ->
  setfii_loop (length tail + restfuel) offset leftIdx rightIdx oLeftId oRightId newId arr idsBeforeOrigin ci destIdx
  = setfii_loop restfuel (offset + length tail)%nat leftIdx rightIdx oLeftId oRightId newId arr
      (char_ids tail ∪ idsBeforeOrigin) (char_ids tail ∪ ci) destIdx.
Proof.
  induction tail as [|c tail' IH];
    intros prev restfuel offset leftIdx rightIdx oLeftId oRightId newId arr idsBeforeOrigin ci destIdx
      Hstep Hlook Hnotleft Hpibo Hpici.
  - simpl. rewrite Nat.add_0_r.
    have -> : char_ids [] ∪ idsBeforeOrigin = idsBeforeOrigin by set_solver.
    have -> : char_ids [] ∪ ci = ci by set_solver.
    done.
  - simpl length. simpl plus.
    (* unfold one loop step for [c] *)
    simpl setfii_loop.
    have Hc0 : arr !! Z.to_nat (leftIdx + Z.of_nat offset) = Some c.
    { have := Hlook 0%nat c eq_refl. rewrite Nat.add_0_r //. }
    rewrite Hc0 /=.
    have [Hor Hne] : origin_id (origin c) = Some (item_id prev) ∧
                     item_id prev ≠ item_id c
      := run_step_tail_origin (prev :: c :: tail') 0 prev c Hstep eq_refl eq_refl.
    have Hnl : origin_id (origin c) ≠ oLeftId.
    { rewrite Hor. apply Hnotleft. apply elem_of_cons. by left. }
    rewrite decide_False; last exact Hnl.
    rewrite Hor.
    rewrite decide_True; last first.
    { apply elem_of_union. right. exact Hpibo. }
    rewrite decide_False; last first.
    { move=> Hnotin. apply Hnotin. apply elem_of_union. right. exact Hpici. }
    (* continue-unchanged: recurse with [c] as the new previous char *)
    have Hstep' : run_step (c :: tail') := run_step_tail prev (c :: tail') Hstep.
    have Hlook' : forall k c0, tail' !! k = Some c0 ->
        arr !! Z.to_nat (leftIdx + Z.of_nat (S offset + k)) = Some c0.
    { move=> k c0 Hk. have := Hlook (S k) c0 Hk.
      have -> : (offset + S k)%nat = (S offset + k)%nat by lia.
      done. }
    have Hnl' : forall c0, c0 ∈ c :: tail' -> Some (item_id c0) ≠ oLeftId.
    { move=> c0 Hc0'. apply Hnotleft. apply elem_of_cons. right. exact Hc0'. }
    have Hin1 : item_id c ∈ ({[item_id c]} ∪ idsBeforeOrigin) by set_solver.
    have Hin2 : item_id c ∈ ({[item_id c]} ∪ ci) by set_solver.
    rewrite (IH c restfuel (S offset) leftIdx rightIdx oLeftId oRightId newId arr
               ({[item_id c]} ∪ idsBeforeOrigin) ({[item_id c]} ∪ ci) destIdx
               Hstep' Hlook' Hnl' Hin1 Hin2).
    have -> : (S offset + length tail')%nat = (offset + S (length tail'))%nat by lia.
    have -> : char_ids tail' ∪ ({[item_id c]} ∪ idsBeforeOrigin) = char_ids (c :: tail') ∪ idsBeforeOrigin
      by (rewrite char_ids_cons; set_solver).
    have -> : char_ids tail' ∪ ({[item_id c]} ∪ ci) = char_ids (c :: tail') ∪ ci
      by (rewrite char_ids_cons; set_solver).
    done.
Qed.

(** Tail cascade, MOVE flavor: with an empty conflicting set, every tail char
    repositions the destination one past itself. The destination tracks the
    cursor ([destIdx = leftIdx + offset]). *)
Lemma setfii_tail_move (tail : list (YjsItem A)) :
  forall (prev : YjsItem A) (restfuel offset : nat) (leftIdx rightIdx : Z)
    (oLeftId oRightId : option YjsId) (newId : YjsId)
    (arr : list (YjsItem A)) (idsBeforeOrigin : gset YjsId),
  run_step (prev :: tail) ->
  (forall k c, tail !! k = Some c ->
     arr !! (Z.to_nat (leftIdx + Z.of_nat (offset + k))) = Some c) ->
  (forall c, c ∈ prev :: tail -> Some (item_id c) ≠ oLeftId) ->
  item_id prev ∈ idsBeforeOrigin ->
  (0 <= leftIdx + Z.of_nat offset)%Z ->
  setfii_loop (length tail + restfuel) offset leftIdx rightIdx oLeftId oRightId newId arr
    idsBeforeOrigin ∅ (leftIdx + Z.of_nat offset)%Z
  = setfii_loop restfuel (offset + length tail)%nat leftIdx rightIdx oLeftId oRightId newId arr
      (char_ids tail ∪ idsBeforeOrigin) ∅ (leftIdx + Z.of_nat (offset + length tail))%Z.
Proof.
  induction tail as [|c tail' IH];
    intros prev restfuel offset leftIdx rightIdx oLeftId oRightId newId arr idsBeforeOrigin
      Hstep Hlook Hnotleft Hpibo Hpos.
  - simpl. rewrite Nat.add_0_r.
    have -> : char_ids [] ∪ idsBeforeOrigin = idsBeforeOrigin by set_solver.
    done.
  - simpl length. simpl plus.
    simpl setfii_loop.
    have Hc0 : arr !! Z.to_nat (leftIdx + Z.of_nat offset) = Some c.
    { have := Hlook 0%nat c eq_refl. rewrite Nat.add_0_r //. }
    rewrite Hc0 /=.
    have [Hor Hne] : origin_id (origin c) = Some (item_id prev) ∧
                     item_id prev ≠ item_id c
      := run_step_tail_origin (prev :: c :: tail') 0 prev c Hstep eq_refl eq_refl.
    have Hnl : origin_id (origin c) ≠ oLeftId.
    { rewrite Hor. apply Hnotleft. apply elem_of_cons. by left. }
    rewrite decide_False; last exact Hnl.
    rewrite Hor.
    rewrite decide_True; last first.
    { apply elem_of_union. right. exact Hpibo. }
    rewrite decide_True; last first.
    { move=> Hin. apply elem_of_union in Hin.
      destruct Hin as [Hin | Hin].
      - apply elem_of_singleton in Hin. exact (Hne Hin).
      - set_solver. }
    (* reposition one past [c] and recurse *)
    have Hidx : Z.of_nat (Z.to_nat (leftIdx + Z.of_nat offset) + 1)
              = (leftIdx + Z.of_nat (S offset))%Z by lia.
    rewrite Hidx.
    have Hstep' : run_step (c :: tail') := run_step_tail prev (c :: tail') Hstep.
    have Hlook' : forall k c0, tail' !! k = Some c0 ->
        arr !! Z.to_nat (leftIdx + Z.of_nat (S offset + k)) = Some c0.
    { move=> k c0 Hk. have := Hlook (S k) c0 Hk.
      have -> : (offset + S k)%nat = (S offset + k)%nat by lia.
      done. }
    have Hnl' : forall c0, c0 ∈ c :: tail' -> Some (item_id c0) ≠ oLeftId.
    { move=> c0 Hc0'. apply Hnotleft. apply elem_of_cons. right. exact Hc0'. }
    have Hin1 : item_id c ∈ ({[item_id c]} ∪ idsBeforeOrigin) by set_solver.
    have Hpos' : (0 <= leftIdx + Z.of_nat (S offset))%Z by lia.
    rewrite (IH c restfuel (S offset) leftIdx rightIdx oLeftId oRightId newId arr
               ({[item_id c]} ∪ idsBeforeOrigin) Hstep' Hlook' Hnl' Hin1 Hpos').
    have -> : (S offset + length tail')%nat = (offset + S (length tail'))%nat by lia.
    have -> : char_ids tail' ∪ ({[item_id c]} ∪ idsBeforeOrigin) = char_ids (c :: tail') ∪ idsBeforeOrigin
      by (rewrite char_ids_cons; set_solver).
    done.
Qed.

(** THE block step: one whole [run_step]-chained block of the scan window
    reduces to a single node-level decision made by its HEAD char, exactly as
    the node-stepping heap scan decides it (issue #28 M4). The four outcomes:
    move past the block (case 1 with a smaller client, or case 2 with the
    conflict's origin scanned but not conflicting), break (same integration
    points, or an origin before the window), or scan on (accumulators absorb
    the block). *)
Lemma setfii_block_step (h : YjsItem A) (tail : list (YjsItem A))
    (restfuel offset : nat) (leftIdx rightIdx : Z)
    (oLeftId oRightId : option YjsId) (newId : YjsId)
    (arr : list (YjsItem A)) (idsBeforeOrigin ci : gset YjsId) (destIdx : Z) :
  run_step (h :: tail) ->
  (forall k c, (h :: tail) !! k = Some c ->
     arr !! (Z.to_nat (leftIdx + Z.of_nat (offset + k))) = Some c) ->
  (forall c, c ∈ h :: tail -> Some (item_id c) ≠ oLeftId) ->
  (0 <= leftIdx + Z.of_nat offset)%Z ->
  setfii_loop (length (h :: tail) + restfuel) offset leftIdx rightIdx
    oLeftId oRightId newId arr idsBeforeOrigin ci destIdx
  = (if decide (origin_id (origin h) = oLeftId) then
       if decide (clientId (item_id h) < clientId newId)%nat then
         setfii_loop restfuel (offset + length (h :: tail))%nat leftIdx rightIdx
           oLeftId oRightId newId arr
           (char_ids (h :: tail) ∪ idsBeforeOrigin) ∅
           (leftIdx + Z.of_nat (offset + length (h :: tail)))%Z
       else if decide (origin_id (rightOrigin h) = oRightId) then Some destIdx
       else
         setfii_loop restfuel (offset + length (h :: tail))%nat leftIdx rightIdx
           oLeftId oRightId newId arr
           (char_ids (h :: tail) ∪ idsBeforeOrigin) (char_ids (h :: tail) ∪ ci) destIdx
     else
       match origin_id (origin h) with
       | Some col =>
         if decide (col ∈ ({[item_id h]} ∪ idsBeforeOrigin)) then
           if decide (col ∉ ({[item_id h]} ∪ ci)) then
             setfii_loop restfuel (offset + length (h :: tail))%nat leftIdx rightIdx
               oLeftId oRightId newId arr
               (char_ids (h :: tail) ∪ idsBeforeOrigin) ∅
               (leftIdx + Z.of_nat (offset + length (h :: tail)))%Z
           else
             setfii_loop restfuel (offset + length (h :: tail))%nat leftIdx rightIdx
               oLeftId oRightId newId arr
               (char_ids (h :: tail) ∪ idsBeforeOrigin) (char_ids (h :: tail) ∪ ci) destIdx
         else Some destIdx
       | None => Some destIdx
       end).
Proof.
  move=> Hstep Hlook Hnotleft Hpos.
  have Hh0 : arr !! Z.to_nat (leftIdx + Z.of_nat offset) = Some h.
  { have := Hlook 0%nat h eq_refl. rewrite Nat.add_0_r //. }
  have Hlook' : forall k c, tail !! k = Some c ->
      arr !! Z.to_nat (leftIdx + Z.of_nat (S offset + k)) = Some c.
  { move=> k c Hk. have := Hlook (S k) c Hk.
    have -> : (offset + S k)%nat = (S offset + k)%nat by lia.
    done. }
  have Hidx1 : Z.of_nat (Z.to_nat (leftIdx + Z.of_nat offset) + 1)
             = (leftIdx + Z.of_nat (S offset))%Z by lia.
  have Hin_ibo : item_id h ∈ ({[item_id h]} ∪ idsBeforeOrigin) by set_solver.
  have Hin_ci : item_id h ∈ ({[item_id h]} ∪ ci) by set_solver.
  have Hpos' : (0 <= leftIdx + Z.of_nat (S offset))%Z by lia.
  have Hlen : length (h :: tail) = S (length tail) by done.
  (* unfold the head step *)
  simpl setfii_loop. rewrite Hh0 /=.
  destruct (decide (origin_id (origin h) = oLeftId)) as [Hc1 | Hc1].
  - destruct (decide (clientId (item_id h) < clientId newId)%nat) as [Hcl | Hcl].
    + (* case 1, smaller client: move past the head, then the MOVE cascade *)
      rewrite Hidx1.
      rewrite (setfii_tail_move tail h restfuel (S offset) leftIdx rightIdx
                 oLeftId oRightId newId arr ({[item_id h]} ∪ idsBeforeOrigin)
                 Hstep Hlook' Hnotleft Hin_ibo Hpos').
      have -> : (S offset + length tail)%nat = (offset + length (h :: tail))%nat by (rewrite Hlen; lia).
      have -> : char_ids tail ∪ ({[item_id h]} ∪ idsBeforeOrigin) = char_ids (h :: tail) ∪ idsBeforeOrigin
        by (rewrite char_ids_cons; set_solver).
      done.
    + destruct (decide (origin_id (rightOrigin h) = oRightId)) as [Hro | Hro]; first done.
      (* case 1, scan on: the STAY cascade *)
      rewrite (setfii_tail_stay tail h restfuel (S offset) leftIdx rightIdx
                 oLeftId oRightId newId arr ({[item_id h]} ∪ idsBeforeOrigin) ({[item_id h]} ∪ ci) destIdx
                 Hstep Hlook' Hnotleft Hin_ibo Hin_ci).
      have -> : (S offset + length tail)%nat = (offset + length (h :: tail))%nat by (rewrite Hlen; lia).
      have -> : char_ids tail ∪ ({[item_id h]} ∪ idsBeforeOrigin) = char_ids (h :: tail) ∪ idsBeforeOrigin
        by (rewrite char_ids_cons; set_solver).
      have -> : char_ids tail ∪ ({[item_id h]} ∪ ci) = char_ids (h :: tail) ∪ ci
        by (rewrite char_ids_cons; set_solver).
      done.
  - destruct (origin_id (origin h)) as [col|] eqn:Hcol; last done.
    destruct (decide (col ∈ ({[item_id h]} ∪ idsBeforeOrigin))) as [Hmem | Hmem]; last done.
    destruct (decide (col ∉ ({[item_id h]} ∪ ci))) as [Hnot | Hnot].
    + (* case 2, move: MOVE cascade *)
      rewrite Hidx1.
      rewrite (setfii_tail_move tail h restfuel (S offset) leftIdx rightIdx
                 oLeftId oRightId newId arr ({[item_id h]} ∪ idsBeforeOrigin)
                 Hstep Hlook' Hnotleft Hin_ibo Hpos').
      have -> : (S offset + length tail)%nat = (offset + length (h :: tail))%nat by (rewrite Hlen; lia).
      have -> : char_ids tail ∪ ({[item_id h]} ∪ idsBeforeOrigin) = char_ids (h :: tail) ∪ idsBeforeOrigin
        by (rewrite char_ids_cons; set_solver).
      done.
    + (* case 2, stay: STAY cascade *)
      rewrite (setfii_tail_stay tail h restfuel (S offset) leftIdx rightIdx
                 oLeftId oRightId newId arr ({[item_id h]} ∪ idsBeforeOrigin) ({[item_id h]} ∪ ci) destIdx
                 Hstep Hlook' Hnotleft Hin_ibo Hin_ci).
      have -> : (S offset + length tail)%nat = (offset + length (h :: tail))%nat by (rewrite Hlen; lia).
      have -> : char_ids tail ∪ ({[item_id h]} ∪ idsBeforeOrigin) = char_ids (h :: tail) ∪ idsBeforeOrigin
        by (rewrite char_ids_cons; set_solver).
      have -> : char_ids tail ∪ ({[item_id h]} ∪ ci) = char_ids (h :: tail) ∪ ci
        by (rewrite char_ids_cons; set_solver).
      done.
Qed.

(* ===== block-query bridging (issue #28 M4, stage C1a) =====================
   The Go scan appends the WHOLE scanned run's id span to its sets before
   querying the conflict's left origin, so the heap test runs against
   [char_ids (h :: tail) ∪ X] while [setfii_block_step]'s decisions read
   [{[item_id h]} ∪ X] (the char-level accumulator at the head). The two
   agree because the queried id can never be a TAIL char of the very run
   being scanned: tail ids share the head's client with strictly larger
   clocks ([run_step]), and a head's same-client left origin has a strictly
   smaller clock (causal creation order; supplied by the caller as
   [Horiginclk], sourced from the store's origin-clock invariant). *)

(** Along a [run_step] chain, every tail char's id is the head's client with
    clock [clock h + k + 1]. *)
Lemma run_step_tail_ids (h : YjsItem A) (tail : list (YjsItem A)) :
  run_step (h :: tail) ->
  forall k y, tail !! k = Some y ->
    clientId (item_id y) = clientId (item_id h) ∧
    clock (item_id y) = (clock (item_id h) + k + 1)%nat.
Proof.
  intros Hstep k. revert h tail Hstep.
  induction k as [|k' IH]; intros h tail Hstep y Hk;
    (destruct tail as [|c tail']; first by rewrite lookup_nil in Hk).
  - injection Hk as <-.
    destruct (Hstep 0%nat h c eq_refl eq_refl) as (Hidc & _ & _).
    rewrite Hidc /=. split; [done | lia].
  - simpl in Hk.
    have Hstep' : run_step (c :: tail') := run_step_tail h (c :: tail') Hstep.
    destruct (IH c tail' Hstep' y Hk) as [Hcl Hck].
    destruct (Hstep 0%nat h c eq_refl eq_refl) as (Hidc & _ & _).
    rewrite Hcl Hck Hidc /=. split; [done | lia].
Qed.

(** The heap query against the block-absorbed set equals the pure query
    against the head-only set. *)
Lemma block_query_head (h : YjsItem A) (tail : list (YjsItem A))
    (col : YjsId) (X : gset YjsId) :
  run_step (h :: tail) ->
  (clientId col = clientId (item_id h) -> (clock col < S (clock (item_id h)))%nat) ->
  col ∈ char_ids (h :: tail) ∪ X <-> col ∈ ({[item_id h]} ∪ X : gset YjsId).
Proof.
  move=> Hstep Hclk.
  rewrite char_ids_cons.
  split.
  - move=> Hin. apply elem_of_union in Hin as [Hin | Hin]; last set_solver.
    apply elem_of_union in Hin as [Hin | Hin]; first set_solver.
    exfalso.
    apply elem_of_list_to_set, list_elem_of_fmap in Hin as (y & -> & Hy).
    apply list_elem_of_lookup_1 in Hy as [k Hk].
    destruct (run_step_tail_ids h tail Hstep k y Hk) as [Hcl Hck].
    have := Hclk Hcl. lia.
  - move=> Hin. apply elem_of_union in Hin as [Hin | Hin]; last set_solver.
    apply elem_of_union. left. apply elem_of_union. left. exact Hin.
Qed.

(* ===== the per-char ops of a multi-element wire item (issue #28 U7) ====== *)

(** [ops_from client clock originId rightOriginId chars]: the per-char ops of a run of [chars]
    minted by client [client] from clock [clock]: char [k] gets id [(client, clock + k)],
    the first op keeps the wire left origin [originId], each later op chains off
    the previous char, and every op shares the wire right origin [rightOriginId]
    (y-octo run semantics, the same shape [Text.Insert]'s loop mints). *)
Fixpoint ops_from (client clock : nat) (originId rightOriginId : option YjsId) (chars : list A) :
    list (IntegrateInput (A := A)) :=
  match chars with
  | [] => []
  | ch :: rest =>
      MkIntegrateInput originId rightOriginId ch (MkYjsId client clock)
        :: ops_from client (S clock) (Some (MkYjsId client clock)) rightOriginId rest
  end.

(** The ops a wire item [input] denotes when its content splits into
    [chars] (on the instantiated side, [explode] of the node's string). *)
Definition ops_of_input (input : IntegrateInput (A := A)) (chars : list A) :
    list (IntegrateInput (A := A)) :=
  ops_from (clientId (in_id input)) (clock (in_id input))
           (in_originId input) (in_rightOriginId input) chars.

Lemma ops_from_length client clock originId rightOriginId (chars : list A) :
  length (ops_from client clock originId rightOriginId chars) = length chars.
Proof.
  elim: chars client clock originId rightOriginId => [| ch chars IH] client clock originId rightOriginId; simpl; [done |].
  rewrite IH //.
Qed.

(** Per-op field facts, by position. *)
Lemma ops_from_lookup client clock originId rightOriginId (chars : list A) (k : nat)
    (op : IntegrateInput (A := A)) :
  ops_from client clock originId rightOriginId chars !! k = Some op ->
  in_id op = MkYjsId client (clock + k)%nat ∧
  in_rightOriginId op = rightOriginId ∧
  chars !! k = Some (in_content op) ∧
  (k = 0%nat -> in_originId op = originId) ∧
  (forall k', k = S k' -> in_originId op = Some (MkYjsId client (clock + k')%nat)).
Proof.
  elim: chars client clock originId rightOriginId k op => [| ch chars IH] client clock originId rightOriginId k op; simpl;
    first by rewrite lookup_nil.
  destruct k as [| k].
  - move=> [= <-]. simpl.
    split_and!; [by rewrite Nat.add_0_r | done | done | done | lia].
  - move=> Hk.
    destruct (IH client (S clock) (Some (MkYjsId client clock)) rightOriginId k op Hk)
      as (Hid & Hrid & Hch & Ho0 & Hos).
    split_and!.
    + rewrite Hid. f_equal. lia.
    + exact Hrid.
    + exact Hch.
    + lia.
    + move=> k' [= <-].
      destruct k as [| k2].
      * rewrite (Ho0 eq_refl). do 2 f_equal. lia.
      * rewrite (Hos k2 eq_refl). do 2 f_equal. lia.
Qed.

(** The whole run is [chained_after] whatever the head origin names. *)
Lemma ops_from_chained client clock (prev : YjsId) rightOriginId (chars : list A) :
  chained_after prev rightOriginId (ops_from client clock (Some prev) rightOriginId chars).
Proof.
  elim: chars clock prev => [| ch chars IH] clock prev; first done.
  simpl. split_and!; [done | done | exact (IH (S clock) (MkYjsId client clock))].
Qed.

(** The minted ids are pairwise distinct (consecutive clocks). *)
Lemma ops_from_ids_nodup client startClock originId rightOriginId (chars : list A) :
  NoDup (input_ids (ops_from client startClock originId rightOriginId chars)).
Proof.
  have Hgen : forall (l : list A) (ck0 : nat) (oid0 : option YjsId),
      NoDup (input_ids (ops_from client ck0 oid0 rightOriginId l)) ∧
      (forall idx inp, ops_from client ck0 oid0 rightOriginId l !! idx = Some inp ->
         (ck0 <= clock (in_id inp))%nat).
  { elim => [| ch l IHl] ck0 oid0.
    - split; [apply NoDup_nil; done | by move=> idx inp; rewrite lookup_nil].
    - destruct (IHl (S ck0) (Some (MkYjsId client ck0))) as [Hnd Hlb].
      split.
      + rewrite /input_ids fmap_cons. apply NoDup_cons. split; last exact Hnd.
        move=> Hin. apply list_elem_of_fmap in Hin as (inp & Heq & Hinp).
        apply list_elem_of_lookup_1 in Hinp as [idx Hidx].
        have Hle := Hlb idx inp Hidx.
        have Hck : clock (in_id inp) = ck0 by rewrite -Heq //.
        lia.
      + move=> idx inp. destruct idx as [| idx].
        * move=> [= <-]. simpl. lia.
        * move=> Hidx. have := Hlb idx inp Hidx. simpl. lia. }
  exact (proj1 (Hgen chars startClock originId)).
Qed.

(** The 1-char bridge: a single-char wire item denotes exactly itself, and
    the fold collapses to one step (what the pre-U7 callers integrate). *)
Lemma ops_of_input_singleton (input : IntegrateInput (A := A)) :
  ops_of_input input [in_content input] = [input].
Proof.
  rewrite /ops_of_input /=.
  destruct input as [o r c [client clock]] => //.
Qed.

Lemma integrate_all_singleton (i : IntegrateInput (A := A)) (arr : list (YjsItem A)) :
  integrate_all [i] arr = integrate i arr.
Proof. simpl. destruct (integrate i arr) => //. Qed.

(** [toItem] resolves only the origins (id / content are copied through), so two
    inputs sharing both origin ids resolve to the same pointers. This bridges a
    wire item to its per-char head op (issue #28 U7c): they share origins and
    id, differing only in content. *)
Lemma toItem_content_swap (a b : IntegrateInput (A := A))
    (arr : list (YjsItem A)) (ita : YjsItem A) :
  in_originId a = in_originId b ->
  in_rightOriginId a = in_rightOriginId b ->
  toItem a arr = Some ita ->
  toItem b arr = Some (Item (origin ita) (rightOrigin ita) (in_id b) (in_content b)).
Proof.
  rewrite /toItem => Ho Hr. rewrite -Ho -Hr.
  case: (match in_originId a with
         | Some id => itemPtr <$> find_by_id id arr | None => Some First end) => [optr|] //=.
  case: (match in_rightOriginId a with
         | Some id => itemPtr <$> find_by_id id arr | None => Some Last end) => [rptr|] //=.
  by move=> [<-].
Qed.

(** [maximalId] reads only the item's id, so it transfers along equal ids
    (issue #28 U7c: the wire item's head op shares its id). *)
Lemma maximalId_id_irrel (a b : YjsItem A) (arr : list (YjsItem A)) :
  item_id a = item_id b -> maximalId a arr -> maximalId b arr.
Proof.
  rewrite /maximalId => Hid Hm x Hx Hcc.
  rewrite -Hid. apply Hm; [exact Hx | rewrite Hid; exact Hcc].
Qed.

(** Insert-at variants of the splice shifts: the HEAD of a run lands at an
    arbitrary scan position [d] (take d ++ new :: drop d), not after an
    anchor, so the right-origin index and pointer shift under that form
    (issue #28 U7). *)
Lemma findRightIdx_insert_shift arr (d : nat) (newit : YjsItem A)
    (rightOriginId : option YjsId) (rightIdx : Z) :
  (d <= length arr)%nat ->
  (Z.of_nat d <= rightIdx)%Z ->
  findRightIdx rightOriginId arr = Some rightIdx ->
  (forall z, z ∈ arr -> item_id z ≠ item_id newit) ->
  findRightIdx rightOriginId (take d arr ++ newit :: drop d arr) = Some (rightIdx + 1)%Z.
Proof.
  move=> Hd Hdr Hri Hfresh.
  move: Hri. rewrite /findRightIdx.
  destruct rightOriginId as [r_id|]; last first.
  { move=> [= <-]. rewrite length_app /= length_take length_drop. f_equal. lia. }
  destruct (list_find (fun it => item_id it = r_id) arr) as [[k R]|] eqn:Hfind; last done.
  move=> [= HrIdx].
  apply list_find_Some in Hfind. destruct Hfind as (Hk & HidR & Hfirst).
  have Hkarr : (k < length arr)%nat by (apply lookup_lt_Some in Hk).
  have Hdk : (d <= k)%nat by lia.
  have Hfind' : list_find (fun it => item_id it = r_id)
                  (take d arr ++ newit :: drop d arr) = Some (S k, R).
  { apply list_find_Some. split_and!.
    - rewrite lookup_app_r; last (rewrite length_take; lia).
      rewrite length_take Nat.min_l; last lia.
      have -> : (S k - d)%nat = S (k - d)%nat by lia.
      rewrite /= lookup_drop.
      have -> : (d + (k - d))%nat = k by lia.
      exact Hk.
    - exact HidR.
    - move=> i y Hlook Hilt.
      destruct (decide (i < d)%nat) as [Hid2 | Hid2].
      + rewrite lookup_app_l in Hlook; last (rewrite length_take; lia).
        rewrite lookup_take_lt in Hlook; last lia.
        apply (Hfirst i y Hlook). lia.
      + rewrite lookup_app_r in Hlook; last (rewrite length_take; lia).
        rewrite length_take Nat.min_l in Hlook; last lia.
        destruct (decide (i = d)) as [-> | Hne].
        * rewrite Nat.sub_diag /= in Hlook.
          injection Hlook as <-.
          move=> HidN.
          have HRin : R ∈ arr := list_elem_of_lookup_2 _ _ _ Hk.
          exact (Hfresh R HRin (eq_trans HidR (eq_sym HidN))).
        * have Hsub : (i - d)%nat = S (i - d - 1)%nat by lia.
          rewrite Hsub /= lookup_drop in Hlook.
          apply (Hfirst (d + (i - d - 1))%nat y Hlook). lia. }
  rewrite Hfind' /=. f_equal. lia.
Qed.

Lemma getPtrExcept_insert_shift arr (d : nat) (newit : YjsItem A)
    (rightIdx : Z) (rptr : YjsPtr A) :
  (d <= length arr)%nat ->
  (Z.of_nat d <= rightIdx)%Z ->
  getPtrExcept arr rightIdx = Some rptr ->
  getPtrExcept (take d arr ++ newit :: drop d arr) (rightIdx + 1) = Some rptr.
Proof.
  move=> Hd Hdr.
  rewrite /getPtrExcept.
  have Hlen1 : length (take d arr ++ newit :: drop d arr) = S (length arr)
    by (rewrite length_app /= length_take length_drop; lia).
  destruct (decide (rightIdx = -1)%Z) as [-> | Hne1]; first lia.
  destruct (decide (rightIdx = Z.of_nat (length arr))%Z) as [-> | Hne2].
  - move=> [= <-].
    rewrite decide_False; last lia.
    rewrite decide_True; last (rewrite Hlen1; lia).
    done.
  - move=> Hlook.
    rewrite decide_False; last lia.
    rewrite decide_False; last (rewrite Hlen1; lia).
    have Hrn : (Z.to_nat rightIdx < length arr)%nat.
    { destruct (arr !! Z.to_nat rightIdx) eqn:Hx; last done.
      apply lookup_lt_Some in Hx. exact Hx. }
    rewrite -Hlook.
    have -> : Z.to_nat (rightIdx + 1) = S (Z.to_nat rightIdx) by lia.
    f_equal.
    rewrite lookup_app_r; last (rewrite length_take; lia).
    rewrite length_take Nat.min_l; last lia.
    have -> : (S (Z.to_nat rightIdx) - d)%nat = S (Z.to_nat rightIdx - d)%nat by lia.
    rewrite /= lookup_drop.
    f_equal. lia.
Qed.

End run_theory.
