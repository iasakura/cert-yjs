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
From stdpp Require Import base numbers list sorting.
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
    destruct (findPtrIdx_closed arr (origin other) Hinv Hoclosed) as (oL & HoL & HoLb).
    rewrite HoL /=.
    have Horclosed : ∀ z : YjsItem A, rightOrigin other = itemPtr z -> z ∈ arr.
    { have Hclosed := yai_closed _ Hinv.
      move=> z Heq.
      destruct other as [o r id c]. simpl in Heq. subst r.
      exact (closedRight _ Hclosed _ _ _ _ Hoin). }
    destruct (findPtrIdx_closed arr (rightOrigin other) Hinv Horclosed) as (oR & HoR & HoRb).
    rewrite HoR /=.
    (* origin other sits strictly left of S j ... *)
    have Hlt : YjsLt' (origin other) (itemPtr other).
    { destruct other as [o r id c]. exists 1%nat. simpl.
      apply (ltOrigin 0). apply leqSame. }
    have HotherIdx : findPtrIdx (itemPtr other) arr = Some (Z.of_nat (S j))
      := findPtrIdx_item arr (S j) other (yai_unique _ Hinv) Hother.
    have HoLlt : (oL < Z.of_nat (S j))%Z.
    { exact (findptridx_order2.YjsLt'_findPtrIdx_lt arr (origin other) (itemPtr other)
               oL (Z.of_nat (S j)) Hinv
               ltac:(exact (findptridx_getelem.findPtrIdx_ArrSet arr _ oL HoL))
               ltac:(exact (findptridx_getelem.findPtrIdx_ArrSet arr _ (Z.of_nat (S j)) HotherIdx))
               Hlt HoL HotherIdx). }
    (* ... and not AT j (no successor), so strictly below j: the loop exits *)
    have HoLne : oL <> Z.of_nat j.
    { move=> HoLj. subst oL.
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
    destruct (in_rightOriginId input) as [rid|].
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

End run_theory.
