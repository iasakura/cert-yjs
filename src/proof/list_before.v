(** The position order on lists, free of Cert-Yjs definitions.

    [list_before l x y] says [x] occurs at a strictly smaller position than
    [y] in [l]. Under [NoDup l] positions are unique, so on the members of
    [l] it is a strict order (transitive, irreflexive, asymmetric); the laws
    below take that hypothesis where they need it. It passes through [cons]
    and the head, through a split point ([list_before_split] /
    [list_before_split_r]), through prefixes ([list_before_prefix] and, for
    members of the prefix, [list_before_prefix_inv]) and through [filter]
    ([list_before_filter] and, for members of the filtered list,
    [list_before_filter_inv]); a list whose numeric measure strictly grows
    along positions orders its members by that measure
    ([list_before_of_measure]); the reflexive-transitive closure of a relation
    whose every edge points forward in [l] points forward in [l] up to
    equality ([rtc_list_before]); and in a list with duplicate-free images
    under a function, members are determined by their image
    ([NoDup_fmap_elem_of_eq]).

    Its one user is [network_convergence], which ranks the structural
    dependency order of a delivered set by a replica's delivery order. Pure
    stdpp; iterate on this file alone. *)
From stdpp Require Import base list relations.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.

(** [list_before l x y]: [x] occurs strictly before [y] in [l] (at some pair
    of positions). Under [NoDup l] positions are unique, so on the members
    of [l] this is a strict total order; the laws below are stated under
    that hypothesis where they need it. *)
Definition list_before {X : Type} (l : list X) (x y : X) : Prop :=
  ∃ i j : nat, l !! i = Some x ∧ l !! j = Some y ∧ (i < j)%nat.

Lemma list_before_elem_of_l {X : Type} (l : list X) (x y : X) :
  list_before l x y -> x ∈ l.
Proof. move=> [i [j [Hi [_ _]]]]. exact (list_elem_of_lookup_2 _ _ _ Hi). Qed.

Lemma list_before_elem_of_r {X : Type} (l : list X) (x y : X) :
  list_before l x y -> y ∈ l.
Proof. move=> [i [j [_ [Hj _]]]]. exact (list_elem_of_lookup_2 _ _ _ Hj). Qed.

Lemma list_before_trans {X : Type} (l : list X) (x y z : X) :
  NoDup l -> list_before l x y -> list_before l y z -> list_before l x z.
Proof.
  move=> Hnd [i [j [Hi [Hj Hij]]]] [j' [k [Hj' [Hk Hjk]]]].
  have Heq : j = j' := NoDup_lookup l j j' y Hnd Hj Hj'.
  exists i, k. split_and!; [exact Hi | exact Hk | lia].
Qed.

Lemma list_before_irrefl {X : Type} (l : list X) (x : X) :
  NoDup l -> ¬ list_before l x x.
Proof.
  move=> Hnd [i [j [Hi [Hj Hij]]]].
  have Heq : i = j := NoDup_lookup l i j x Hnd Hi Hj. lia.
Qed.

Lemma list_before_asymm {X : Type} (l : list X) (x y : X) :
  NoDup l -> list_before l x y -> list_before l y x -> False.
Proof.
  move=> Hnd Hxy Hyx.
  exact (list_before_irrefl l x Hnd (list_before_trans l x y x Hnd Hxy Hyx)).
Qed.

Lemma list_before_cons {X : Type} (l : list X) (a x y : X) :
  list_before l x y -> list_before (a :: l) x y.
Proof.
  move=> [i [j [Hi [Hj Hij]]]]. exists (S i), (S j). split_and!; [done | done | lia].
Qed.

Lemma list_before_cons_head {X : Type} (l : list X) (a y : X) :
  y ∈ l -> list_before (a :: l) a y.
Proof.
  move=> Hy. destruct (list_elem_of_lookup_1 _ _ Hy) as [j Hj].
  exists 0%nat, (S j). split_and!; [done | done | lia].
Qed.

(** Nothing is before the head. *)
Lemma list_before_head {X : Type} (l : list X) (a b : X) :
  NoDup (a :: l) -> ¬ list_before (a :: l) b a.
Proof.
  move=> Hnd [i [j [Hi [Hj Hij]]]].
  have Heq : j = 0%nat := NoDup_lookup (a :: l) j 0 a Hnd Hj eq_refl. lia.
Qed.

(** What is before a split point sits in the prefix. *)
Lemma list_before_split {X : Type} (l l1 l2 : list X) (a b : X) :
  NoDup l -> l = l1 ++ a :: l2 -> list_before l b a -> b ∈ l1.
Proof.
  move=> Hnd Hsplit [i [j [Hi [Hj Hij]]]].
  have Hja : l !! length l1 = Some a by rewrite Hsplit list_lookup_middle //.
  have Heq : j = length l1 := NoDup_lookup l j (length l1) a Hnd Hj Hja.
  subst j. rewrite Hsplit lookup_app_l // in Hi.
  exact (list_elem_of_lookup_2 _ _ _ Hi).
Qed.

(** The split point is before everything after it. *)
Lemma list_before_split_r {X : Type} (l l1 l2 : list X) (a b : X) :
  l = l1 ++ a :: l2 -> b ∈ l2 -> list_before l a b.
Proof.
  move=> Hsplit Hb. destruct (list_elem_of_lookup_1 _ _ Hb) as [i Hi].
  exists (length l1), (length l1 + S i)%nat. split_and!.
  - rewrite Hsplit list_lookup_middle //.
  - rewrite Hsplit lookup_app_r; last lia.
    replace (length l1 + S i - length l1)%nat with (S i) by lia. exact Hi.
  - lia.
Qed.

(** Order in a prefix is order in the list, and conversely for members of the
    prefix. *)
Lemma list_before_prefix {X : Type} (l0 l : list X) (x y : X) :
  l0 `prefix_of` l -> list_before l0 x y -> list_before l x y.
Proof.
  move=> [rest ->] [i [j [Hi [Hj Hij]]]].
  exists i, j. split_and!; [| | exact Hij].
  - rewrite lookup_app_l //. exact (lookup_lt_Some _ _ _ Hi).
  - rewrite lookup_app_l //. exact (lookup_lt_Some _ _ _ Hj).
Qed.

Lemma list_before_prefix_inv {X : Type} (l0 l : list X) (x y : X) :
  NoDup l -> l0 `prefix_of` l -> x ∈ l0 -> y ∈ l0 ->
  list_before l x y -> list_before l0 x y.
Proof.
  move=> Hnd [rest Hl] Hx Hy [i [j [Hi [Hj Hij]]]].
  destruct (list_elem_of_lookup_1 _ _ Hx) as (i0 & Hi0).
  destruct (list_elem_of_lookup_1 _ _ Hy) as (j0 & Hj0).
  have Hi0' : l !! i0 = Some x.
  { rewrite Hl lookup_app_l //. exact (lookup_lt_Some _ _ _ Hi0). }
  have Hj0' : l !! j0 = Some y.
  { rewrite Hl lookup_app_l //. exact (lookup_lt_Some _ _ _ Hj0). }
  have Heqi : i0 = i := NoDup_lookup l i0 i x Hnd Hi0' Hi.
  have Heqj : j0 = j := NoDup_lookup l j0 j y Hnd Hj0' Hj.
  exists i0, j0. split_and!; [exact Hi0 | exact Hj0 | lia].
Qed.

(** Order in a filtered list is order in the list. *)
Lemma list_before_filter {X : Type} (Pf : X -> Prop) `{∀ x, Decision (Pf x)}
    (l : list X) (x y : X) :
  list_before (filter Pf l) x y -> list_before l x y.
Proof.
  elim: l => [| a l IH].
  { move=> [i [j [Hi [_ _]]]]. rewrite lookup_nil // in Hi. }
  rewrite filter_cons. case_decide as Ha.
  - move=> [i [j [Hi [Hj Hij]]]].
    destruct i as [| i]; destruct j as [| j]; simpl in Hi, Hj; try lia.
    + injection Hi as ->.
      apply list_before_cons_head.
      have Hyf : y ∈ filter Pf l := list_elem_of_lookup_2 _ _ _ Hj.
      apply list_elem_of_filter in Hyf. exact (proj2 Hyf).
    + apply list_before_cons. apply IH. exists i, j. split_and!; [done | done | lia].
  - move=> Hb. apply list_before_cons. exact (IH Hb).
Qed.

(** Conversely, members of the filtered list keep their order from the list
    (positions are unique under [NoDup]). *)
Lemma list_before_filter_inv {X : Type} (Pf : X -> Prop) `{∀ x, Decision (Pf x)}
    (l : list X) (x y : X) :
  NoDup l -> x ∈ filter Pf l -> y ∈ filter Pf l ->
  list_before l x y -> list_before (filter Pf l) x y.
Proof.
  elim: l => [| a l IH].
  { move=> _ _ _ [i [j [Hi _]]]. rewrite lookup_nil // in Hi. }
  move=> Hnd Hx Hy [i [j [Hi [Hj Hij]]]].
  apply NoDup_cons in Hnd as [Hnotin Hnd].
  destruct i as [| i]; destruct j as [| j]; simpl in Hi, Hj; try lia.
  - (* [x] is the head *)
    injection Hi as <-.
    have Hyl : y ∈ l := list_elem_of_lookup_2 _ _ _ Hj.
    have Hpa : Pf a.
    { apply list_elem_of_filter in Hx. exact (proj1 Hx). }
    rewrite filter_cons decide_True //.
    apply list_before_cons_head.
    apply list_elem_of_filter. split; [| exact Hyl].
    apply list_elem_of_filter in Hy as [HPy Hy].
    exact HPy.
  - (* both in the tail *)
    have Hxl : x ∈ l := list_elem_of_lookup_2 _ _ _ Hi.
    have Hyl : y ∈ l := list_elem_of_lookup_2 _ _ _ Hj.
    have Hxf : x ∈ filter Pf l.
    { apply list_elem_of_filter. apply list_elem_of_filter in Hx. split; [exact (proj1 Hx) | exact Hxl]. }
    have Hyf : y ∈ filter Pf l.
    { apply list_elem_of_filter. apply list_elem_of_filter in Hy. split; [exact (proj1 Hy) | exact Hyl]. }
    have Hb : list_before (filter Pf l) x y.
    { apply IH; [exact Hnd | exact Hxf | exact Hyf |]. exists i, j. split_and!; [done | done | lia]. }
    rewrite filter_cons. case_decide; [apply list_before_cons; exact Hb | exact Hb].
Qed.

(** A list whose measure strictly grows along positions orders its members
    by the measure. *)
Lemma list_before_of_measure {X : Type} (f : X -> nat) (l : list X) (x y : X) :
  (∀ (i j : nat) (a b : X), (i < j)%nat -> l !! i = Some a -> l !! j = Some b ->
     (f a < f b)%nat) ->
  x ∈ l -> y ∈ l -> (f x < f y)%nat -> list_before l x y.
Proof.
  move=> Hmono Hx Hy Hlt.
  destruct (list_elem_of_lookup_1 _ _ Hx) as (i & Hi).
  destruct (list_elem_of_lookup_1 _ _ Hy) as (j & Hj).
  destruct (Nat.lt_trichotomy i j) as [Hij | [Hij | Hij]].
  - by exists i, j.
  - subst j. rewrite Hi in Hj. injection Hj as ->. lia.
  - have := Hmono j i y x Hij Hj Hi. lia.
Qed.

(** The reflexive-transitive closure of an order-respecting relation respects
    the order, up to equality. *)
Lemma rtc_list_before {X : Type} (R : relation X) (l : list X) (x y : X) :
  NoDup l ->
  (∀ a b, R a b -> list_before l a b) ->
  rtc R x y -> x = y ∨ list_before l x y.
Proof.
  move=> Hnd HR. induction 1 as [z | a b c Hab Hbc IH]; first by left.
  right. destruct IH as [-> | Hbc'].
  - exact (HR a c Hab).
  - exact (list_before_trans l a b c Hnd (HR a b Hab) Hbc').
Qed.

(** Members of a list with duplicate-free images are determined by their
    image. *)
Lemma NoDup_fmap_elem_of_eq {X Y : Type} (f : X -> Y) (l : list X) (x y : X) :
  NoDup (f <$> l) -> x ∈ l -> y ∈ l -> f x = f y -> x = y.
Proof.
  move=> Hnd Hx Hy Hf.
  destruct (list_elem_of_lookup_1 _ _ Hx) as (i & Hi).
  destruct (list_elem_of_lookup_1 _ _ Hy) as (j & Hj).
  have Hfi : (f <$> l) !! i = Some (f x) by rewrite list_lookup_fmap Hi //.
  have Hfj : (f <$> l) !! j = Some (f x) by rewrite list_lookup_fmap Hj Hf //.
  have Heq : i = j := NoDup_lookup _ i j (f x) Hnd Hfi Hfj.
  subst j. rewrite Hi in Hj. by injection Hj.
Qed.
