(** General Iris resource-algebra laws the Cert-Yjs proofs use.

    They live here rather than in a type's [heap.v] because they say nothing
    about any of our definitions: growth, lookup and fragment minting for an
    [auth (gmap K (gset V))] (the per-type item sets), the same for an
    [auth (gset YjsId)] (the accepted-id set), a grow-and-persist step for a
    [ghost_map] (the root-type registry), and replication laws for [tok_set]
    token bundles (the reader capabilities).

    List facts free of Cert-Yjs definitions: [fmap_concat], [list_elem_of_concat],
    [concat_fmap], [list_filter_fmap], [list_filter_iff_elem_of],
    [StronglySorted_fmap_elem_of], [map_to_list_insert_existing],
    [concat_perm], [elem_of_list_insert_inv] (membership in a list with one
    slot replaced), [map_to_list_fst_perm] (two maps with the same domain
    list the same keys). Positions: [list_before] (strictly earlier in a
    list) with its order laws under [NoDup], [list_before_filter] /
    [list_before_prefix] / [list_before_of_measure], [rtc_list_before] (a
    closure of forward edges points forward), [NoDup_fmap_elem_of_eq]. Map
    big-op:
    [big_sepM_map_imap_total], a big-op over a total [map_imap] is the
    big-op over the underlying map. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.proof Require Import core.
From New.proof Require Import tok_set.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.

(** Updating an existing key's value reshuffles [map_to_list] only at that key. *)
Lemma map_to_list_insert_existing {V : Type} (m : gmap loc V) (k : loc) (v v' : V) :
  m !! k = Some v ->
  map_to_list (<[k:=v']> m) ≡ₚ (k, v') :: map_to_list (delete k m).
Proof.
  move=> Hk.
  pose proof (map_to_list_delete (<[k:=v']> m) k v' (lookup_insert_eq m k v')) as Hp.
  rewrite delete_insert_eq in Hp. symmetry. exact Hp.
Qed.

(** [concat] respects permutation of the outer list. *)
Lemma concat_perm {D : Type} (ll1 ll2 : list (list D)) :
  ll1 ≡ₚ ll2 -> concat ll1 ≡ₚ concat ll2.
Proof.
  induction 1; simpl.
  - reflexivity.
  - apply Permutation_app_head. exact IHPermutation.
  - rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - etrans; eassumption.
Qed.

(** Membership in a concatenation: some member list holds the element. *)
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

(* A generic [ghost_map] grow-and-persist step, in its own section so it depends
   only on a [ghost_mapG] instance (issue #54): the certificate proof in
   [store/applyUpdate], whose section lacks the store's [seq_inG] / [ftypes_inG],
   reconciles the registry map with the concrete one after [applyUpdate]'s drain
   creates fresh root types, minting one persistent binding per new name. *)
(** [fmap] pushes through [concat]. *)
Lemma concat_fmap {X Y : Type} (f : X -> Y) (l : list (list X)) :
  fmap (M := list) f (concat l)
  = concat (fmap (M := list) (λ xs, fmap (M := list) f xs) l).
Proof.
  induction l as [| x l IH]; simpl; [done |].
  rewrite fmap_app IH //.
Qed.

(** [filter] commutes with [fmap] (the predicate pulled back along the
    function). *)
Lemma list_filter_fmap {X Y : Type} (f : X -> Y) (P : Y -> Prop)
    `{!∀ y, Decision (P y)} (l : list X) :
  filter P (f <$> l) = f <$> filter (λ x, P (f x)) l.
Proof.
  induction l as [| x l IH]; [done |].
  csimpl. rewrite !filter_cons.
  repeat case_decide; csimpl; rewrite ?IH; first [done | tauto].
Qed.

(** [list_filter_iff] with the equivalence only on members. *)
Lemma list_filter_iff_elem_of {X : Type} (P1 P2 : X -> Prop)
    `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} (l : list X) :
  (∀ x, x ∈ l -> (P1 x ↔ P2 x)) ->
  filter P1 l = filter P2 l.
Proof.
  induction l as [| x l IH]; [done |].
  move=> Hiff. rewrite !filter_cons.
  have Hx : P1 x ↔ P2 x by (apply Hiff; apply elem_of_cons; by left).
  have Hrest : filter P1 l = filter P2 l
    by (apply IH; move=> y Hy; apply Hiff; apply elem_of_cons; by right).
  repeat case_decide; rewrite Hrest; first [done | tauto].
Qed.

(** [StronglySorted_fmap] with the order implication only on members. *)
Lemma StronglySorted_fmap_elem_of {X Y : Type} (R1 : relation X) (R2 : relation Y)
    (f : X -> Y) (l : list X) :
  (∀ x y, x ∈ l -> y ∈ l -> R1 x y -> R2 (f x) (f y)) ->
  StronglySorted R1 l -> StronglySorted R2 (f <$> l).
Proof.
  intros Himp Hss. induction Hss as [| x l Hss IH Hall]; csimpl; constructor.
  - apply IH. intros a b Ha Hb. apply Himp; apply elem_of_cons; by right.
  - rewrite Forall_fmap. apply Forall_forall. intros a Ha. simpl.
    apply Himp; [apply elem_of_cons; by left | apply elem_of_cons; by right |].
    rewrite Forall_forall in Hall. by apply Hall.
Qed.


(** Membership in a list with one slot replaced: the new element, or an
    element of the old list. *)
Lemma elem_of_list_insert_inv {X : Type} (l : list X) (k : nat) (x y : X) :
  y ∈ <[k := x]> l -> y = x ∨ y ∈ l.
Proof.
  destruct (decide (k < length l)%nat) as [Hk | Hk].
  - rewrite insert_take_drop; last exact Hk.
    rewrite elem_of_app elem_of_cons.
    move=> [Hy | [Hy | Hy]].
    + right. apply list_elem_of_lookup in Hy as (i & Hi).
      apply lookup_take_Some in Hi as [Hi _]. apply list_elem_of_lookup. eauto.
    + left. exact Hy.
    + right. apply list_elem_of_lookup in Hy as (i & Hi).
      rewrite lookup_drop in Hi. apply list_elem_of_lookup. eauto.
  - rewrite list_insert_ge; last lia. move=> Hy. right. exact Hy.
Qed.

(* ===== positions in a list ================================================ *)

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

Section ghost_map_grow.
Context {Σ : gFunctors} {K V : Type} `{Countable K} `{ghost_mapG Σ K V}.
Lemma ghost_map_grow_persist (γ : gname) (m m' : gmap K V) :
  m ⊆ m' ->
  ghost_map_auth γ 1 m -∗
  ([∗ map] k ↦ v ∈ m, k ↪[γ]□ v) ==∗
  ghost_map_auth γ 1 m' ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ]□ v).
Proof.
  iIntros (Hsub) "Hauth #Hbinds".
  have Hdisj : (m' ∖ m) ##ₘ m.
  { apply map_disjoint_difference_l1. reflexivity. }
  have Hunion : (m' ∖ m) ∪ m = m'.
  { rewrite map_union_comm; last exact Hdisj. exact (map_difference_union _ _ Hsub). }
  iMod (ghost_map_insert_persist_big (m' ∖ m) with "Hauth") as "[Hauth #Hd]";
    first exact Hdisj.
  iEval (rewrite Hunion) in "Hauth".
  iModIntro. iFrame "Hauth".
  iApply big_sepM_intro. iIntros "!#" (k v Hkv).
  destruct (m !! k) as [v0|] eqn:Hb.
  - have Hv0 : v0 = v.
    { have Hw : m' !! k = Some v0 := lookup_weaken _ _ _ _ Hb Hsub.
      rewrite Hkv in Hw. by injection Hw. }
    subst v0. iApply (big_sepM_lookup with "Hbinds"). exact Hb.
  - iApply (big_sepM_lookup with "Hd").
    apply lookup_difference_Some. split; [exact Hkv | exact Hb].
Qed.
End ghost_map_grow.

Section auth_gmap_gset.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.


(* ===== lemmas ============================================================= *)

(* ----- ghost lemmas for the [auth (gmap K (gset V))] item-set RA --------- *)

(** A fragment [◯ {[k := S]}] combined with the authority [● m] both WITNESSES
    the key ([m !! k = Some S']) AND bounds it ([S ⊆ S']). This is what makes
    [is_type_lb] prove the type is registered and give a lower bound. *)
Lemma auth_gmap_gset_lookup {K V : Type} `{Countable K} `{Countable V}
    `{!inG Σ (authR (gmapUR K (gsetUR V)))} (γ : gname) (m : gmap K (gset V)) (k : K) (S : gset V) :
  own γ (● m) -∗ own γ (◯ {[k := S]}) -∗ ⌜∃ S', m !! k = Some S' ∧ S ⊆ S'⌝.
Proof.
  iIntros "Ha Hf".
  iDestruct (own_valid_2 with "Ha Hf") as %Hv.
  iPureIntro.
  apply auth_both_valid_discrete in Hv as [Hincl _].
  apply singleton_included_l in Hincl as [S' [Hlk Hsub]].
  exists S'.
  apply leibniz_equiv in Hlk.
  rewrite Some_included_total in Hsub.
  rewrite gset_included in Hsub.
  split; assumption.
Qed.


(** Fractional variant of [auth_gmap_gset_lookup]: a reader holding a [dq]-share
    of the authority ([●{dq} m], a reader's share of the store) can still learn membership
    and the lower bound. Used by the concurrent read API (Text.Len). *)
Lemma auth_gmap_gset_lookup_dq {K V : Type} `{Countable K} `{Countable V}
    `{!inG Σ (authR (gmapUR K (gsetUR V)))} (γ : gname) (dq : dfrac) (m : gmap K (gset V)) (k : K) (S : gset V) :
  own γ (●{dq} m) -∗ own γ (◯ {[k := S]}) -∗ ⌜∃ S', m !! k = Some S' ∧ S ⊆ S'⌝.
Proof.
  iIntros "Ha Hf".
  iDestruct (own_valid_2 with "Ha Hf") as %Hv.
  iPureIntro.
  apply auth_both_dfrac_valid_discrete in Hv as [_ [Hincl _]].
  apply singleton_included_l in Hincl as [S' [Hlk Hsub]].
  exists S'.
  apply leibniz_equiv in Hlk.
  rewrite Some_included_total in Hsub.
  rewrite gset_included in Hsub.
  split; assumption.
Qed.


(** Grow the set at [k] (from [Sold] to [Snew ⊇ Sold]) in the authority and mint
    the matching fragment [◯ {[k := Snew]}] (= the new [is_type_lb]). *)
Lemma auth_gmap_gset_grow {K V : Type} `{Countable K} `{Countable V}
    `{!inG Σ (authR (gmapUR K (gsetUR V)))} (γ : gname) (m : gmap K (gset V)) (k : K) (Sold Snew : gset V) :
  m !! k = Some Sold -> Sold ⊆ Snew ->
  own γ (● m) ==∗ own γ (● (<[k:=Snew]> m)) ∗ own γ (◯ {[k := Snew]}).
Proof.
  iIntros (Hk Hsub) "Ha".
  iMod (own_update _ _ (● (<[k:=Snew]> m) ⋅ ◯ {[k := Snew]}) with "Ha") as "H".
  { apply auth_update_alloc.
    apply local_update_unital_discrete. intros z Hvm Hz.
    rewrite left_id in Hz. rewrite -Hz. split.
    - by apply insert_valid.
    - intros i. rewrite lookup_op.
      destruct (decide (i = k)) as [->|Hne].
      + rewrite lookup_insert lookup_singleton Hk.
        destruct (decide (k = k)); last done.
        rewrite -Some_op. f_equiv. rewrite gset_op. set_solver.
      + rewrite lookup_insert_ne // lookup_singleton_ne // left_id //. }
  iModIntro. iDestruct "H" as "[$ $]".
Qed.


(** Batch variant of [auth_gmap_gset_grow]: grow EVERY key's set at once
    (pointwise [⊆]) and mint a persistent whole-map snapshot fragment, out of
    which each key's [◯ {[k := S]}] projects ([auth_gmap_gset_frag_lookup]).
    Used by [applyUpdate], which grows many types in one batch. The domain may
    also GROW ([dom m ⊆ dom m']): [getOrCreateYType]'s miss branch registers a
    fresh type mid-batch (issue #54), so [m'] can carry keys absent from [m]
    (their fresh fragment is minted here); only the surviving keys must not
    shrink. *)
Lemma auth_gmap_gset_grow_snap {K V : Type} `{Countable K} `{Countable V}
    `{!inG Σ (authR (gmapUR K (gsetUR V)))} (γ : gname) (m m' : gmap K (gset V)) :
  dom m ⊆ dom m' ->
  (∀ k S S', m !! k = Some S -> m' !! k = Some S' -> S ⊆ S') ->
  own γ (● m) ==∗ own γ (● m') ∗ own γ (◯ m').
Proof.
  iIntros (Hdom Hsub) "Ha".
  iMod (own_update _ _ (● m' ⋅ ◯ m') with "Ha") as "H".
  { apply auth_update_alloc.
    apply local_update_unital_discrete. intros z Hvm Hz.
    rewrite left_id in Hz. rewrite -Hz. split.
    - intros k. destruct (m' !! k) eqn:Hk; rewrite Hk //.
    - intros k. rewrite lookup_op.
      destruct (m !! k) as [S|] eqn:Hmk; destruct (m' !! k) as [S'|] eqn:Hm'k.
      + rewrite Hmk Hm'k -Some_op. f_equiv. rewrite gset_op.
        pose proof (Hsub k S S' Hmk Hm'k). set_solver.
      + exfalso. apply (elem_of_dom_2 (D := gset K)) in Hmk.
        apply Hdom in Hmk. apply elem_of_dom in Hmk.
        rewrite Hm'k in Hmk. exact (is_Some_None Hmk).
      + rewrite Hmk Hm'k right_id //.
      + rewrite Hmk Hm'k //. }
  iModIntro. iDestruct "H" as "[$ $]".
Qed.


(** Project one key's fragment (an [is_type_lb] to be) out of a whole-map
    snapshot fragment. *)
Lemma auth_gmap_gset_frag_lookup {K V : Type} `{Countable K} `{Countable V}
    `{!inG Σ (authR (gmapUR K (gsetUR V)))} (γ : gname) (m : gmap K (gset V)) (k : K) (S : gset V) :
  m !! k = Some S ->
  own γ (◯ m) ⊢ own γ (◯ {[k := S]}).
Proof.
  intros Hk. apply own_mono, auth_frag_mono.
  apply/singleton_included_l. exists S.
  split; [by rewrite Hk | apply/Some_included; by left].
Qed.


(** A whole-map fragment (the snapshot [auth_gmap_gset_grow_snap] mints)
    sits pointwise below the authority, at ANY fraction: every key it has is
    registered and its set is a lower bound of the current one. *)
Lemma auth_gmap_gset_included {K V : Type} `{Countable K} `{Countable V}
    `{!inG Σ (authR (gmapUR K (gsetUR V)))} (γ : gname) (dq : dfrac)
    (m M : gmap K (gset V)) :
  own γ (●{dq} m) -∗ own γ (◯ M) -∗
  ⌜∀ (k : K) (S : gset V), M !! k = Some S -> ∃ S', m !! k = Some S' ∧ S ⊆ S'⌝.
Proof.
  iIntros "Ha Hf".
  iDestruct (own_valid_2 with "Ha Hf") as %Hv.
  iPureIntro.
  apply auth_both_dfrac_valid_discrete in Hv as [_ [Hincl _]].
  move=> k S Hk.
  have Hk' := proj1 (lookup_included M m) Hincl k.
  rewrite Hk in Hk'.
  destruct (Some_included_is_Some _ _ Hk') as [S' HS'].
  rewrite HS' Some_included_total gset_included in Hk'.
  exists S'. split; [exact HS' | exact Hk'].
Qed.

(** A singleton fragment weakens to any subset (the lower bound only loses
    information). *)
Lemma auth_gmap_gset_frag_weaken {K V : Type} `{Countable K} `{Countable V}
    `{!inG Σ (authR (gmapUR K (gsetUR V)))} (γ : gname) (k : K) (S S' : gset V) :
  S ⊆ S' -> own γ (◯ {[k := S']}) ⊢ own γ (◯ {[k := S]}).
Proof.
  intros Hsub. apply own_mono, auth_frag_mono, singleton_included_mono. by apply gset_included.
Qed.

(** Mint a fragment below the CURRENT set at a key, under ANY authority
    fraction (a [gset] fragment is core-id, so nothing is transferred): how a
    holder of a [●{dq}] share (a reader's fraction of the store, or the write-lock
    holder) mints an [is_type_lb] at (a subset of) the current item set
    without growing anything. *)
Lemma auth_gmap_gset_frag_alloc {K V : Type} `{Countable K} `{Countable V}
    `{!inG Σ (authR (gmapUR K (gsetUR V)))} (γ : gname) (dq : dfrac)
    (m : gmap K (gset V)) (k : K) (S S' : gset V) :
  m !! k = Some S' -> S ⊆ S' ->
  own γ (●{dq} m) ==∗ own γ (●{dq} m) ∗ own γ (◯ {[k := S]}).
Proof.
  iIntros (Hk Hsub) "Ha".
  iMod (own_update _ _ (●{dq} m ⋅ ◯ {[k := S]}) with "Ha") as "H".
  { apply auth_update_dfrac_alloc; first apply _.
    apply singleton_included_l. exists S'.
    split; [by rewrite Hk |].
    apply Some_included_total. by apply gset_included. }
  iModIntro. iDestruct "H" as "[$ $]".
Qed.

End auth_gmap_gset.

(* Splitting a token bundle into single read capabilities ([wp_NewDoc] hands
   the store's [actualMaxReaders] reader slots to the caller this way). *)
Section tok_replicate.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.

(** A [tok_set] token bundle is the iterated single token. *)
Lemma own_toks_replicate (γ : gname) (n : nat) :
  own_toks γ n -∗ [∗] replicate n (own_toks γ 1).
Proof.
  iInduction n as [| n IH]; iIntros "H"; simpl; first done.
  replace (S n) with (1 + n)%nat by lia.
  iDestruct (own_toks_add_1 n 1 with "H") as "[H1 Hn]".
  iFrame "H1". by iApply "IH".
Qed.

(** Zip two replicated bundles into a replicated bundle of pairs. *)
Lemma big_sep_replicate_sep (n : nat) (P Q : iProp Σ) :
  ([∗] replicate n P) ∗ ([∗] replicate n Q) -∗ [∗] replicate n (P ∗ Q).
Proof.
  iInduction n as [| n IH]; iIntros "[HP HQ]"; simpl; first done.
  iDestruct "HP" as "[HP HPs]". iDestruct "HQ" as "[HQ HQs]".
  iFrame "HP HQ". iApply "IH". iFrame.
Qed.

End tok_replicate.

Section auth_gset.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Notation accUR := (authR (gsetUR YjsId)).
Context {acc_inG : inG Σ accUR}.


(** A fragment [◯ T] under the authority [● S] gives the lower bound [T ⊆ S]. *)
Lemma auth_gset_frag_sub (γ : gname) (S T : gset YjsId) :
  own γ (● S : accUR) -∗ own γ (◯ T : accUR) -∗ ⌜T ⊆ S⌝.
Proof.
  iIntros "Ha Hf". iDestruct (own_valid_2 with "Ha Hf") as %Hv. iPureIntro.
  apply auth_both_valid_discrete in Hv as [Hincl _]. by apply gset_included in Hincl.
Qed.


(** The same comparison under a SHARED authority: a reader holding a [●{dq}]
    share of the delete set still learns that its certificate's ids are in it. *)
Lemma auth_gset_frag_sub_dq (γ : gname) (dq : dfrac) (S T : gset YjsId) :
  own γ (●{dq} S : accUR) -∗ own γ (◯ T : accUR) -∗ ⌜T ⊆ S⌝.
Proof.
  iIntros "Ha Hf". iDestruct (own_valid_2 with "Ha Hf") as %Hv. iPureIntro.
  apply auth_both_dfrac_valid_discrete in Hv as (_ & Hincl & _). by apply gset_included.
Qed.

(** Grow the accepted set (adding [T]) and mint the matching whole-set
    fragment, out of which each [◯ {[i]}] projects. *)
Lemma auth_gset_grow (γ : gname) (S T : gset YjsId) :
  own γ (● S : accUR) ==∗ own γ (● (S ∪ T) : accUR) ∗ own γ (◯ (S ∪ T) : accUR).
Proof.
  iIntros "Ha".
  iMod (own_update _ _ (● (S ∪ T) ⋅ ◯ (S ∪ T)) with "Ha") as "H".
  { apply auth_update_alloc. apply local_update_unital_discrete.
    intros z _ Heq. rewrite left_id in Heq. split.
    - done.
    - rewrite -Heq gset_op. set_solver. }
  iModIntro. iDestruct "H" as "[$ $]".
Qed.


(** Project a subset fragment (in particular a singleton receipt). *)
Lemma auth_gset_frag_mono (γ : gname) (S T : gset YjsId) :
  T ⊆ S -> own γ (◯ S : accUR) ⊢ own γ (◯ T : accUR).
Proof. intros Hsub. apply own_mono, auth_frag_mono. by apply gset_included. Qed.


(** Two lower bounds join into their union ([◯] fragments of a [gset]
    authority compose by union). *)
Lemma auth_gset_frag_union (γ : gname) (S T : gset YjsId) :
  own γ (◯ S : accUR) -∗ own γ (◯ T : accUR) -∗ own γ (◯ (S ∪ T) : accUR).
Proof.
  iIntros "H1 H2". iCombine "H1 H2" as "H".
  rewrite -gset_op auth_frag_op. iExact "H".
Qed.


(** The empty lower bound, out of thin air (the unit of the fragment). *)
Lemma auth_gset_frag_empty (γ : gname) :
  ⊢ |==> own γ (◯ (∅ : gset YjsId) : accUR).
Proof. iApply own_unit. Qed.

End auth_gset.

Section big_sepM_imap.
Context {PROP : bi}.
Context `{Countable K} {A B : Type}.

(** A big-op over a [map_imap] with a total (always-[Some]) function is the
    big-op over the underlying map at the transformed entries. *)
Lemma big_sepM_map_imap_total (f : K -> A -> B) (Φ : K -> B -> PROP) (m : gmap K A) :
  ([∗ map] i ↦ y ∈ map_imap (λ i x, Some (f i x)) m, Φ i y) ⊣⊢
  ([∗ map] i ↦ x ∈ m, Φ i (f i x)).
Proof.
  induction m as [|i x m Hmi IH] using map_ind.
  - rewrite map_imap_empty !big_sepM_empty //.
  - rewrite (map_imap_insert_Some _ _ _ _ (f i x)); [| done].
    rewrite big_sepM_insert; last first.
    { rewrite map_lookup_imap Hmi //. }
    rewrite big_sepM_insert; [| exact Hmi].
    rewrite IH //.
Qed.

End big_sepM_imap.

(** [fmap] distributes over [concat]. *)
Lemma fmap_concat {X Y : Type} (f : X -> Y) (L : list (list X)) :
  (f <$> concat L : list Y) = concat ((λ l : list X, (f <$> l : list Y)) <$> L : list (list Y)).
Proof. induction L as [| l L IH]; [done |]. simpl. rewrite fmap_app IH //. Qed.

(** Two maps with the same domain list the same keys, up to order. *)
Lemma map_to_list_fst_perm {K V1 V2 : Type} `{Countable K}
    (m1 : gmap K V1) (m2 : gmap K V2) :
  dom m1 = dom m2 -> (map_to_list m1).*1 ≡ₚ (map_to_list m2).*1.
Proof.
  move=> Hdom. apply NoDup_Permutation; [apply NoDup_fst_map_to_list..|].
  move=> k. rewrite !list_elem_of_fmap.
  split.
  - move=> [[k' v] [-> Hin]]. simpl.
    have Hk : k' ∈ dom m2.
    { rewrite -Hdom. apply elem_of_dom. exists v. by apply elem_of_map_to_list. }
    apply elem_of_dom in Hk as [v2 Hv2]. exists (k', v2). split; [done |].
    by apply elem_of_map_to_list.
  - move=> [[k' v] [-> Hin]]. simpl.
    have Hk : k' ∈ dom m1.
    { rewrite Hdom. apply elem_of_dom. exists v. by apply elem_of_map_to_list. }
    apply elem_of_dom in Hk as [v1 Hv1]. exists (k', v1). split; [done |].
    by apply elem_of_map_to_list.
Qed.
