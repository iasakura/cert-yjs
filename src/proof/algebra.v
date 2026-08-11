(** General Iris resource-algebra laws the cert-yjs proofs use.

    They live here rather than in a type's [heap.v] because they say nothing
    about any of our definitions: growth, lookup and fragment minting for an
    [auth (gmap K (gset V))] (the per-type item sets), the same for an
    [auth (gset YjsId)] (the accepted-id set), a grow-and-persist step for a
    [ghost_map] (the root-type registry), and replication laws for [tok_set]
    token bundles (the reader capabilities). *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.proof Require Import core.
From New.proof Require Import tok_set.
From iris.algebra Require Import auth gmap gset.

(* A generic [ghost_map] grow-and-persist step, in its own section so it depends
   only on a [ghost_mapG] instance (issue #54): the certificate proof in
   [store/applyUpdate], whose section lacks the store's [seq_inG] / [ftypes_inG],
   reconciles the registry map with the concrete one after [applyUpdate]'s drain
   creates fresh root types, minting one persistent binding per new name. *)
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
    of the authority ([●{dq} m], from [store_inv_ro]) can still learn membership
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


(** Mint a fragment below the CURRENT set at a key, under ANY authority
    fraction (a [gset] fragment is core-id, so nothing is transferred): how a
    holder of a [●{dq}] share (a reader's [store_inv_ro], or the write-lock
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

End auth_gset.
