(** store update path, split layer: [wp_store__splitNode],
    [wp_store__splitAtAndGetLeft] / [wp_store__splitAtAndGetRight] (each over
    the whole store, with a local stepping stone over the item index and the
    pool), plus the
    split-pool bookkeeping ([pool_invs], [split_types_update_rel], the
    [split_pool_*] / [split_cells_*] lemmas). Split out of
    [store/GetNode] so it proof-checks in parallel; same [Section]
    boilerplate and [#[local]] instances. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.item Require Import run_theory model value heap.
From New.proof Require Import history.
From New.proof.store Require Import model value heap Integrate.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
From New.proof.store Require Import GetNode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

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
Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* the grow-only item-set RA (the certificate proofs grow the [sn_seq]
   authority and mint [is_type_lb] fragments) *)
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
(* The store's reader-count accounting ties the readers' share to the [types]
   map via a [dfrac_agree]; [store/heap] declares it up front, so the specs
   reached from here carry it too. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

(* [client_run]'s merge_sort instances are [#[local]] in [store/model];
   the run-list lemmas here need them again. *)
#[local] Instance cell_le_dec : RelDecision cell_le.
Proof. rewrite /cell_le. solve_decision. Defined.
#[local] Instance cell_le_trans : Transitive cell_le.
Proof. rewrite /cell_le. move=> x y z. lia. Qed.
#[local] Instance cell_le_total : Total cell_le.
Proof. rewrite /cell_le. move=> x y. lia. Qed.

(** [store.getOrCreateYType], lookup-hit case: the name is already bound in
    the registry, so the creation branch is dead and the bound type comes
    back. This is the only case the verified update path needs — see
    [wp_store__applyUpdate]'s bound-names precondition (the on-the-fly type
    creation of y-octo's update path is outside the verified subset for now:
    it would grow [types]/[bind]/[m] with a fresh empty type mid-batch). *)


(** The head model item survives a nonempty left truncation ([take]) — used by
    the split's LEFT half ([ic_run = take o (ic_run c)]), which keeps the node's
    location and head. Stated over the raw run list ([run_head c = hd inhabitant
    (ic_run c)]); [split_cell_left] lives in [store/model]. *)
Lemma hd_inhabitant_take (r : list (YjsItem A)) (o : nat) :
  (0 < o)%nat -> hd inhabitant (take o r) = hd inhabitant r.
Proof.
  move=> Ho. destruct r as [|a r']; first by rewrite take_nil.
  destruct o; [lia | done].
Qed.



(** The head of a right drop is the element at the drop offset — the split's
    RIGHT half heads at [ic_run c !! o]. *)
Lemma hd_inhabitant_drop (r : list (YjsItem A)) (o : nat) (y : YjsItem A) :
  r !! o = Some y -> hd inhabitant (drop o r) = y.
Proof. move=> Ho. rewrite (drop_S r y o Ho) //=. Qed.


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
    [Hckbnd] (the head clock fits as a NAT, from [own_type_pool_id_bounds])
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
      move=> originId Hoid Hcl.
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
  - (* leftCell vs leftCell: same loc, guard is false *)
    exfalso. exact (Hlocne eq_refl).
  - (* leftCell vs rightCell: left half strictly below the right half *)
    left. rewrite Hclockl Hlenl HclkrZ. lia.
  - (* leftCell vs old *)
    have Hcc' : cell_client c2 = cell_client cw by rewrite -Hcc Hclientl //.
    destruct (Holdcase c2 Hc2 Hcc') as [Hd | Hd].
    + right. rewrite Hclockl. lia.
    + left. rewrite Hclockl Hlenl. lia.
  - (* rightCell vs leftCell *)
    right. rewrite Hclockl Hlenl HclkrZ. lia.
  - (* rightCell vs rightCell: same loc *)
    exfalso. exact (Hlocne eq_refl).
  - (* rightCell vs old *)
    have Hcc' : cell_client c2 = cell_client cw by rewrite -Hcc Hclientr //.
    destruct (Holdcase c2 Hc2 Hcc') as [Hd | Hd].
    + right. rewrite HclkrZ. lia.
    + left. rewrite HclkrZ Hlenr. lia.
  - (* old vs leftCell *)
    have Hcc' : cell_client c1 = cell_client cw by rewrite Hcc Hclientl //.
    destruct (Holdcase c1 Hc1 Hcc') as [Hd | Hd].
    + left. rewrite Hclockl. lia.
    + right. rewrite Hclockl Hlenl. lia.
  - (* old vs rightCell *)
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

(** A split refines the live cells: both halves inherit the node's
    [ic_deleted] bit and share out its run ([split_cell_left] takes a prefix,
    [split_cell_right] the matching suffix), so a live cell after the split is
    covered, chars and all, by a live cell before it. This is what carries the
    tombstone-set invariant [delete_set_tombstoned] across a split. *)
Lemma split_pool_live_refine (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k o : nat) (rloc : loc)
    (cw : item_cell) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  live_refine types (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types).
Proof.
  move=> Htypes Hck.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  have Hcw : cw ∈ all_cells types by rewrite Hold; apply list_elem_of_here.
  move=> c' Hc' Hlive. rewrite Hnew in Hc'.
  apply elem_of_cons in Hc' as [-> | Hc'].
  { exists cw. split_and!; [exact Hcw | exact Hlive |].
    move=> y Hy. rewrite -(take_drop o (ic_run cw)). apply elem_of_app. by left. }
  apply elem_of_cons in Hc' as [-> | Hc'].
  { exists cw. split_and!; [exact Hcw | exact Hlive |].
    move=> y Hy. rewrite -(take_drop o (ic_run cw)). apply elem_of_app. by right. }
  exists c'. split_and!; [rewrite Hold; apply elem_of_cons; by right | exact Hlive | done].
Qed.

(** Dually, a split keeps every tombstoned char tombstoned: the halves inherit
    the node's bit and partition its run, so a dead char lands in one of them.
    This is what carries a delete loop's "covered so far" record across the
    splits the next iteration performs. *)
Lemma split_pool_dead_chars_kept (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k o : nat) (rloc : loc)
    (cw : item_cell) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  dead_chars_kept types (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types).
Proof.
  move=> Htypes Hck.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  move=> c Hc Hdel y Hy. rewrite Hold in Hc.
  apply elem_of_cons in Hc as [-> | Hc]; last first.
  { exists c. split_and!;
      [rewrite Hnew; apply elem_of_cons; right; apply elem_of_cons; by right
      | exact Hdel | exact Hy]. }
  (* the split node: the char sits in the prefix or in the suffix *)
  rewrite -(take_drop o (ic_run cw)) in Hy.
  apply elem_of_app in Hy as [Hy | Hy].
  - exists (split_cell_left cw o). split_and!;
      [rewrite Hnew; apply list_elem_of_here | exact Hdel | exact Hy].
  - exists (split_cell_right cw o rloc). split_and!;
      [rewrite Hnew; apply elem_of_cons; right; apply list_elem_of_here
      | exact Hdel | exact Hy].
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


(** The pool invariants survive a split: the two halves inherit the node's
    coordinates ([split_pool_fits] / [_rangedisj] / [_originclk]) and the
    right half lands at a fresh location ([split_pool_locdup]). *)
Lemma pool_invs_split (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z ->
  rloc ∉ (ic_loc <$> all_cells types) ->
  pool_invs types ->
  pool_invs (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types).
Proof.
  move=> Htypes0 Hck Hrunwf Ho Hckbnd Hrfresh [Hfits [Hnodup [Hrangedisj Horiginclk]]].
  have Hcwmem : cw ∈ all_cells types.
  { apply all_cells_elem_of. exists parent, (MkTypeState cells arr).
    split; [exact Htypes0 | exact (list_elem_of_lookup_2 _ _ _ Hck)]. }
  have Hfitscw := Hfits cw Hcwmem.
  split_and!.
  - exact (split_pool_fits types parent cells arr k cw _ rloc Htypes0 Hck Hrunwf Ho Hckbnd Hfits).
  - exact (split_pool_locdup types parent cells arr k cw _ rloc Htypes0 Hck Hrfresh Hnodup).
  - exact (split_pool_rangedisj types parent cells arr k cw _ rloc Htypes0 Hck Hrunwf Ho Hckbnd Hfitscw Hnodup Hrangedisj).
  - exact (split_pool_originclk types parent cells arr k cw _ rloc Htypes0 Hck Hrunwf Ho Horiginclk).
Qed.

(** [store.splitNode n diff] (issue #28 M4): split the run cell [cw] (at DLL
    index [k] of type [parent]) at offset [diff] into a truncated left half
    (same node loc) and a fresh right half ([rloc]), updating both the
    per-type DLL and the per-client run list. The pure cell effect is
    [split_cells cells k (uint.nat diff) rloc], invisible to the flattened
    document. *)
(** Proof note: [word] does not use [0 <= Z.of_nat l] on its own, so a
    [clock + length < 2^64] bound needs the length-nonneg fact spelled out to
    recover the per-clock [< 2^64] word conversion (issue #28 U7c); the proof
    keeps [word] on clean variables. *)
Lemma wp_store__splitNode (s : loc) (st : store_state)
    (parent : loc) (cells arr : list _) (k : nat) (cw : item_cell) (diff : w64) :
  ss_types st !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  (0 < uint.nat diff < length (ic_run cw))%nat ->
  {{{ is_pkg_init yjs ∗ own_store_struct s st }}}
    s @! (go.PointerType yjs.store) @! "splitNode" #(ic_loc cw) #diff
  {{{ (rloc : loc), RET (#(ic_loc cw), #rloc);
      own_store_struct s
        (st <| ss_types := <[parent := MkTypeState (split_cells cells k (uint.nat diff) rloc) arr]> (ss_types st) |>) ∗
      ⌜fresh_loc rloc (ss_types st)⌝ }}}.
Proof using Type*.
  move=> Htypes Hcellk Hdiff.
  destruct st as [client0 k0 types bind pend pdel]. simpl in *.
  iIntros (Φ) "(#Hpkg & Hcells) HΦ".
  iDestruct "Hcells" as "(Hfields0 & %Hinvs0)".
  have Hpool : pool_invs types := proj1 Hinvs0.
  have Hreg0 : registry_coh bind types := proj2 Hinvs0.
  have [Hrunfits [Hnodup [Hrangedisj Horiginclk]]] := Hpool.
  iDestruct "Hfields0" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iDestruct "Hitems" as (mref) "(Hitemsf & Hitemmap)".
  have Hcwmem0 : cw ∈ all_cells types.
  { apply all_cells_elem_of. exists parent, (MkTypeState cells arr).
    split; [exact Htypes | exact (list_elem_of_lookup_2 _ _ _ Hcellk)]. }
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbnds0.
  have Hckbnd0 : (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z := proj2 (Hbnds0 cw Hcwmem0).
  iDestruct (own_type_pool_runs_wf with "Htypes") as %Hwfs0.
  have Hrunwf0 : run_wf (ic_run cw) := Hwfs0 cw Hcwmem0.
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
  iDestruct "Hseg2" as (itemVal olidcw oridcw) "Hcons".
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
  have Hsclen : length (itemVal.(yjs.item.content').(yjs.content.content')) = length cw.(ic_run).
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
  iAssert (own_type_pool (DfracOwn 1) (delete parent types))%I with "[Hrestown Hrestinv]" as "Hrestmap".
  { rewrite /own_type_pool big_sepM_sep. iFrame "Hrestown Hrestinv". }
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
  have Hnowrapcw : (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) < 2^64)%Z := Hrunfits cw Hcwmem.
  have Hdisj : ∀ c, c ∈ all_cells types -> cell_client c = cell_client cw -> ic_loc c ≠ ic_loc cw ->
     (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z (cell_clock cw))%Z ∨
     (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) <= uint.Z (cell_clock c))%Z
    := λ c Hc Hcc Hlocne, Hrangedisj c cw Hc Hcwmem Hcc Hlocne.
  have Hckbnd : (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z
    by (rewrite Hid /toYjsId /=; word).
  have Hcwck : cell_clock cw = itemVal.(yjs.item.id').(yjs.id.clock').
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
  have Hcontl : content <$> take o cw.(ic_run) = explode (take (sint.nat diff) itemVal.(yjs.item.content').(yjs.content.content')).
  { rewrite Hsintdiff fmap_take Hcontent /toContent /explode fmap_take //. }
  have Hsubdrop : subslice (sint.nat diff) (sint.nat cbs.(slice.len)) itemVal.(yjs.item.content').(yjs.content.content')
                = drop o itemVal.(yjs.item.content').(yjs.content.content').
  { rewrite Hsintdiff Hsintlen -Hsclen /subslice. rewrite take_ge; [reflexivity | lia]. }
  have Hcontr : content <$> drop o cw.(ic_run) = explode (drop o itemVal.(yjs.item.content').(yjs.content.content')).
  { rewrite fmap_drop Hcontent /toContent /explode fmap_drop //. }
  (* [if n.right != nil] branches on whether [cw] is the run's last cell (suf) *)
  destruct suf as [|d0 drest] eqn:Hsufeq.
  - (* cw is last: no downstream relink. Remaining: own_dll_split (cs2=[]),
       own_ytype_cells rebuild over split_cells, and the item-map surgery
       (getNodeIndex over the split run + client_run_loc_insert). *)
    (* ----- guard + n.right := rs ----- *)
    iDestruct "Hrest" as %[Hrnull Htl0eq].
    rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.right') = null) Hrnull).
    wp_auto.
    (* ----- branch-agnostic split-cell pure facts (origin telescoping) ----- *)
    set (leftCell := split_cell_left cw o).
    set (rightCell := split_cell_right cw o rs).
    set (originId := {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId');
                   yjs.id.clock' := word.sub (word.add itemVal.(yjs.item.id').(yjs.id.clock') diff) (W64 1) |}).
    have Hopos : (0 < o)%nat by (rewrite /o; lia).
    have Hnowrap_add : (uint.Z itemVal.(yjs.item.id').(yjs.id.clock') + uint.Z diff < 2^64)%Z.
    { rewrite -Hcwck. have H1 := Hnowrapcw. have H2 := Hdiff. word. }
    have Hadd_eq : (uint.nat itemVal.(yjs.item.id').(yjs.id.clock') + o)%nat = uint.nat (word.add itemVal.(yjs.item.id').(yjs.id.clock') diff).
    { rewrite /o. clear -Hnowrap_add. word. }
    have [xprev Hxprev] : is_Some (cw.(ic_run) !! (o - 1)%nat).
    { apply lookup_lt_is_Some. rewrite /o. lia. }
    have Hyo2 : cw.(ic_run) !! S (o - 1)%nat = Some yo.
    { replace (S (o - 1))%nat with o by (rewrite /o; lia). exact Hyo. }
    have Hstep := proj2 Hrun (o - 1)%nat xprev yo Hxprev Hyo2.
    have Horig : origin yo = itemPtr xprev by (destruct Hstep as [_ [Hh _]]; exact Hh).
    have Hxpid := run_wf_lookup_clock cw.(ic_run) (o - 1)%nat (run_head cw) xprev Hrun Hrun0 Hxprev.
    have Hcrorig : origin_id (origin (run_head rightCell)) = toYjsId <$> Some originId.
    { rewrite /rightCell Hrhcr Horig /origin_id /=. f_equal.
      rewrite Hxpid Hid /toYjsId /originId /=. f_equal. clear -Hnowrap_add Hdiff. word. }
    have Hrhck : clock (item_id (run_head cw)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clock') by (rewrite Hid /toYjsId /=).
    have Hclcl : cell_clock leftCell = cell_clock cw by (rewrite /leftCell /cell_clock Hrhcl).
    have Hcccl : cell_client leftCell = cell_client cw by (rewrite /leftCell /cell_client Hrhcl).
    have Hcccr : cell_client rightCell = cell_client cw by (rewrite /rightCell /cell_client Hrhcr Hyoid /=).
    have Hccr_clock : uint.Z (cell_clock rightCell) = (uint.Z (cell_clock cw) + Z.of_nat o)%Z.
    { rewrite /rightCell /cell_clock Hrhcr Hyoid /= Hrhck. clear -Hnowrap_add Hdiff. rewrite /o. word. }
    have Hsc : split_cells cells k o rs = pre ++ leftCell :: rightCell :: [].
    { rewrite /split_cells Hcellk. rewrite -/suf Hsufeq. rewrite app_nil_r. reflexivity. }
    (* the split-cell struct values [ivl] (truncated cw) / [ivr] (right half) *)
    set (ivl := itemVal <| yjs.item.content' := {| yjs.content.content' := take (sint.nat diff) itemVal.(yjs.item.content').(yjs.content.content') |} |> <| yjs.item.right' := rs |>).
    set (ivr := {| yjs.item.id' := {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId'); yjs.id.clock' := word.add itemVal.(yjs.item.id').(yjs.id.clock') diff |};
                   yjs.item.originLeftId' := olid_ptr;
                   yjs.item.originRightId' := itemVal.(yjs.item.originRightId');
                   yjs.item.left' := cw.(ic_loc);
                   yjs.item.right' := itemVal.(yjs.item.right');
                   yjs.item.parent' := itemVal.(yjs.item.parent');
                   yjs.item.content' := {| yjs.content.content' := subslice (sint.nat diff) (sint.nat cbs.(slice.len)) itemVal.(yjs.item.content').(yjs.content.content') |};
                   yjs.item.flags' := itemVal.(yjs.item.flags') |}).
    have Hivl_ol : ivl.(yjs.item.originLeftId') = itemVal.(yjs.item.originLeftId') by (rewrite /ivl /=).
    have Hivl_or : ivl.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId') by (rewrite /ivl /=).
    have Hivl_left : ivl.(yjs.item.left') = ml by (rewrite /ivl /=; exact Hprev).
    have Hivr_r : ivr.(yjs.item.right') = null by (rewrite /ivr /=; exact Hrnull).
    have Hrhcl' : run_head leftCell = run_head cw by (rewrite /leftCell; exact Hrhcl).
    have Hrhcr' : run_head rightCell = yo by (rewrite /rightCell; exact Hrhcr).
    have Hrhcli : clientId (item_id (run_head cw)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clientId') by (rewrite Hid /toYjsId /=).
    have Hclloc : ic_loc leftCell = cw.(ic_loc) by (rewrite /leftCell /=).
    have Hcrloc : ic_loc rightCell = rs by (rewrite /rightCell /=).
    have Hivr_ol : ivr.(yjs.item.originLeftId') = olid_ptr by (rewrite /ivr /=).
    have Hivr_or : ivr.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId') by (rewrite /ivr /=).
    have Hp1 : ic_loc leftCell ≠ null by (rewrite /leftCell /=; exact Hmfnn).
    have Hp2 : ic_loc rightCell ≠ null by (rewrite /rightCell /=; exact Hrsnn).
    have Hp4 : ivl.(yjs.item.right') = ic_loc rightCell by (rewrite /ivl /rightCell /=).
    have Hp5 : ivl.(yjs.item.parent') = ic_parent leftCell by (rewrite /ivl /leftCell /=; exact Hpar).
    have Hp6 : item_id (run_head leftCell) = toYjsId ivl.(yjs.item.id'). { rewrite Hrhcl' /ivl /=. exact Hid. }
    have Hp7 : content <$> ic_run leftCell = explode (toContent ivl.(yjs.item.content')). { rewrite /leftCell /ivl /toContent /=. exact Hcontl. }
    have Hp8 : origin_id (origin (run_head leftCell)) = toYjsId <$> olidcw. { rewrite Hrhcl'. exact Holid. }
    have Hp9 : origin_id (rightOrigin (run_head leftCell)) = toYjsId <$> oridcw. { rewrite Hrhcl'. exact Horid. }
    have Hp10 : ivl.(yjs.item.flags') = (if ic_deleted leftCell then W8 6 else W8 2). { rewrite /ivl /leftCell /=. exact Hflags. }
    have Hp11 : run_wf (ic_run leftCell). { rewrite /leftCell /=. exact (run_wf_take cw.(ic_run) o Hopos Hrun). }
    have Hp12 : ivr.(yjs.item.left') = ic_loc leftCell. { rewrite /ivr /leftCell /=. reflexivity. }
    have Hp13 : ivr.(yjs.item.parent') = ic_parent rightCell. { rewrite /ivr /rightCell /=. exact Hpar. }
    have Hp14 : item_id (run_head rightCell) = toYjsId ivr.(yjs.item.id'). { rewrite Hrhcr' Hyoid /ivr /toYjsId /=. rewrite Hrhck Hrhcli Hadd_eq. reflexivity. }
    have Hp15 : content <$> ic_run rightCell = explode (toContent ivr.(yjs.item.content')). { rewrite /rightCell /ivr /toContent /= Hsubdrop. exact Hcontr. }
    have Hp17 : origin_id (rightOrigin (run_head rightCell)) = toYjsId <$> oridcw. { rewrite Hrhcr' Hyoro. exact Horid. }
    have Hp18 : ivr.(yjs.item.flags') = (if ic_deleted rightCell then W8 6 else W8 2). { rewrite /ivr /rightCell /=. exact Hflags. }
    have Hp19 : run_wf (ic_run rightCell). { rewrite /rightCell /=. exact (run_wf_drop cw.(ic_run) o Hoinrun Hrun). }
    (* ----- read the client run slice (map.lookup1), BEFORE Phase A locks cw ----- *)
    iDestruct "Hitemmap" as (gm) "(Hmap & Hruns & %Hcomplete & %Hclkloc)".
    set (kc := itemVal.(yjs.item.id').(yjs.id.clientId')).
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
      iApply (own_dll_split (DfracOwn 1) pre (@nil item_cell) leftCell rightCell ivl ivr olidcw oridcw (Some originId) oridcw yt.(yjs.yType.start') rs ml Hp1 Hp2 Hivl_left Hp4 Hp5 Hp6 Hp7 Hp8 Hp9 Hp10 Hp11 Hp12 Hp13 Hp14 Hp15 Hcrorig Hp17 Hp18 Hp19).
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
      - apply elem_of_cons in Hc as [-> | Hc]; [rewrite /leftCell /=; exact Hcparcw |].
        apply elem_of_cons in Hc as [-> | Hc]; [rewrite /rightCell /=; exact Hcparcw | by apply elem_of_nil in Hc]. }
    iAssert (own_ytype_cells parent (DfracOwn 1) (split_cells cells k o rs) arr) with "[Hparent Hdll2]" as "Hyt2".
    { iExists yt, rs. iFrame "Hparent Hdll2". iPureIntro. split_and!.
      - rewrite (split_cells_num_visible cells k o rs cw Hcellk). exact Hlen0.
      - rewrite /cells_repr (split_cells_flatten cells k o rs cw Hcellk). exact Hrepr0.
      - exact Hcpar_split. }
    iAssert (own_type_pool (DfracOwn 1) (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types))%I with "[Hyt2 Hrestmap]" as "Htypes2".
    { rewrite /own_type_pool -insert_delete_eq big_sepM_insert_delete delete_delete_eq.
      iFrame "Hrestmap". simpl. iFrame "Hyt2". iPureIntro. exact Harrinv. }
    (* ----- getNodeIndex over the split run [run_half] = client_run with cw -> leftCell ----- *)
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
    have Hss_half : StronglySorted cell_le (<[kw := leftCell]> (client_run types kc)) := Hss_replace (client_run types kc) kw cw leftCell (client_run_sorted types kc) Hkw Hclcl.
    set (run_half := <[kw := leftCell]> (client_run types kc)).
    have HndAll : NoDup (all_cells types) := NoDup_fmap_1 ic_loc _ Hnodup.
    have Hndrun : NoDup (client_run types kc).
    { rewrite /client_run (merge_sort_Permutation cell_le _). apply NoDup_filter. exact HndAll. }
    have Hkwlt : (kw < length (client_run types kc))%nat by (apply lookup_lt_Some in Hkw; exact Hkw).
    have Hlockw : (ic_loc <$> client_run types kc) !! kw = Some (ic_loc leftCell).
    { rewrite list_lookup_fmap Hkw /=. done. }
    have Hlocs : ic_loc <$> run_half = ic_loc <$> client_run types kc.
    { rewrite /run_half list_fmap_insert (list_insert_id _ _ _ Hlockw) //. }
    have Hkw_half : run_half !! kw = Some leftCell.
    { rewrite /run_half. apply list_lookup_insert_Some. left. split_and!; [reflexivity | reflexivity | exact Hkwlt]. }
    have Hclk_half : cell_clock leftCell = itemVal.(yjs.item.id').(yjs.id.clock') by (rewrite Hclcl Hcwck).
    have Hsub : ∀ c, c ∈ run_half → c = leftCell ∨ c ∈ client_run types kc.
    { move=> c Hc. apply list_elem_of_lookup_1 in Hc as [j Hj]. rewrite /run_half in Hj.
      apply list_lookup_insert_Some in Hj as [(_ & <- & _) | (_ & Hj)]; [by left | right; exact (list_elem_of_lookup_2 _ _ _ Hj)]. }
    have Hfits_half : ∀ c, c ∈ run_half → (uint.Z (cell_clock c) + length (ic_run c) < 2^64)%Z.
    { move=> c Hc. destruct (Hsub c Hc) as [-> | HcL].
      - rewrite Hclcl /leftCell /= length_take. have H := Hnowrapcw. lia.
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
    (* pin [uint.nat idx = kw]: the covering cell in [run_half] is [leftCell] (NoDup locs) *)
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
    have Hclcli : cell_client leftCell = cell_client cw by (rewrite /leftCell /cell_client Hrhcl).
    have Hrun_half : sorted_client_run (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) kc run_half.
    { split_and!; [exact Hss_half | rewrite Hlocs; exact HndLocRun |].
      move=> c Hc. apply client_run_mem. split; [exact (Hmem_half c Hc) |].
      destruct (Hsub c Hc) as [-> | HcL]; [rewrite Hclcli; exact Hcwcc |].
      exact (proj2 (proj1 (client_run_mem types kc c) HcL)). }
    have Hpool2 : pool_invs (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types)
      := pool_invs_split types parent cells arr k cw o rs Htypes Hcellk Hrun Hdiff Hckbnd Hrsfresh Hpool.
    iEval (rewrite -Hlocs) in "Hslice".
    wp_apply (wp_getNodeIndex slk (DfracOwn 1) (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) kc run_half (itemVal.(yjs.item.id').(yjs.id.clock')) Hrun_half Hpool2 with "[$Hslice $Htypes2]").
    iIntros (idx ok) "(Hslice & Htypes2 & %Hires)".
    iDestruct (own_type_pool_id_bounds with "Htypes2") as %Hbnds2.
    have Hlcbnd := proj2 (Hbnds2 leftCell (Hmem_half leftCell (list_elem_of_lookup_2 _ _ _ Hkw_half))).
    have Hlccov : cell_covers_clock leftCell (uint.nat itemVal.(yjs.item.id').(yjs.id.clock')).
    { have Hlen : (0 < length (ic_run leftCell))%nat.
      { rewrite /leftCell /split_cell_left /= length_take /o. lia. }
      move: Hclk_half. rewrite /cell_clock /cell_covers_clock. move=> Hclk. split; word. }
    destruct ok; last first.
    { exfalso. exact (Hires leftCell (list_elem_of_lookup_2 _ _ _ Hkw_half) Hlccov). }
    destruct Hires as (cres & Hcres & Hcov).
    have Hcresbnd := proj2 (Hbnds2 cres (Hmem_half cres (list_elem_of_lookup_2 _ _ _ Hcres))).
    have Hcresle : (uint.Z (cell_clock cres) <= uint.Z itemVal.(yjs.item.id').(yjs.id.clock'))%Z.
    { destruct Hcov as [H1 _]. rewrite /cell_clock. word. }
    have Hcreslt : (uint.Z itemVal.(yjs.item.id').(yjs.id.clock') < uint.Z (cell_clock cres) + Z.of_nat (length (ic_run cres)))%Z.
    { destruct Hcov as [_ H2]. rewrite /cell_clock. word. }
    have Hcresmem : cres ∈ run_half := list_elem_of_lookup_2 _ _ _ Hcres.
    have Hcresloc : ic_loc cres = ic_loc leftCell.
    { destruct (Hsub cres Hcresmem) as [-> | HcresL]; [reflexivity |].
      have Hcresall : cres ∈ all_cells types := proj1 (proj1 (client_run_mem types kc cres) HcresL).
      have Hcrescc : cell_client cres = cell_client cw.
      { rewrite (proj2 (proj1 (client_run_mem types kc cres) HcresL)) -Hcwcc //. }
      destruct (decide (ic_loc cres = ic_loc cw)) as [Heq | Hne].
      - rewrite Heq Hclloc //.
      - exfalso. rewrite -Hcwck in Hcresle Hcreslt.
        destruct (Hdisj cres Hcresall Hcrescc Hne) as [Hd | Hd]; lia. }
    have Hidxloc : (ic_loc <$> run_half) !! (uint.nat idx) = Some (ic_loc leftCell) by (rewrite list_lookup_fmap Hcres /= Hcresloc //).
    have Hkwloc : (ic_loc <$> run_half) !! kw = Some (ic_loc leftCell) by (rewrite list_lookup_fmap Hkw_half //).
    have HndLocRunHalf : NoDup (ic_loc <$> run_half) by (rewrite Hlocs; exact HndLocRun).
    have Hidxkw : uint.nat idx = kw := NoDup_lookup _ _ _ _ HndLocRunHalf Hidxloc Hkwloc.
    have Hcrescl : cres = leftCell.
    { have Htmp : run_half !! kw = Some cres by (rewrite -Hidxkw; exact Hcres). congruence. }
    iEval (rewrite Hlocs) in "Hslice".
    (* ----- the append-based item-map surgery (no length-fit side condition:
       append's growth is modeled with an overflow assume, so no client-run
       capacity premise is needed, unlike a pre-sized make) ----- *)
    iDestruct (own_slice_len with "Hslice") as %[Hslklen Hslklen0].
    rewrite length_fmap in Hslklen Hslklen0.
    have Hkwlt2 : (kw < length (client_run types kc))%nat by (apply lookup_lt_Some in Hkw).
    have Hidxsint : sint.Z idx = Z.of_nat kw by (move: Hslklen Hslklen0 Hkwlt2; rewrite -Hidxkw => ? ? ?; word).
    wp_auto.
    iDestruct (own_slice_wf with "Hslice") as %Hslkwf.
    (* newNodes = append(nil, nodes[:index+1]...) *)
    rewrite decide_True; last word.
    wp_auto.
    have Hsplitbnd : (0 ≤ sint.Z (w64_word_instance.(word.add) idx (W64 1)) ≤ sint.Z slk.(slice.len) ≤ sint.Z slk.(slice.len))%Z by word.
    iDestruct (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) (ic_loc <$> client_run types kc) Hsplitbnd with "Hslice") as "(Hsl_pre & Hsl_suf & Hsl_tail)".
    iAssert (slice.nil ↦* ([] : list loc))%I with "[]" as "Hnil0"; first iApply own_slice_nil.
    iAssert (own_slice_cap loc slice.nil (DfracOwn 1))%I with "[]" as "Hnilcap"; first iApply own_slice_cap_nil.
    wp_apply (wp_slice_append with "[Hnil0 Hnilcap Hsl_pre]"); first (iFrame "Hnil0 Hnilcap Hsl_pre").
    iIntros (sl1) "(Hsl1 & Hsl1cap & Hsl_pre)".
    wp_auto.
    (* newNodes = append(newNodes, right) *)
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "%slit [Hslit _]". wp_auto.
    wp_apply (wp_slice_append with "[Hsl1 Hsl1cap Hslit]"); first (iFrame "Hsl1 Hsl1cap Hslit").
    iIntros (sl2) "(Hsl2 & Hsl2cap & _)".
    wp_auto.
    (* newNodes = append(newNodes, nodes[index+1:]...) *)
    rewrite decide_True; last word.
    wp_auto.
    wp_apply (wp_slice_append with "[Hsl2 Hsl2cap Hsl_suf]"); first (iFrame "Hsl2 Hsl2cap Hsl_suf").
    iIntros (newSl) "(HnewNodes & HnewCap & Hsl_suf)".
    wp_auto.
    have HnkB : sint.nat (w64_word_instance.(word.add) idx (W64 1)) = (kw + 1)%nat.
    { move: Hslklen Hslklen0 Hkwlt2 Hidxsint => ? ? ? ?. word. }
    have Esrc : subslice (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (sint.nat slk.(slice.len)) (ic_loc <$> client_run types kc) = drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite HnkB -Hslklen /subslice take_ge; [reflexivity | rewrite length_fmap; clear -Hkwlt2; lia]. }
    have Elit : <[sint.nat (W64 0) := rs]> ([null] : list loc) = [rs].
    { have -> : sint.nat (W64 0) = 0%nat by word. reflexivity. }
    have Eall : (([] ++ take (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (ic_loc <$> client_run types kc)) ++ <[sint.nat (W64 0) := rs]> ([null] : list loc)) ++ subslice (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (sint.nat slk.(slice.len)) (ic_loc <$> client_run types kc) = take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite Esrc Elit HnkB app_nil_l -app_assoc /=. reflexivity. }
    iEval (rewrite Eall) in "HnewNodes".
    iAssert (slk ↦* (ic_loc <$> client_run types kc))%I with "[Hsl_pre Hsl_suf Hsl_tail]" as "Hslice".
    { rewrite (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) (ic_loc <$> client_run types kc) Hsplitbnd). iFrame. }
    (* s.items[client] = newNodes: the key read borrows cl's node back from types2 *)
    have Hklt : (k < length cells)%nat by (apply lookup_lt_Some in Hcellk).
    have Hsck : split_cells cells k o rs !! k = Some leftCell.
    { rewrite Hsc /pre lookup_app_r; last (rewrite length_take; clear -Hklt; lia).
      rewrite length_take Nat.min_l; last (clear -Hklt; lia).
      have -> : (k - k)%nat = 0%nat by (clear -k; lia).
      reflexivity. }
    have Hlk2 : (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) !! parent = Some {| ty_cells := split_cells cells k o rs; ty_arr := arr |} by apply lookup_insert_eq.
    iDestruct (big_sepM_lookup_acc _ _ parent {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Hlk2 with "Htypes2") as "[(Hpc2 & %Harrinv2) Hclose2]".
    iDestruct "Hpc2" as (yt2 tl2) "(Hparent2 & Hdll2 & %Hlen2 & %Hrepr2 & %Hcpar2)".
    iDestruct (own_dll_acc (DfracOwn 1) (split_cells cells k o rs) yt2.(yjs.yType.start') tl2 k leftCell Hsck with "Hdll2") as (iv2 olid2 orid2) "(%Hcloc2 & %Hcl2 & %Hcr2 & %Hid2 & %Hcontent2 & %Holid2 & %Horid2 & %Hflags2 & %Hrun2 & %Hpar2 & Hcval2 & Hcol2 & Hcor2 & Hback2)".
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
    have Hkpcl : cell_kp leftCell = cell_kp cw.
    { rewrite /cell_kp /cell_pr Hcccl Hclcl Hclloc. reflexivity. }
    have Hkp : cell_kp <$> all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp rightCell].
    { etransitivity.
      { apply Permutation_map.
        exact (all_cells_insert types parent {| ty_cells := cells; ty_arr := arr |} {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Htypes). }
      simpl. rewrite Hsc.
      etransitivity; last first.
      { apply Permutation_app_tail. apply Permutation_map. symmetry.
        exact (all_cells_lookup types parent {| ty_cells := cells; ty_arr := arr |} Htypes). }
      simpl. rewrite -Hsplit !map_app /= Hkpcl -!app_assoc /=.
      apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    have Hbef : forall y, y ∈ take (kw + 1) (client_run types (cell_client rightCell)) -> ((cell_pr y).1 < (cell_pr rightCell).1)%Z.
    { move=> y Hy.
      rewrite Hcccr Hcwcc in Hy.
      apply list_elem_of_lookup_1 in Hy as [j Hj].
      apply lookup_take_Some in Hj as [Hj Hjlt].
      have Hple : (uint.Z (cell_clock y) <= uint.Z (cell_clock cw))%Z.
      { destruct (decide (j = kw)) as [-> | Hne].
        - rewrite Hkw in Hj. injection Hj as <-. lia.
        - exact (StronglySorted_lookup_le cell_le (client_run types kc) j kw y cw (client_run_sorted types kc) Hj Hkw ltac:(clear -Hjlt Hne; lia)). }
      rewrite /cell_pr /= Hccr_clock. clear -Hple Hopos. lia. }
    have Haft : forall y, y ∈ drop (kw + 1) (client_run types (cell_client rightCell)) -> ((cell_pr rightCell).1 < (cell_pr y).1)%Z.
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
    have Hrun_eq := client_run_loc_insert types (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) rightCell (kw + 1) Hkp Hclkloc Hbef Haft.
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
    have Hdecomp : forall c0, c0 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> c0 ∈ all_cells types \/ c0 = leftCell \/ c0 = rightCell.
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
    have HF2 : forall c, c ∈ all_cells types -> cell_client c = cell_client cw -> (cell_pr c).1 = (cell_pr rightCell).1 -> False.
    { move=> c Hc Hcc Hpr.
      rewrite /cell_pr /= Hccr_clock in Hpr.
      destruct (decide (c.(ic_loc) = cw.(ic_loc))) as [He | Hne].
      - have Heq : c = cw := HinjAll c cw Hc Hcwmem He.
        rewrite Heq in Hpr. clear -Hpr Hopos. lia.
      - destruct (Hdisj c Hc Hcc Hne) as [Hd | Hd].
        + clear -Hd Hpr Hopos. lia.
        + clear -Hd Hpr Hoinrun. lia. }
    have Hprcl : (cell_pr leftCell).1 = (cell_pr cw).1 by (rewrite /cell_pr /= Hclcl //).
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
        have Hne2 : client ≠ cell_client rightCell.
        { rewrite Hcccr Hcwcc. move=> Heqc. rewrite Heqc lookup_delete_eq in Hcs. discriminate. }
        rewrite (client_run_loc_other types (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) rightCell client Hkp Hclkloc Hne2). iFrame.
      - iPureIntro. split; [exact Hcomplete2 | exact Hclkloc2]. }
    wp_auto.
    have Hpool' : pool_invs (<[parent := MkTypeState (split_cells cells k o rs) arr]> types)
      := pool_invs_split types parent cells arr k cw o rs Htypes Hcellk Hrunwf0 Hdiff Hckbnd0 Hrsfresh Hpool.
    have Hreg' : registry_coh bind (<[parent := MkTypeState (split_cells cells k o rs) arr]> types)
      := registry_coh_insert bind types parent _ _ Htypes Hreg0.
    iApply ("HΦ" $! rs).
    iSplitL "Hclient Hclock HdeletedSet Hitemsf Hitemmap2 Hregistry Htypes2 Hpending Hpdeletes";
      last by (iPureIntro; split; [exact Hrsnn | exact Hrsfresh]).
    simpl.
    iApply (own_store_struct_intro _ (MkStoreState client0 k0 (<[parent := MkTypeState (split_cells cells k o rs) arr]> types) bind pend pdel)
              (conj Hpool' Hreg') with "Hclient Hclock HdeletedSet [Hitemsf Hitemmap2] Hregistry Htypes2 Hpending Hpdeletes").
    iExists mref. iFrame "Hitemsf Hitemmap2".
  - (* cw has a right neighbour d0: relink d0.left := right, then the same DLL
       split, ytype rebuild, getNodeIndex pin, and item-map surgery as the
       last-cell branch (suf = d0 :: drest threads through own_dll_split's cs2
       and the split_cells shape; the item-map tail is otherwise identical). *)
    iDestruct "Hrest" as (ivd olidd oridd) "(%Hlocd & %Hprevd & %Hpard & %Hidd & %Hcontentd & %Holidd & %Horidd & %Hflagsd & %Hrund & Hvald & Holeftd & Horightd & Hrestd)".
    destruct Hlocd as [Hlocd1 Hlocdnn].
    (* ----- guard (n.right ≠ nil): relink d0.left := right, then n.right := rs ----- *)
    rewrite (bool_decide_eq_false_2 (itemVal.(yjs.item.right') = null) Hlocdnn).
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
    set (leftCell := split_cell_left cw o).
    set (rightCell := split_cell_right cw o rs).
    set (originId := {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId');
                   yjs.id.clock' := word.sub (word.add itemVal.(yjs.item.id').(yjs.id.clock') diff) (W64 1) |}).
    have Hopos : (0 < o)%nat by (rewrite /o; lia).
    have Hnowrap_add : (uint.Z itemVal.(yjs.item.id').(yjs.id.clock') + uint.Z diff < 2^64)%Z.
    { rewrite -Hcwck. have H1 := Hnowrapcw. have H2 := Hdiff. word. }
    have Hadd_eq : (uint.nat itemVal.(yjs.item.id').(yjs.id.clock') + o)%nat = uint.nat (word.add itemVal.(yjs.item.id').(yjs.id.clock') diff).
    { rewrite /o. clear -Hnowrap_add. word. }
    have [xprev Hxprev] : is_Some (cw.(ic_run) !! (o - 1)%nat).
    { apply lookup_lt_is_Some. rewrite /o. lia. }
    have Hyo2 : cw.(ic_run) !! S (o - 1)%nat = Some yo.
    { replace (S (o - 1))%nat with o by (rewrite /o; lia). exact Hyo. }
    have Hstep := proj2 Hrun (o - 1)%nat xprev yo Hxprev Hyo2.
    have Horig : origin yo = itemPtr xprev by (destruct Hstep as [_ [Hh _]]; exact Hh).
    have Hxpid := run_wf_lookup_clock cw.(ic_run) (o - 1)%nat (run_head cw) xprev Hrun Hrun0 Hxprev.
    have Hcrorig : origin_id (origin (run_head rightCell)) = toYjsId <$> Some originId.
    { rewrite /rightCell Hrhcr Horig /origin_id /=. f_equal.
      rewrite Hxpid Hid /toYjsId /originId /=. f_equal. clear -Hnowrap_add Hdiff. word. }
    have Hrhck : clock (item_id (run_head cw)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clock') by (rewrite Hid /toYjsId /=).
    have Hclcl : cell_clock leftCell = cell_clock cw by (rewrite /leftCell /cell_clock Hrhcl).
    have Hcccl : cell_client leftCell = cell_client cw by (rewrite /leftCell /cell_client Hrhcl).
    have Hcccr : cell_client rightCell = cell_client cw by (rewrite /rightCell /cell_client Hrhcr Hyoid /=).
    have Hccr_clock : uint.Z (cell_clock rightCell) = (uint.Z (cell_clock cw) + Z.of_nat o)%Z.
    { rewrite /rightCell /cell_clock Hrhcr Hyoid /= Hrhck. clear -Hnowrap_add Hdiff. rewrite /o. word. }
    have Hsc : split_cells cells k o rs = pre ++ leftCell :: rightCell :: d0 :: drest.
    { rewrite /split_cells Hcellk. rewrite -/suf Hsufeq. reflexivity. }
    (* the split-cell struct values [ivl] (truncated cw) / [ivr] (right half) *)
    set (ivl := itemVal <| yjs.item.content' := {| yjs.content.content' := take (sint.nat diff) itemVal.(yjs.item.content').(yjs.content.content') |} |> <| yjs.item.right' := rs |>).
    set (ivr := {| yjs.item.id' := {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId'); yjs.id.clock' := word.add itemVal.(yjs.item.id').(yjs.id.clock') diff |};
                   yjs.item.originLeftId' := olid_ptr;
                   yjs.item.originRightId' := itemVal.(yjs.item.originRightId');
                   yjs.item.left' := cw.(ic_loc);
                   yjs.item.right' := itemVal.(yjs.item.right');
                   yjs.item.parent' := itemVal.(yjs.item.parent');
                   yjs.item.content' := {| yjs.content.content' := subslice (sint.nat diff) (sint.nat cbs.(slice.len)) itemVal.(yjs.item.content').(yjs.content.content') |};
                   yjs.item.flags' := itemVal.(yjs.item.flags') |}).
    have Hivl_ol : ivl.(yjs.item.originLeftId') = itemVal.(yjs.item.originLeftId') by (rewrite /ivl /=).
    have Hivl_or : ivl.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId') by (rewrite /ivl /=).
    have Hivl_left : ivl.(yjs.item.left') = ml by (rewrite /ivl /=; exact Hprev).
    have Hivr_r : ivr.(yjs.item.right') = itemVal.(yjs.item.right') by reflexivity.
    have Hrhcl' : run_head leftCell = run_head cw by (rewrite /leftCell; exact Hrhcl).
    have Hrhcr' : run_head rightCell = yo by (rewrite /rightCell; exact Hrhcr).
    have Hrhcli : clientId (item_id (run_head cw)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clientId') by (rewrite Hid /toYjsId /=).
    have Hclloc : ic_loc leftCell = cw.(ic_loc) by (rewrite /leftCell /=).
    have Hcrloc : ic_loc rightCell = rs by (rewrite /rightCell /=).
    have Hivr_ol : ivr.(yjs.item.originLeftId') = olid_ptr by (rewrite /ivr /=).
    have Hivr_or : ivr.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId') by (rewrite /ivr /=).
    have Hp1 : ic_loc leftCell ≠ null by (rewrite /leftCell /=; exact Hmfnn).
    have Hp2 : ic_loc rightCell ≠ null by (rewrite /rightCell /=; exact Hrsnn).
    have Hp4 : ivl.(yjs.item.right') = ic_loc rightCell by (rewrite /ivl /rightCell /=).
    have Hp5 : ivl.(yjs.item.parent') = ic_parent leftCell by (rewrite /ivl /leftCell /=; exact Hpar).
    have Hp6 : item_id (run_head leftCell) = toYjsId ivl.(yjs.item.id'). { rewrite Hrhcl' /ivl /=. exact Hid. }
    have Hp7 : content <$> ic_run leftCell = explode (toContent ivl.(yjs.item.content')). { rewrite /leftCell /ivl /toContent /=. exact Hcontl. }
    have Hp8 : origin_id (origin (run_head leftCell)) = toYjsId <$> olidcw. { rewrite Hrhcl'. exact Holid. }
    have Hp9 : origin_id (rightOrigin (run_head leftCell)) = toYjsId <$> oridcw. { rewrite Hrhcl'. exact Horid. }
    have Hp10 : ivl.(yjs.item.flags') = (if ic_deleted leftCell then W8 6 else W8 2). { rewrite /ivl /leftCell /=. exact Hflags. }
    have Hp11 : run_wf (ic_run leftCell). { rewrite /leftCell /=. exact (run_wf_take cw.(ic_run) o Hopos Hrun). }
    have Hp12 : ivr.(yjs.item.left') = ic_loc leftCell. { rewrite /ivr /leftCell /=. reflexivity. }
    have Hp13 : ivr.(yjs.item.parent') = ic_parent rightCell. { rewrite /ivr /rightCell /=. exact Hpar. }
    have Hp14 : item_id (run_head rightCell) = toYjsId ivr.(yjs.item.id'). { rewrite Hrhcr' Hyoid /ivr /toYjsId /=. rewrite Hrhck Hrhcli Hadd_eq. reflexivity. }
    have Hp15 : content <$> ic_run rightCell = explode (toContent ivr.(yjs.item.content')). { rewrite /rightCell /ivr /toContent /= Hsubdrop. exact Hcontr. }
    have Hp17 : origin_id (rightOrigin (run_head rightCell)) = toYjsId <$> oridcw. { rewrite Hrhcr' Hyoro. exact Horid. }
    have Hp18 : ivr.(yjs.item.flags') = (if ic_deleted rightCell then W8 6 else W8 2). { rewrite /ivr /rightCell /=. exact Hflags. }
    have Hp19 : run_wf (ic_run rightCell). { rewrite /rightCell /=. exact (run_wf_drop cw.(ic_run) o Hoinrun Hrun). }
    (* ----- read the client run slice (map.lookup1), BEFORE Phase A locks cw ----- *)
    iDestruct "Hitemmap" as (gm) "(Hmap & Hruns & %Hcomplete & %Hclkloc)".
    set (kc := itemVal.(yjs.item.id').(yjs.id.clientId')).
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
    (* ----- Phase A: reassemble the suffix DLL behind [rightCell], own_dll_split, close ----- *)
    iAssert (own_dll (DfracOwn 1) itemVal.(yjs.item.right') tl0 rs null (d0 :: drest))
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
      iApply (own_dll_split (DfracOwn 1) pre (d0 :: drest) leftCell rightCell ivl ivr olidcw oridcw (Some originId) oridcw yt.(yjs.yType.start') tl0 ml Hp1 Hp2 Hivl_left Hp4 Hp5 Hp6 Hp7 Hp8 Hp9 Hp10 Hp11 Hp12 Hp13 Hp14 Hp15 Hcrorig Hp17 Hp18 Hp19).
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
      - apply elem_of_cons in Hc as [-> | Hc]; [rewrite /leftCell /=; exact Hcparcw |].
        apply elem_of_cons in Hc as [-> | Hc]; [rewrite /rightCell /=; exact Hcparcw |].
        apply Hcpar0. rewrite -Hsplit. apply elem_of_app; right.
        apply elem_of_cons; right. exact Hc. }
    iAssert (own_ytype_cells parent (DfracOwn 1) (split_cells cells k o rs) arr) with "[Hparent Hdll2]" as "Hyt2".
    { iExists yt, tl0. iFrame "Hparent Hdll2". iPureIntro. split_and!.
      - rewrite (split_cells_num_visible cells k o rs cw Hcellk). exact Hlen0.
      - rewrite /cells_repr (split_cells_flatten cells k o rs cw Hcellk). exact Hrepr0.
      - exact Hcpar_split. }
    iAssert (own_type_pool (DfracOwn 1) (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types))%I with "[Hyt2 Hrestmap]" as "Htypes2".
    { rewrite /own_type_pool -insert_delete_eq big_sepM_insert_delete delete_delete_eq.
      iFrame "Hrestmap". simpl. iFrame "Hyt2". iPureIntro. exact Harrinv. }
    (* ----- getNodeIndex over the split run [run_half] = client_run with cw -> leftCell ----- *)
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
    have Hss_half : StronglySorted cell_le (<[kw := leftCell]> (client_run types kc)) := Hss_replace (client_run types kc) kw cw leftCell (client_run_sorted types kc) Hkw Hclcl.
    set (run_half := <[kw := leftCell]> (client_run types kc)).
    have HndAll : NoDup (all_cells types) := NoDup_fmap_1 ic_loc _ Hnodup.
    have Hndrun : NoDup (client_run types kc).
    { rewrite /client_run (merge_sort_Permutation cell_le _). apply NoDup_filter. exact HndAll. }
    have Hkwlt : (kw < length (client_run types kc))%nat by (apply lookup_lt_Some in Hkw; exact Hkw).
    have Hlockw : (ic_loc <$> client_run types kc) !! kw = Some (ic_loc leftCell).
    { rewrite list_lookup_fmap Hkw /=. done. }
    have Hlocs : ic_loc <$> run_half = ic_loc <$> client_run types kc.
    { rewrite /run_half list_fmap_insert (list_insert_id _ _ _ Hlockw) //. }
    have Hkw_half : run_half !! kw = Some leftCell.
    { rewrite /run_half. apply list_lookup_insert_Some. left. split_and!; [reflexivity | reflexivity | exact Hkwlt]. }
    have Hclk_half : cell_clock leftCell = itemVal.(yjs.item.id').(yjs.id.clock') by (rewrite Hclcl Hcwck).
    have Hsub : ∀ c, c ∈ run_half → c = leftCell ∨ c ∈ client_run types kc.
    { move=> c Hc. apply list_elem_of_lookup_1 in Hc as [j Hj]. rewrite /run_half in Hj.
      apply list_lookup_insert_Some in Hj as [(_ & <- & _) | (_ & Hj)]; [by left | right; exact (list_elem_of_lookup_2 _ _ _ Hj)]. }
    have Hfits_half : ∀ c, c ∈ run_half → (uint.Z (cell_clock c) + length (ic_run c) < 2^64)%Z.
    { move=> c Hc. destruct (Hsub c Hc) as [-> | HcL].
      - rewrite Hclcl /leftCell /= length_take. have H := Hnowrapcw. lia.
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
    (* pin [uint.nat idx = kw]: the covering cell in [run_half] is [leftCell] (NoDup locs) *)
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
    have Hclcli : cell_client leftCell = cell_client cw by (rewrite /leftCell /cell_client Hrhcl).
    have Hrun_half : sorted_client_run (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) kc run_half.
    { split_and!; [exact Hss_half | rewrite Hlocs; exact HndLocRun |].
      move=> c Hc. apply client_run_mem. split; [exact (Hmem_half c Hc) |].
      destruct (Hsub c Hc) as [-> | HcL]; [rewrite Hclcli; exact Hcwcc |].
      exact (proj2 (proj1 (client_run_mem types kc c) HcL)). }
    have Hpool2 : pool_invs (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types)
      := pool_invs_split types parent cells arr k cw o rs Htypes Hcellk Hrun Hdiff Hckbnd Hrsfresh Hpool.
    iEval (rewrite -Hlocs) in "Hslice".
    wp_apply (wp_getNodeIndex slk (DfracOwn 1) (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) kc run_half (itemVal.(yjs.item.id').(yjs.id.clock')) Hrun_half Hpool2 with "[$Hslice $Htypes2]").
    iIntros (idx ok) "(Hslice & Htypes2 & %Hires)".
    iDestruct (own_type_pool_id_bounds with "Htypes2") as %Hbnds2.
    have Hlcbnd := proj2 (Hbnds2 leftCell (Hmem_half leftCell (list_elem_of_lookup_2 _ _ _ Hkw_half))).
    have Hlccov : cell_covers_clock leftCell (uint.nat itemVal.(yjs.item.id').(yjs.id.clock')).
    { have Hlen : (0 < length (ic_run leftCell))%nat.
      { rewrite /leftCell /split_cell_left /= length_take /o. lia. }
      move: Hclk_half. rewrite /cell_clock /cell_covers_clock. move=> Hclk. split; word. }
    destruct ok; last first.
    { exfalso. exact (Hires leftCell (list_elem_of_lookup_2 _ _ _ Hkw_half) Hlccov). }
    destruct Hires as (cres & Hcres & Hcov).
    have Hcresbnd := proj2 (Hbnds2 cres (Hmem_half cres (list_elem_of_lookup_2 _ _ _ Hcres))).
    have Hcresle : (uint.Z (cell_clock cres) <= uint.Z itemVal.(yjs.item.id').(yjs.id.clock'))%Z.
    { destruct Hcov as [H1 _]. rewrite /cell_clock. word. }
    have Hcreslt : (uint.Z itemVal.(yjs.item.id').(yjs.id.clock') < uint.Z (cell_clock cres) + Z.of_nat (length (ic_run cres)))%Z.
    { destruct Hcov as [_ H2]. rewrite /cell_clock. word. }
    have Hcresmem : cres ∈ run_half := list_elem_of_lookup_2 _ _ _ Hcres.
    have Hcresloc : ic_loc cres = ic_loc leftCell.
    { destruct (Hsub cres Hcresmem) as [-> | HcresL]; [reflexivity |].
      have Hcresall : cres ∈ all_cells types := proj1 (proj1 (client_run_mem types kc cres) HcresL).
      have Hcrescc : cell_client cres = cell_client cw.
      { rewrite (proj2 (proj1 (client_run_mem types kc cres) HcresL)) -Hcwcc //. }
      destruct (decide (ic_loc cres = ic_loc cw)) as [Heq | Hne].
      - rewrite Heq Hclloc //.
      - exfalso. rewrite -Hcwck in Hcresle Hcreslt.
        destruct (Hdisj cres Hcresall Hcrescc Hne) as [Hd | Hd]; lia. }
    have Hidxloc : (ic_loc <$> run_half) !! (uint.nat idx) = Some (ic_loc leftCell) by (rewrite list_lookup_fmap Hcres /= Hcresloc //).
    have Hkwloc : (ic_loc <$> run_half) !! kw = Some (ic_loc leftCell) by (rewrite list_lookup_fmap Hkw_half //).
    have HndLocRunHalf : NoDup (ic_loc <$> run_half) by (rewrite Hlocs; exact HndLocRun).
    have Hidxkw : uint.nat idx = kw := NoDup_lookup _ _ _ _ HndLocRunHalf Hidxloc Hkwloc.
    have Hcrescl : cres = leftCell.
    { have Htmp : run_half !! kw = Some cres by (rewrite -Hidxkw; exact Hcres). congruence. }
    iEval (rewrite Hlocs) in "Hslice".
    (* ----- the append-based item-map surgery (no length-fit side condition:
       append's growth is modeled with an overflow assume, so no client-run
       capacity premise is needed, unlike a pre-sized make) ----- *)
    iDestruct (own_slice_len with "Hslice") as %[Hslklen Hslklen0].
    rewrite length_fmap in Hslklen Hslklen0.
    have Hkwlt2 : (kw < length (client_run types kc))%nat by (apply lookup_lt_Some in Hkw).
    have Hidxsint : sint.Z idx = Z.of_nat kw by (move: Hslklen Hslklen0 Hkwlt2; rewrite -Hidxkw => ? ? ?; word).
    wp_auto.
    iDestruct (own_slice_wf with "Hslice") as %Hslkwf.
    (* newNodes = append(nil, nodes[:index+1]...) *)
    rewrite decide_True; last word.
    wp_auto.
    have Hsplitbnd : (0 ≤ sint.Z (w64_word_instance.(word.add) idx (W64 1)) ≤ sint.Z slk.(slice.len) ≤ sint.Z slk.(slice.len))%Z by word.
    iDestruct (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) (ic_loc <$> client_run types kc) Hsplitbnd with "Hslice") as "(Hsl_pre & Hsl_suf & Hsl_tail)".
    iAssert (slice.nil ↦* ([] : list loc))%I with "[]" as "Hnil0"; first iApply own_slice_nil.
    iAssert (own_slice_cap loc slice.nil (DfracOwn 1))%I with "[]" as "Hnilcap"; first iApply own_slice_cap_nil.
    wp_apply (wp_slice_append with "[Hnil0 Hnilcap Hsl_pre]"); first (iFrame "Hnil0 Hnilcap Hsl_pre").
    iIntros (sl1) "(Hsl1 & Hsl1cap & Hsl_pre)".
    wp_auto.
    (* newNodes = append(newNodes, right) *)
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "%slit [Hslit _]". wp_auto.
    wp_apply (wp_slice_append with "[Hsl1 Hsl1cap Hslit]"); first (iFrame "Hsl1 Hsl1cap Hslit").
    iIntros (sl2) "(Hsl2 & Hsl2cap & _)".
    wp_auto.
    (* newNodes = append(newNodes, nodes[index+1:]...) *)
    rewrite decide_True; last word.
    wp_auto.
    wp_apply (wp_slice_append with "[Hsl2 Hsl2cap Hsl_suf]"); first (iFrame "Hsl2 Hsl2cap Hsl_suf").
    iIntros (newSl) "(HnewNodes & HnewCap & Hsl_suf)".
    wp_auto.
    have HnkB : sint.nat (w64_word_instance.(word.add) idx (W64 1)) = (kw + 1)%nat.
    { move: Hslklen Hslklen0 Hkwlt2 Hidxsint => ? ? ? ?. word. }
    have Esrc : subslice (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (sint.nat slk.(slice.len)) (ic_loc <$> client_run types kc) = drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite HnkB -Hslklen /subslice take_ge; [reflexivity | rewrite length_fmap; clear -Hkwlt2; lia]. }
    have Elit : <[sint.nat (W64 0) := rs]> ([null] : list loc) = [rs].
    { have -> : sint.nat (W64 0) = 0%nat by word. reflexivity. }
    have Eall : (([] ++ take (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (ic_loc <$> client_run types kc)) ++ <[sint.nat (W64 0) := rs]> ([null] : list loc)) ++ subslice (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (sint.nat slk.(slice.len)) (ic_loc <$> client_run types kc) = take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite Esrc Elit HnkB app_nil_l -app_assoc /=. reflexivity. }
    iEval (rewrite Eall) in "HnewNodes".
    iAssert (slk ↦* (ic_loc <$> client_run types kc))%I with "[Hsl_pre Hsl_suf Hsl_tail]" as "Hslice".
    { rewrite (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) (ic_loc <$> client_run types kc) Hsplitbnd). iFrame. }
    (* s.items[client] = newNodes: the key read borrows cl's node back from types2 *)
    have Hklt : (k < length cells)%nat by (apply lookup_lt_Some in Hcellk).
    have Hsck : split_cells cells k o rs !! k = Some leftCell.
    { rewrite Hsc /pre lookup_app_r; last (rewrite length_take; clear -Hklt; lia).
      rewrite length_take Nat.min_l; last (clear -Hklt; lia).
      have -> : (k - k)%nat = 0%nat by (clear -k; lia).
      reflexivity. }
    have Hlk2 : (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) !! parent = Some {| ty_cells := split_cells cells k o rs; ty_arr := arr |} by apply lookup_insert_eq.
    iDestruct (big_sepM_lookup_acc _ _ parent {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Hlk2 with "Htypes2") as "[(Hpc2 & %Harrinv2) Hclose2]".
    iDestruct "Hpc2" as (yt2 tl2) "(Hparent2 & Hdll3 & %Hlen2 & %Hrepr2 & %Hcpar2)".
    iDestruct (own_dll_acc (DfracOwn 1) (split_cells cells k o rs) yt2.(yjs.yType.start') tl2 k leftCell Hsck with "Hdll3") as (iv2 olid2 orid2) "(%Hcloc2 & %Hcl2 & %Hcr2 & %Hid2 & %Hcontent2 & %Holid2 & %Horid2 & %Hflags2 & %Hrun2 & %Hpar2 & Hcval2 & Hcol2 & Hcor2 & Hback2)".
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
    have Hkpcl : cell_kp leftCell = cell_kp cw.
    { rewrite /cell_kp /cell_pr Hcccl Hclcl Hclloc. reflexivity. }
    have Hkp : cell_kp <$> all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp rightCell].
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
    have Hbef : forall y, y ∈ take (kw + 1) (client_run types (cell_client rightCell)) -> ((cell_pr y).1 < (cell_pr rightCell).1)%Z.
    { move=> y Hy.
      rewrite Hcccr Hcwcc in Hy.
      apply list_elem_of_lookup_1 in Hy as [j Hj].
      apply lookup_take_Some in Hj as [Hj Hjlt].
      have Hple : (uint.Z (cell_clock y) <= uint.Z (cell_clock cw))%Z.
      { destruct (decide (j = kw)) as [-> | Hne].
        - rewrite Hkw in Hj. injection Hj as <-. lia.
        - exact (StronglySorted_lookup_le cell_le (client_run types kc) j kw y cw (client_run_sorted types kc) Hj Hkw ltac:(clear -Hjlt Hne; lia)). }
      rewrite /cell_pr /= Hccr_clock. clear -Hple Hopos. lia. }
    have Haft : forall y, y ∈ drop (kw + 1) (client_run types (cell_client rightCell)) -> ((cell_pr rightCell).1 < (cell_pr y).1)%Z.
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
    have Hrun_eq := client_run_loc_insert types (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) rightCell (kw + 1) Hkp Hclkloc Hbef Haft.
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
    have Hdecomp : forall c0, c0 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> c0 ∈ all_cells types \/ c0 = leftCell \/ c0 = rightCell.
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
    have HF2 : forall c, c ∈ all_cells types -> cell_client c = cell_client cw -> (cell_pr c).1 = (cell_pr rightCell).1 -> False.
    { move=> c Hc Hcc Hpr.
      rewrite /cell_pr /= Hccr_clock in Hpr.
      destruct (decide (c.(ic_loc) = cw.(ic_loc))) as [He | Hne].
      - have Heq : c = cw := HinjAll c cw Hc Hcwmem He.
        rewrite Heq in Hpr. clear -Hpr Hopos. lia.
      - destruct (Hdisj c Hc Hcc Hne) as [Hd | Hd].
        + clear -Hd Hpr Hopos. lia.
        + clear -Hd Hpr Hoinrun. lia. }
    have Hprcl : (cell_pr leftCell).1 = (cell_pr cw).1 by (rewrite /cell_pr /= Hclcl //).
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
        have Hne2 : client ≠ cell_client rightCell.
        { rewrite Hcccr Hcwcc. move=> Heqc. rewrite Heqc lookup_delete_eq in Hcs. discriminate. }
        rewrite (client_run_loc_other types (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) rightCell client Hkp Hclkloc Hne2). iFrame.
      - iPureIntro. split; [exact Hcomplete2 | exact Hclkloc2]. }
    wp_auto.
    have Hpool' : pool_invs (<[parent := MkTypeState (split_cells cells k o rs) arr]> types)
      := pool_invs_split types parent cells arr k cw o rs Htypes Hcellk Hrunwf0 Hdiff Hckbnd0 Hrsfresh Hpool.
    have Hreg' : registry_coh bind (<[parent := MkTypeState (split_cells cells k o rs) arr]> types)
      := registry_coh_insert bind types parent _ _ Htypes Hreg0.
    iApply ("HΦ" $! rs).
    iSplitL "Hclient Hclock HdeletedSet Hitemsf Hitemmap2 Hregistry Htypes2 Hpending Hpdeletes";
      last by (iPureIntro; split; [exact Hrsnn | exact Hrsfresh]).
    simpl.
    iApply (own_store_struct_intro _ (MkStoreState client0 k0 (<[parent := MkTypeState (split_cells cells k o rs) arr]> types) bind pend pdel)
              (conj Hpool' Hreg') with "Hclient Hclock HdeletedSet [Hitemsf Hitemmap2] Hregistry Htypes2 Hpending Hpdeletes").
    iExists mref. iFrame "Hitemsf Hitemmap2".
Qed.



(** [store.splitAtAndGetLeft], general splitting form (issue #28 stage D1b):
    the id may address ANY char of the witness cell's run. When it is the
    run's LAST char the node already ends there and nothing changes;
    otherwise the node is split just after the id ([splitNode] at offset+1)
    and the truncated-in-place left half comes back (same location). Either
    way the returned node's run ends exactly at [idv]: the clean-end
    boundary the C2 flip feeds to Integrate as the left cursor. Local: the
    stepping stone of [wp_store__splitAtAndGetLeft], over the cursor cell's
    coordinates ([parent], [k]). *)
#[local] Lemma wp_store__splitAtAndGetLeft_range (s : loc) (idv : yjs.id.t)
    (st : store_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell) :
  ss_types st !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  cell_client cw = idv.(yjs.id.clientId') ->
  (uint.Z (cell_clock cw) <= uint.Z idv.(yjs.id.clock'))%Z ->
  (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  {{{ is_pkg_init yjs ∗ own_store_struct s st }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetLeft" #idv
  {{{ (types' : gmap loc type_state), RET (#(ic_loc cw), #true);
      own_store_struct s (st <| ss_types := types' |>) ∗
      ⌜((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat = (length (ic_run cw) - 1)%nat ∧
        types' = ss_types st)
       ∨ (((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) < length (ic_run cw) - 1)%nat ∧
          ∃ rloc : loc, rloc ≠ null ∧ rloc ∉ (ic_loc <$> all_cells (ss_types st)) ∧
            types' = <[parent := MkTypeState
              (split_cells cells k ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc)
              arr]> (ss_types st))⌝ }}}.
Proof using Type*.
  move=> Htypes Hcellk Hcwcc Hcwle Hcwlt.
  destruct st as [client0 k0 types bind pend pdel]. simpl in *.
  iIntros (Φ) "(#Hpkg & Hcells) HΦ".
  iDestruct "Hcells" as "(Hfields0 & %Hinvs0)".
  have Hpool : pool_invs types := proj1 Hinvs0.
  have [Hrunfits [Hnodup [Hrangedisj Horiginclk]]] := Hpool.
  iDestruct "Hfields0" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  have Hcwmem : cw ∈ all_cells types.
  { apply all_cells_elem_of. exists parent, (MkTypeState cells arr).
    split; [exact Htypes | exact (list_elem_of_lookup_2 _ _ _ Hcellk)]. }
  wp_method_call. wp_call. wp_call. wp_auto.
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbnds0.
  have Hcwcov : pool_cell_covers types cw (toYjsId idv).
  { split; [exact Hcwmem |].
    apply (cell_covers_w64 cw idv (proj1 (Hbnds0 cw Hcwmem)) (proj2 (Hbnds0 cw Hcwmem)) (proj1 Hpool cw Hcwmem)).
    split_and!; [exact Hcwcc | exact Hcwle | exact Hcwlt]. }
  iDestruct (own_store_struct_intro _ (MkStoreState client0 k0 types bind pend pdel) Hinvs0 with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
  wp_apply (wp_store__GetNode s idv (MkStoreState client0 k0 types bind pend pdel) with "[$Hcells]").
  iIntros (nl ok) "(Hcells & %Hres)". simpl in Hres.
  iDestruct "Hcells" as "(Hfields1 & %Hinvs1)".
  iDestruct "Hfields1" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  destruct ok; last first.
  { exfalso. exact (Hres cw Hcwcov). }
  destruct Hres as (cres & Hcrescov & Hcresloc).
  have Hnleq : nl = ic_loc cw.
  { rewrite -Hcresloc.
    exact (pool_cell_covers_loc types cres cw (toYjsId idv) Hpool (λ c Hc, proj2 (Hbnds0 c Hc)) Hcrescov Hcwcov). }
  clear Hcresloc. subst nl.
  wp_auto.
  iDestruct (own_type_pool_acc types cw Hcwmem with "Htypes") as "Hacc".
  iNamed "Hacc".
  have Hnwcw := Hrunfits cw Hcwmem. rewrite /cell_fits in Hnwcw.
  have Hcwck : cell_clock cw = itemVal.(yjs.item.id').(yjs.id.clock')
    by (rewrite /cell_clock Hid /toYjsId /=; word).
  have HlenEq : length (itemVal.(yjs.item.content').(yjs.content.content')) = length (ic_run cw).
  { have H := f_equal length Hcontent.
    rewrite length_fmap explode_length /toContent in H. lia. }
  have Hlenpos : (1 <= Z.of_nat (length (ic_run cw)))%Z.
  { have [Hne0 _] := Hrun. destruct (ic_run cw) as [|? ?]; [done | simpl; lia]. }
  have Hosub : uint.Z (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
             = Z.of_nat (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat.
  { rewrite -Hcwck. clear -Hcwle. word. }
  have Holt : ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) < length (ic_run cw))%nat.
  { clear -Hcwle Hcwlt. word. }
  wp_auto.
  wp_apply (wp_item__Len (ic_loc cw) (DfracOwn 1) itemVal with "[$Hval]"). iIntros "Hval".
  rewrite HlenEq.
  wp_auto.
  wp_if_destruct.
  - (* offset = Len-1: the run already ends at [idv]; no split *)
    iDestruct ("Hback" with "Hval") as "Htypes".
    iApply ("HΦ" $! types). simpl.
    iSplitL "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes"; last by (iPureIntro; left; split; [word | reflexivity]).
    iApply (own_store_struct_intro _ (MkStoreState client0 k0 types bind pend pdel) Hinvs1 with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes").
  - (* the id sits strictly inside the run: split just after it *)
    iDestruct ("Hback" with "Hval") as "Htypes".
    have Hnlt : ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) < length (ic_run cw) - 1)%nat.
    { word. }
    have Hdiffnat : uint.nat (w64_word_instance.(word.add)
                      (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                      (W64 1))
                  = ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1)%nat.
    { clear -Hosub Hnlt Hnwcw Hlenpos. word. }
    have Hdiffb : (0 < uint.nat (w64_word_instance.(word.add)
                      (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                      (W64 1)) < length (ic_run cw))%nat.
    { rewrite Hdiffnat. clear -Hnlt. lia. }
    iDestruct (own_store_struct_intro _ (MkStoreState client0 k0 types bind pend pdel) Hinvs1 with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
    wp_apply (wp_store__splitNode s (MkStoreState client0 k0 types bind pend pdel) parent cells arr k cw
                (w64_word_instance.(word.add)
                   (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                   (W64 1))
                Htypes Hcellk Hdiffb
                with "[$Hcells]").
    iIntros (rloc) "(Hcells & %Hrlocfresh')". simpl in Hrlocfresh'.
    have [Hrlocnn Hrlocfresh] := Hrlocfresh'.
    wp_auto.
    iApply ("HΦ" $! (<[parent := MkTypeState (split_cells cells k (uint.nat (w64_word_instance.(word.add)
                   (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                   (W64 1))) rloc) arr]> types)).
    iEval (simpl) in "Hcells". simpl. iFrame "Hcells".
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
    the C2 flip feeds to Integrate as the right cursor. Local: the stepping
    stone of [wp_store__splitAtAndGetRight], over the cursor cell's
    coordinates ([parent], [k]). *)
#[local] Lemma wp_store__splitAtAndGetRight_range (s : loc) (idv : yjs.id.t)
    (st : store_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell) :
  ss_types st !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  cell_client cw = idv.(yjs.id.clientId') ->
  (uint.Z (cell_clock cw) <= uint.Z idv.(yjs.id.clock'))%Z ->
  (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  {{{ is_pkg_init yjs ∗ own_store_struct s st }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetRight" #idv
  {{{ (rl : loc) (types' : gmap loc type_state), RET (#rl, #true);
      own_store_struct s (st <| ss_types := types' |>) ∗
      ⌜((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat = 0%nat ∧
        rl = ic_loc cw ∧ types' = ss_types st)
       ∨ ((0 < (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)))%nat ∧
          rl ≠ null ∧ rl ∉ (ic_loc <$> all_cells (ss_types st)) ∧
          types' = <[parent := MkTypeState
            (split_cells cells k (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl)
            arr]> (ss_types st))⌝ }}}.
Proof using Type*.
  move=> Htypes Hcellk Hcwcc Hcwle Hcwlt.
  destruct st as [client0 k0 types bind pend pdel]. simpl in *.
  iIntros (Φ) "(#Hpkg & Hcells) HΦ".
  iDestruct "Hcells" as "(Hfields0 & %Hinvs0)".
  have Hpool : pool_invs types := proj1 Hinvs0.
  have [Hrunfits [Hnodup [Hrangedisj Horiginclk]]] := Hpool.
  iDestruct "Hfields0" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  have Hcwmem : cw ∈ all_cells types.
  { apply all_cells_elem_of. exists parent, (MkTypeState cells arr).
    split; [exact Htypes | exact (list_elem_of_lookup_2 _ _ _ Hcellk)]. }
  wp_method_call. wp_call. wp_call. wp_auto.
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbnds0.
  have Hcwcov : pool_cell_covers types cw (toYjsId idv).
  { split; [exact Hcwmem |].
    apply (cell_covers_w64 cw idv (proj1 (Hbnds0 cw Hcwmem)) (proj2 (Hbnds0 cw Hcwmem)) (proj1 Hpool cw Hcwmem)).
    split_and!; [exact Hcwcc | exact Hcwle | exact Hcwlt]. }
  iDestruct (own_store_struct_intro _ (MkStoreState client0 k0 types bind pend pdel) Hinvs0 with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
  wp_apply (wp_store__GetNode s idv (MkStoreState client0 k0 types bind pend pdel) with "[$Hcells]").
  iIntros (nl ok) "(Hcells & %Hres)". simpl in Hres.
  iDestruct "Hcells" as "(Hfields1 & %Hinvs1)".
  iDestruct "Hfields1" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  destruct ok; last first.
  { exfalso. exact (Hres cw Hcwcov). }
  destruct Hres as (cres & Hcrescov & Hcresloc).
  have Hnleq : nl = ic_loc cw.
  { rewrite -Hcresloc.
    exact (pool_cell_covers_loc types cres cw (toYjsId idv) Hpool (λ c Hc, proj2 (Hbnds0 c Hc)) Hcrescov Hcwcov). }
  clear Hcresloc. subst nl.
  wp_auto.
  iDestruct (own_type_pool_acc types cw Hcwmem with "Htypes") as "Hacc".
  iNamed "Hacc".
  have Hnwcw := Hrunfits cw Hcwmem. rewrite /cell_fits in Hnwcw.
  have Hcwck : cell_clock cw = itemVal.(yjs.item.id').(yjs.id.clock')
    by (rewrite /cell_clock Hid /toYjsId /=; word).
  have Hlenpos : (1 <= Z.of_nat (length (ic_run cw)))%Z.
  { have [Hne0 _] := Hrun. destruct (ic_run cw) as [|? ?]; [done | simpl; lia]. }
  have Hosub : uint.Z (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
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
    have Hdiffnat : uint.nat (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                  = (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat.
    { clear -Hosub. word. }
    have Hdiffb : (0 < uint.nat (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                   < length (ic_run cw))%nat.
    { rewrite Hdiffnat. clear -Hopos Holt. lia. }
    iDestruct (own_store_struct_intro _ (MkStoreState client0 k0 types bind pend pdel) Hinvs1 with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
    wp_apply (wp_store__splitNode s (MkStoreState client0 k0 types bind pend pdel) parent cells arr k cw
                (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                Htypes Hcellk Hdiffb
                with "[$Hcells]").
    iIntros (rloc) "(Hcells & %Hrlocfresh')". simpl in Hrlocfresh'.
    have [Hrlocnn Hrlocfresh] := Hrlocfresh'.
    wp_auto.
    iApply ("HΦ" $! rloc (<[parent := MkTypeState (split_cells cells k
                (uint.nat (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock')))
                rloc) arr]> types)).
    iEval (simpl) in "Hcells". simpl. iFrame "Hcells".
    iPureIntro. right. split.
    { exact Hopos. }
    split_and!; [exact Hrlocnn | exact Hrlocfresh |].
    rewrite Hdiffnat //.
  - (* offset = 0: the run already starts at [idv]; no split *)
    iDestruct ("Hback" with "Hval") as "Htypes".
    iApply ("HΦ" $! (ic_loc cw) types). simpl.
    iSplitL "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes"; last by (iPureIntro; left; split_and!; [word | reflexivity | reflexivity]).
    iApply (own_store_struct_intro _ (MkStoreState client0 k0 types bind pend pdel) Hinvs1 with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes").
Qed.

(** Every post-split cell's clock range sits inside a same-client cell of the
    original pool (the halves inside the split cell, the rest inside itself);
    this is what transports the range-form freshness facts across a split. *)
Lemma split_pool_subrange (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z ->
  cell_fits cw ->
  ∀ c', c' ∈ all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types) ->
    ∃ c, c ∈ all_cells types ∧ cell_client c' = cell_client c ∧
      (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
      (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')) <=
       uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z.
Proof.
  move=> Htypes Hck Hrunwf Ho Hckbnd Hfitscw c' Hc'.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck)
    as (rest & Hold & Hnew).
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  have HclkZ : uint.Z (cell_clock cw) = Z.of_nat (clock (item_id (run_head cw))).
  { rewrite /cell_clock. word. }
  rewrite Hnew in Hc'.
  apply elem_of_cons in Hc' as [-> | Hc'].
  { exists cw. split_and!.
    - rewrite Hold. apply list_elem_of_here.
    - exact Hclientl.
    - rewrite Hclockl. lia.
    - rewrite Hclockl Hlenl. lia. }
  apply elem_of_cons in Hc' as [-> | Hc'].
  { have Hzr : (uint.Z (cell_clock (split_cell_right cw o rloc))
               = Z.of_nat (clock (item_id (run_head cw)) + o))%Z.
    { rewrite Hclockr.
      have Hbo : (Z.of_nat (clock (item_id (run_head cw)) + o) < 2^64)%Z.
      { rewrite /cell_fits in Hfitscw. clear -HclkZ Hfitscw Ho Hckbnd. lia. }
      clear -Hbo. word. }
    exists cw. split_and!.
    - rewrite Hold. apply list_elem_of_here.
    - exact Hclientr.
    - rewrite Hzr. lia.
    - rewrite Hzr Hlenr. lia. }
  { exists c'. split_and!.
    - rewrite Hold. apply elem_of_cons. by right.
    - done.
    - lia.
    - lia. }
Qed.

(** [store.splitAtAndGetLeft]: make the char [idv] (any char of the pool
    cell [cw]) end a node. When it is the run's last char nothing changes;
    otherwise the node is split just after it and the truncated left half
    keeps the location. The node at [ic_loc cw] then starts where [cw] did
    and ends at [idv]. *)
Lemma wp_store__splitAtAndGetLeft (s : loc) (idv : yjs.id.t) (st : store_state) (cw : item_cell) :
  pool_cell_covers (ss_types st) cw (toYjsId idv) ->
  {{{ is_pkg_init yjs ∗ own_store_struct s st }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetLeft" #idv
  {{{ (types' : gmap loc type_state), RET (#(ic_loc cw), #true);
      own_store_struct s (st <| ss_types := types' |>) ∗
      ⌜split_types_update_rel (ss_types st) types' cw⌝ ∗
      ⌜cell_starts_at types' (ic_parent cw) (ic_loc cw) (item_id (run_head cw))⌝ ∗
      ⌜cell_ends_at types' (ic_parent cw) (ic_loc cw) (toYjsId idv)⌝ }}}.
Proof using Type*.
  move=> Hcov.
  destruct st as [client0 k0 types bind pend pdel]. simpl in *.
  have [Hcwmem Hcwcov] := Hcov.
  iIntros (Φ) "(#Hpkg & Hcells) HΦ".
  iDestruct "Hcells" as "(Hfields0 & %Hinvs0)".
  have Hpool : pool_invs types := proj1 Hinvs0.
  have [Hfits [Hnodup [Hrangedisj Horiginclk]]] := Hpool.
  iDestruct "Hfields0" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  have Hcoords := Hcwmem.
  apply all_cells_elem_of in Hcoords.
  destruct Hcoords as (parent & ts & Htypes0 & Hcts).
  destruct ts as [cells arr]. simpl in Hcts.
  apply list_elem_of_lookup_1 in Hcts as [k Hck].
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbnds.
  have Hckbnd : (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z := proj2 (Hbnds cw Hcwmem).
  have Hcwcov' := Hcwcov.
  destruct (proj1 (cell_covers_w64 cw idv (proj1 (Hbnds cw Hcwmem)) Hckbnd (Hfits cw Hcwmem)) Hcwcov')
    as (Hcwcc & Hcwle & Hcwlt).
  have Hcc : uint.nat (cell_clock cw) = clock (item_id (run_head cw)) by (rewrite /cell_clock; word).
  iDestruct (own_type_pool_acc types cw Hcwmem with "Htypes") as "Hacc".
  iNamed "Hacc".
  iDestruct ("Hback" with "Hval") as "Htypes".
  have Hrunwf := Hrun.
  have Hfitscw := Hfits cw Hcwmem.
  have Hlenpos : (1 <= Z.of_nat (length (ic_run cw)))%Z.
  { destruct Hrunwf as [Hne0 _]. destruct (ic_run cw) as [|? ?]; [done | simpl; lia]. }
  iDestruct (own_store_struct_intro _ (MkStoreState client0 k0 types bind pend pdel) Hinvs0 with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
  wp_apply (wp_store__splitAtAndGetLeft_range s idv (MkStoreState client0 k0 types bind pend pdel) parent cells arr k cw
              Htypes0 Hck Hcwcc Hcwle Hcwlt with "[$Hcells]").
  iIntros (types') "(Hcells & %Hbranch)". simpl in Hbranch.
  destruct Hbranch as [[Hoeq ->] | [Holt2 (rloc & Hrnn & Hrfresh & ->)]].
  - (* no split: the run already ends at the id *)
    iApply ("HΦ" $! types).
    iEval (simpl) in "Hcells". simpl. iFrame "Hcells".
    iPureIntro. split_and!.
    + split_and!.
      * move=> p ts' Hp. exists ts'. split_and!; done.
      * move=> p Hp. exact Hp.
      * move=> kc. lia.
      * move=> c Hc _. exact Hc.
      * move=> ccl clkZ c Hc Hccl Hle2 Hlt2. exists c. split_and!; try done. by left.
      * move=> p ts0 ts0' Hp Hp' _. congruence.
      * move=> c1 Hc1. exists c1. split_and!; [exact Hc1 | done | lia | lia].
      * exact (live_refine_refl types).
      * exact (dead_chars_kept_refl types).
    + exists cw. split_and!; done.
    + destruct Hcwcov as (Hcl & Hle & Hlt).
      exists cw. split_and!; [exact Hcwmem | done | done | exact Hcl |].
      move: Hoeq Hcc Hle Hlt. rewrite /toYjsId /=. lia.
  - (* split just after the id *)
    have Ho2 : (0 < (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1
                < length (ic_run cw))%nat by lia.
    iApply ("HΦ" $! (<[parent := MkTypeState
        (split_cells cells k ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc)
        arr]> types)).
    iEval (simpl) in "Hcells". simpl. iFrame "Hcells".
    iPureIntro. split_and!.
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
      * exact (split_pool_subrange types parent cells arr k cw _ rloc Htypes0 Hck Hrunwf Ho2 Hckbnd Hfitscw).
      * exact (split_pool_live_refine types parent cells arr k _ rloc cw Htypes0 Hck).
      * exact (split_pool_dead_chars_kept types parent cells arr k _ rloc cw Htypes0 Hck).
    + destruct (split_pool_perm types parent cells arr k cw
                  ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc Htypes0 Hck)
        as (rest & Hold & Hnew).
      destruct (split_cell_facts cw
                  ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc Hrunwf Ho2)
        as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
      exists (split_cell_left cw ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1)).
      split_and!; [rewrite Hnew; apply list_elem_of_here | done | done | rewrite Hheadl //].
    + destruct (split_pool_perm types parent cells arr k cw
                  ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc Htypes0 Hck)
        as (rest & Hold & Hnew).
      destruct (split_cell_facts cw
                  ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc Hrunwf Ho2)
        as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
      destruct Hcwcov as (Hcl & Hle & Hlt).
      exists (split_cell_left cw ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1)).
      split_and!; [rewrite Hnew; apply list_elem_of_here | done | done | rewrite Hheadl; exact Hcl |].
      rewrite Hheadl Hlenl. move: Hcc Hle Hlt. rewrite /toYjsId /=. lia.
Qed.


(** [store.splitAtAndGetRight]: make the char [idv] (any char of the pool
    cell [cw]) start a node. When it is the run's first char the node is
    returned as is; otherwise the node is split just before it and the fresh
    right half comes back. Either way the returned node starts at [idv]. *)
Lemma wp_store__splitAtAndGetRight (s : loc) (idv : yjs.id.t) (st : store_state) (cw : item_cell) :
  pool_cell_covers (ss_types st) cw (toYjsId idv) ->
  {{{ is_pkg_init yjs ∗ own_store_struct s st }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetRight" #idv
  {{{ (rl : loc) (types' : gmap loc type_state), RET (#rl, #true);
      own_store_struct s (st <| ss_types := types' |>) ∗
      ⌜split_types_update_rel (ss_types st) types' cw⌝ ∗
      ⌜cell_starts_at types' (ic_parent cw) rl (toYjsId idv)⌝ }}}.
Proof using Type*.
  move=> Hcov.
  destruct st as [client0 k0 types bind pend pdel]. simpl in *.
  have [Hcwmem Hcwcov] := Hcov.
  iIntros (Φ) "(#Hpkg & Hcells) HΦ".
  iDestruct "Hcells" as "(Hfields0 & %Hinvs0)".
  have Hpool : pool_invs types := proj1 Hinvs0.
  have [Hfits [Hnodup [Hrangedisj Horiginclk]]] := Hpool.
  iDestruct "Hfields0" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  have Hcoords := Hcwmem.
  apply all_cells_elem_of in Hcoords.
  destruct Hcoords as (parent & ts & Htypes0 & Hcts).
  destruct ts as [cells arr]. simpl in Hcts.
  apply list_elem_of_lookup_1 in Hcts as [k Hck].
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbnds.
  have Hckbnd : (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z := proj2 (Hbnds cw Hcwmem).
  have Hcwcov' := Hcwcov.
  destruct (proj1 (cell_covers_w64 cw idv (proj1 (Hbnds cw Hcwmem)) Hckbnd (Hfits cw Hcwmem)) Hcwcov')
    as (Hcwcc & Hcwle & Hcwlt).
  have Hcc : uint.nat (cell_clock cw) = clock (item_id (run_head cw)) by (rewrite /cell_clock; word).
  iDestruct (own_type_pool_acc types cw Hcwmem with "Htypes") as "Hacc".
  iNamed "Hacc".
  iDestruct ("Hback" with "Hval") as "Htypes".
  have Hrunwf := Hrun.
  have Hfitscw := Hfits cw Hcwmem.
  have Hlenpos : (1 <= Z.of_nat (length (ic_run cw)))%Z.
  { destruct Hrunwf as [Hne0 _]. destruct (ic_run cw) as [|? ?]; [done | simpl; lia]. }
  iDestruct (own_store_struct_intro _ (MkStoreState client0 k0 types bind pend pdel) Hinvs0 with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
  wp_apply (wp_store__splitAtAndGetRight_range s idv (MkStoreState client0 k0 types bind pend pdel) parent cells arr k cw
              Htypes0 Hck Hcwcc Hcwle Hcwlt with "[$Hcells]").
  iIntros (rl types') "(Hcells & %Hbranch)". simpl in Hbranch.
  destruct Hbranch as [[Hoeq [-> ->]] | [Hopos (Hrlnn & Hrlfresh & ->)]].
  - (* no split: the run already starts at the id *)
    iApply ("HΦ" $! (ic_loc cw) types).
    iEval (simpl) in "Hcells". simpl. iFrame "Hcells".
    iPureIntro. split_and!.
    + split_and!.
      * move=> p ts' Hp. exists ts'. split_and!; done.
      * move=> p Hp. exact Hp.
      * move=> kc. lia.
      * move=> c Hc _. exact Hc.
      * move=> ccl clkZ c Hc Hccl Hle2 Hlt2. exists c. split_and!; try done. by left.
      * move=> p ts0 ts0' Hp Hp' _. congruence.
      * move=> c1 Hc1. exists c1. split_and!; [exact Hc1 | done | lia | lia].
      * exact (live_refine_refl types).
      * exact (dead_chars_kept_refl types).
    + destruct Hcwcov as (Hcl & Hle & Hlt).
      exists cw. split_and!; [exact Hcwmem | done | done |].
      move: Hcl Hle Hoeq Hcc. rewrite /toYjsId /=.
      destruct (item_id (run_head cw)) as [ci ck]. simpl. move=> -> Hle Hoeq Hcc. f_equal. lia.
  - (* split at the offset: the fresh right half starts at the id *)
    have Ho2 : (0 < (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))
                < length (ic_run cw))%nat.
    { split; [exact Hopos |]. clear -Hcwle Hcwlt. word. }
    iApply ("HΦ" $! rl (<[parent := MkTypeState
        (split_cells cells k (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl)
        arr]> types)).
    iEval (simpl) in "Hcells". simpl. iFrame "Hcells".
    iPureIntro. split_and!.
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
      * exact (split_pool_subrange types parent cells arr k cw _ rl Htypes0 Hck Hrunwf Ho2 Hckbnd Hfitscw).
      * exact (split_pool_live_refine types parent cells arr k _ rl cw Htypes0 Hck).
      * exact (split_pool_dead_chars_kept types parent cells arr k _ rl cw Htypes0 Hck).
    + destruct (split_pool_perm types parent cells arr k cw
                  (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl Htypes0 Hck)
        as (rest & Hold & Hnew).
      destruct (split_cell_facts cw
                  (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl Hrunwf Ho2)
        as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
      destruct Hcwcov as (Hcl & Hle & Hlt).
      exists (split_cell_right cw (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl).
      split_and!; [rewrite Hnew; apply elem_of_cons; right; apply list_elem_of_here | done | done |].
      rewrite (split_cell_right_head_id cw _ rl Hrunwf (proj2 Ho2)).
      move: Hcl Hle Hcc. rewrite /toYjsId /=. move=> Hcl Hle Hcc. f_equal; [exact Hcl | lia].
Qed.


(** [store.splitNode] at run granularity (plan-item-run-split stage 2):
    split the [k]-th run of the type at [parent] at offset [diff]; the pool
    gets the two halves ([split_runs]) and the address list the fresh right
    half's address after [k] ([split_locs]), the fresh address new to the
    WHOLE address map. Derived from the cell-level spec through the
    projections. *)
Lemma wp_store__splitNode_runs (s : loc) (str : store_state_runs)
    (parent l : loc) (ls : list loc) (tm : type_model) (k : nat) (r : ItemRun) (diff : w64) :
  sr_pool str !! parent = Some tm ->
  sr_locs str !! parent = Some ls ->
  tm_runs tm !! k = Some r ->
  ls !! k = Some l ->
  (0 < uint.nat diff < length (run_items r))%nat ->
  {{{ is_pkg_init yjs ∗ own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "splitNode" #l #diff
  {{{ (rloc : loc), RET (#l, #rloc);
      own_store_runs s
        (str <| sr_pool := <[parent := MkTypeModel (split_runs (tm_runs tm) k (uint.nat diff)) (tm_arr tm)]> (sr_pool str) |>
             <| sr_locs := <[parent := split_locs ls k rloc]> (sr_locs str) |>) ∗
      ⌜rloc ≠ null ∧ rloc ∉ concat ((map_to_list (sr_locs str)).*2)⌝ }}}.
Proof using Type*.
  move=> Hp Hl Hr Hlk Hdiff.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  iDestruct "Hruns" as (st) "(%Hproj & Hcells)".
  subst str. destruct st as [client k0 types bind pend pdel]. simpl in *.
  rewrite /pool_of lookup_fmap in Hp.
  destruct (types !! parent) as [ts|] eqn:Hts; simplify_eq/=.
  rewrite /locs_of lookup_fmap Hts /= in Hl. simplify_eq/=.
  destruct ts as [cells arr].
  rewrite /type_model_of /= list_lookup_fmap in Hr.
  destruct (cells !! k) as [cw|] eqn:Hck; simplify_eq/=.
  rewrite list_lookup_fmap Hck /= in Hlk. simplify_eq/=.
  wp_apply (wp_store__splitNode s (MkStoreState client k0 types bind pend pdel)
              parent cells arr k cw diff Hts Hck Hdiff with "[$Hcells]").
  iIntros (rloc) "(Hcells & %Hfresh)".
  iApply ("HΦ" $! rloc).
  iSplitL.
  { iExists (MkStoreState client k0
      (<[parent := MkTypeState (split_cells cells k (uint.nat diff) rloc) arr]> types)
      bind pend pdel).
    iEval (simpl) in "Hcells".
    iSplitR; [| iFrame "Hcells"].
    iPureIntro.
    rewrite /state_runs_of /= pool_of_insert locs_of_insert /type_model_of /=.
    rewrite split_cells_runs split_cells_locs //. }
  iPureIntro.
  destruct Hfresh as [Hnn Hnotin]. split; [exact Hnn |].
  simpl. rewrite locs_of_concat. exact Hnotin.
Qed.

End store_update.
