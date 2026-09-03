(** store update path, split layer at run granularity: the DLL half
    [wp_splitItem_runs] (over the type's [own_ytype_runs]), [store.splitNode]
    over the whole store ([wp_store__splitNode_runs], adding the per-client
    run-list insertion), and
    [wp_store__splitAtAndGetLeft_runs] / [wp_store__splitAtAndGetRight_runs]
    (proved from [wp_store__GetNode_runs] and [wp_store__splitNode_runs],
    stepping the pool and the address map by the index-explicit
    [pool_split_left_step] / [pool_split_right_step]), plus the split-pool
    bookkeeping ([pool_invs_split], [split_types_update_rel], the
    [split_pool_*] / [split_cells_*] laws the run-level text layer reads
    its materialized cells through).
    Split out of [store/GetNode] so it proof-checks in parallel; same
    [Section] boilerplate and [#[local]] instances. *)
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

(** [split_cells] index bookkeeping: the left half sits at the split
    index. *)
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

(** [splitItem n diff] at run granularity: the node at address [lc], the
    [k]-th run [r] of the type at [parent], is split at offset [diff] in
    the type's DLL: [lc] keeps the first [diff] chars, the fresh address
    [rloc] gets the rest ([split_locs] / [split_runs]), and [rloc] is new to
    the type. The DLL half of [store.splitNode] (y-octo: [Item::split_at]). *)
Lemma wp_splitItem_runs (parent lc : loc) (ls : list loc) (runs : list ItemRun)
    (arr : list (YjsItem A)) (k : nat) (r : ItemRun) (diff : w64) :
  ls !! k = Some lc ->
  runs !! k = Some r ->
  (0 < uint.nat diff < length (run_items r))%nat ->
  run_fits r ->
  {{{ is_pkg_init yjs ∗ own_ytype_runs parent (DfracOwn 1) ls (MkTypeModel runs arr) }}}
    @! yjs.splitItem #lc #diff
  {{{ (rloc : loc), RET #rloc;
      own_ytype_runs parent (DfracOwn 1) (split_locs ls k rloc)
        (MkTypeModel (split_runs runs k (uint.nat diff)) arr) ∗
      ⌜rloc ≠ null ∧ rloc ∉ ls⌝ }}}.
Proof using Type*.
  move=> Hlk Hrk Hdiff Hfits.
  wp_start as "Htext". iNamed "Htext".
  iEval (cbn [tm_runs]) in "Hdll".
  iDestruct (own_dll_runs_length with "Hdll") as %Hlenl.
  pose proof (take_drop_middle ls k lc Hlk) as Hsl.
  pose proof (take_drop_middle runs k r Hrk) as Hsr.
  set (prel := take k ls) in Hsl.
  set (sufl := drop (S k) ls) in Hsl.
  set (prer := take k runs) in Hsr.
  set (sufr := drop (S k) runs) in Hsr.
  have Hlent : length prel = length prer by rewrite /prel /prer !length_take Hlenl.
  iEval (rewrite -Hsl -Hsr (own_dll_runs_app _ _ _ _ _ _ _ _ _ _ Hlent)) in "Hdll".
  iDestruct "Hdll" as (ml mf) "[Hseg1 Hseg2]".
  iDestruct (own_dll_runs_cons_unfold with "Hseg2") as (nxtcw) "(%Hhead & %Hpccw & %Hrun & Hnodecw & Hrest)".
  destruct Hhead as [Hmfeq Hmfnn]. subst mf.
  iDestruct "Hnodecw" as (itemVal olidcw oridcw)
    "(Hval & Holeft & Horight & %Hinlcw & %Hinrcw & %Hidn & %Hcontn & %Hpar & %Hprev & %Hnextcw & %Hflags)".
  have Hid : item_id (run_head_item r) = toYjsId itemVal.(yjs.item.id').
  { symmetry. exact Hidn. }
  have Hcontent : content <$> run_items r = explode (toContent itemVal.(yjs.item.content')).
  { have Hstr : toContent itemVal.(yjs.item.content') = items_string (run_items r) := Hcontn.
    rewrite Hstr. exact Hpccw. }
  have Holid : origin_id (origin (run_head_item r)) = toYjsId <$> olidcw.
  { symmetry. exact Hinlcw. }
  have Horid : origin_id (rightOrigin (run_head_item r)) = toYjsId <$> oridcw.
  { symmetry. exact Hinrcw. }
  iDestruct (typed_pointsto_not_null with "Hval") as %Hcwnn.
  wp_auto.
  (* olid := newId(client, clock+diff-1) *)
  wp_apply wp_NewId.
  (* cb := []byte(n.content.content) via the byte round-trip *)
  wp_apply wp_string_to_bytes. iIntros (cbs) "[Hcb Hcbcap]". wp_auto.
  (* the right node's id := newId(client, clock+diff) *)
  wp_apply wp_NewId.
  have Hsclen : length (itemVal.(yjs.item.content').(yjs.content.content')) = length (run_items r).
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
  (* the fresh right node's address misses the whole type: the two opened
     segments by the DLL's freshness law, the split node by pointsto conflict *)
  iDestruct (own_dll_runs_fresh with "Hrs Hseg1") as %Hfr_pre.
  iDestruct (own_dll_runs_fresh with "Hrs Hrest") as %Hfr_suf.
  iAssert (⌜rs ≠ lc⌝)%I as %Hfr_cw.
  { destruct (decide (rs = lc)) as [Heqloc | Hneloc]; last by iPureIntro.
    subst rs.
    iDestruct (item_pointsto_conflict with "Hrs Hval") as %[]. }
  have Hrsfresh : rs ∉ ls.
  { rewrite -Hsl. move=> Hin. apply elem_of_app in Hin as [Hin | Hin]; [exact (Hfr_pre Hin) |].
    apply elem_of_cons in Hin as [Heq | Hin]; [exact (Hfr_cw Heq) | exact (Hfr_suf Hin)]. }
  set (o := uint.nat diff).
  have Hnowrapcw : (Z.of_nat (run_clock r) + Z.of_nat (length (run_items r)) < 2^64)%Z := Hfits.
  have Hckbnd : (Z.of_nat (clock (item_id (run_head_item r))) < 2^64)%Z
    by (rewrite Hid /toYjsId /=; word).
  have Hcwck : run_clock r = uint.nat itemVal.(yjs.item.id').(yjs.id.clock')
    by (rewrite /run_clock Hid /toYjsId /=).
  have Hsintlen : sint.nat cbs.(slice.len) = length (run_items r).
  { rewrite -Hsclen. symmetry. exact Hcbwf1. }
  have Hsintdiff : sint.nat diff = o.
  { rewrite /o. word. }
  have Hoinrun : (o < length (run_items r))%nat by (rewrite /o; lia).
  have Hole : (o <= length (run_items r))%nat by lia.
  have Hrun0 : run_items r !! 0%nat = Some (run_head_item r).
  { rewrite /run_head_item. destruct Hrun as [Hne _]. destruct (run_items r) as [|a r']; [done | reflexivity]. }
  destruct (run_items r !! o) as [yo|] eqn:Hyo; [| apply lookup_ge_None in Hyo; lia].
  have Hyoid := run_wf_lookup_clock (run_items r) o (run_head_item r) yo Hrun Hrun0 Hyo.
  have Hyoro := run_wf_lookup_rightOrigin (run_items r) o (run_head_item r) yo Hrun Hrun0 Hyo.
  iDestruct (typed_pointsto_not_null with "olid") as %Holidnn.
  iPersist "olid".
  have Hrhcl : run_head_item (split_run_left r o) = run_head_item r.
  { rewrite /run_head_item /split_run_left /=. apply hd_inhabitant_take. rewrite /o; lia. }
  have Hrhcr : run_head_item (split_run_right r o) = yo.
  { rewrite /run_head_item /split_run_right /=. exact (hd_inhabitant_drop _ o yo Hyo). }
  have Hcontl : content <$> take o (run_items r) = explode (take (sint.nat diff) itemVal.(yjs.item.content').(yjs.content.content')).
  { rewrite Hsintdiff fmap_take Hcontent /toContent /explode fmap_take //. }
  have Hsubdrop : subslice (sint.nat diff) (sint.nat cbs.(slice.len)) itemVal.(yjs.item.content').(yjs.content.content')
                = drop o itemVal.(yjs.item.content').(yjs.content.content').
  { rewrite Hsintdiff Hsintlen -Hsclen /subslice. rewrite take_ge; [reflexivity | lia]. }
  have Hcontr : content <$> drop o (run_items r) = explode (drop o itemVal.(yjs.item.content').(yjs.content.content')).
  { rewrite fmap_drop Hcontent /toContent /explode fmap_drop //. }
  (* ----- the two halves' facts (origin telescoping), branch-agnostic ----- *)
  set (leftRun := split_run_left r o).
  set (rightRun := split_run_right r o).
  set (originId := {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId');
                 yjs.id.clock' := word.sub (word.add itemVal.(yjs.item.id').(yjs.id.clock') diff) (W64 1) |}).
  have Hopos : (0 < o)%nat by (rewrite /o; lia).
  have Hnowrap_add : (uint.Z itemVal.(yjs.item.id').(yjs.id.clock') + uint.Z diff < 2^64)%Z.
  { have H1 := Hnowrapcw. rewrite Hcwck in H1. have H2 := Hdiff. word. }
  have Hadd_eq : (uint.nat itemVal.(yjs.item.id').(yjs.id.clock') + o)%nat = uint.nat (word.add itemVal.(yjs.item.id').(yjs.id.clock') diff).
  { rewrite /o. clear -Hnowrap_add. word. }
  have [xprev Hxprev] : is_Some (run_items r !! (o - 1)%nat).
  { apply lookup_lt_is_Some. rewrite /o. lia. }
  have Hyo2 : run_items r !! S (o - 1)%nat = Some yo.
  { replace (S (o - 1))%nat with o by (rewrite /o; lia). exact Hyo. }
  have Hstep := proj2 Hrun (o - 1)%nat xprev yo Hxprev Hyo2.
  have Horig : origin yo = itemPtr xprev by (destruct Hstep as [_ [Hh _]]; exact Hh).
  have Hxpid := run_wf_lookup_clock (run_items r) (o - 1)%nat (run_head_item r) xprev Hrun Hrun0 Hxprev.
  have Hcrorig : origin_id (origin (run_head_item rightRun)) = toYjsId <$> Some originId.
  { rewrite /rightRun Hrhcr Horig /origin_id /=. f_equal.
    rewrite Hxpid Hid /toYjsId /originId /=. f_equal. clear -Hnowrap_add Hdiff. word. }
  have Hrhck : clock (item_id (run_head_item r)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clock') by (rewrite Hid /toYjsId /=).
  have Hrhcli : clientId (item_id (run_head_item r)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clientId') by (rewrite Hid /toYjsId /=).
  set (ivl := itemVal <| yjs.item.content' := {| yjs.content.content' := take (sint.nat diff) itemVal.(yjs.item.content').(yjs.content.content') |} |> <| yjs.item.right' := rs |>).
  set (ivr := {| yjs.item.id' := {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId'); yjs.id.clock' := word.add itemVal.(yjs.item.id').(yjs.id.clock') diff |};
                 yjs.item.originLeftId' := olid_ptr;
                 yjs.item.originRightId' := itemVal.(yjs.item.originRightId');
                 yjs.item.left' := lc;
                 yjs.item.right' := itemVal.(yjs.item.right');
                 yjs.item.parent' := itemVal.(yjs.item.parent');
                 yjs.item.content' := {| yjs.content.content' := subslice (sint.nat diff) (sint.nat cbs.(slice.len)) itemVal.(yjs.item.content').(yjs.content.content') |};
                 yjs.item.flags' := itemVal.(yjs.item.flags') |}).
  have Hivl_ol : ivl.(yjs.item.originLeftId') = itemVal.(yjs.item.originLeftId') by (rewrite /ivl /=).
  have Hivl_or : ivl.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId') by (rewrite /ivl /=).
  have Hivl_left : ivl.(yjs.item.left') = ml by (rewrite /ivl /=; exact Hprev).
  have Hivr_r : ivr.(yjs.item.right') = itemVal.(yjs.item.right') by reflexivity.
  have Hivr_ol : ivr.(yjs.item.originLeftId') = olid_ptr by (rewrite /ivr /=).
  have Hivr_or : ivr.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId') by (rewrite /ivr /=).
  have Hp4 : ivl.(yjs.item.right') = rs by (rewrite /ivl /=).
  have Hp5 : ivl.(yjs.item.parent') = parent by (rewrite /ivl /=; exact Hpar).
  have Hp6 : item_id (run_head_item leftRun) = toYjsId ivl.(yjs.item.id'). { rewrite /leftRun Hrhcl /ivl /=. exact Hid. }
  have Hp7 : content <$> run_items leftRun = explode (toContent ivl.(yjs.item.content')). { rewrite /leftRun /ivl /toContent /=. exact Hcontl. }
  have Hp8 : origin_id (origin (run_head_item leftRun)) = toYjsId <$> olidcw. { rewrite /leftRun Hrhcl. exact Holid. }
  have Hp9 : origin_id (rightOrigin (run_head_item leftRun)) = toYjsId <$> oridcw. { rewrite /leftRun Hrhcl. exact Horid. }
  have Hp10 : ivl.(yjs.item.flags') = (if run_deleted leftRun then W8 6 else W8 2). { rewrite /ivl /leftRun /=. exact Hflags. }
  have Hp11 : run_wf (run_items leftRun). { rewrite /leftRun /=. exact (run_wf_take (run_items r) o Hopos Hrun). }
  have Hp12 : ivr.(yjs.item.left') = lc. { rewrite /ivr /=. reflexivity. }
  have Hp13 : ivr.(yjs.item.parent') = parent. { rewrite /ivr /=. exact Hpar. }
  have Hp14 : item_id (run_head_item rightRun) = toYjsId ivr.(yjs.item.id'). { rewrite /rightRun Hrhcr Hyoid /ivr /toYjsId /=. rewrite Hrhck Hrhcli Hadd_eq. reflexivity. }
  have Hp15 : content <$> run_items rightRun = explode (toContent ivr.(yjs.item.content')). { rewrite /rightRun /ivr /toContent /= Hsubdrop. exact Hcontr. }
  have Hp17 : origin_id (rightOrigin (run_head_item rightRun)) = toYjsId <$> oridcw. { rewrite /rightRun Hrhcr Hyoro. exact Horid. }
  have Hp18 : ivr.(yjs.item.flags') = (if run_deleted rightRun then W8 6 else W8 2). { rewrite /ivr /rightRun /=. exact Hflags. }
  have Hp19 : run_wf (run_items rightRun). { rewrite /rightRun /=. exact (run_wf_drop (run_items r) o Hoinrun Hrun). }
  have Hpcl : run_per_char leftRun := run_per_char_intro _ _ _ Hp7.
  have Hpcr : run_per_char rightRun := run_per_char_intro _ _ _ Hp15.
  iDestruct "Horight" as "#HorightP".
  (* [if n.right != nil] branches on whether [lc] is the type's last node *)
  destruct sufl as [|d0l sufl'] eqn:Hsufleq; destruct sufr as [|d0r sufr'] eqn:Hsufreq;
    [| iDestruct "Hrest" as %[] | iDestruct "Hrest" as %[] |].
  - (* lc is last: no downstream relink *)
    iDestruct "Hrest" as %[Hrnull0 Htl0eq].
    have Hrnull : itemVal.(yjs.item.right') = null by rewrite Hnextcw Hrnull0.
    rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.right') = null) Hrnull).
    wp_auto.
    have Hsl' : split_locs ls k rs = prel ++ [lc; rs] ++ [].
    { rewrite /split_locs Hlk -/prel -/sufl Hsufleq //. }
    have Hsr' : split_runs runs k o = prer ++ [leftRun; rightRun] ++ [].
    { rewrite /split_runs Hrk -/prer -/sufr Hsufreq //. }
    iApply ("HΦ" $! rs).
    iSplitL; last (iPureIntro; split; [exact Hrsnn | exact Hrsfresh]).
    iExists yt, rs. iFrame "Hparent".
    iSplitL.
    { iEval (cbn [tm_runs]). rewrite Hsl' Hsr'.
      iApply (own_dll_runs_split (DfracOwn 1) parent prel [] prer [] lc rs r o
                yt.(yjs.yType.start') rs ml null Hlent Hmfnn Hrsnn Hpcl Hpcr Hp11 Hp19).
      iSplitL "Hseg1"; first iFrame "Hseg1".
      iSplitL "Hval Holeft".
      { iExists ivl, olidcw, oridcw.
        rewrite Hivl_ol Hivl_or.
        iFrame "Hval Holeft HorightP".
        iPureIntro. split_and!.
        - exact (eq_sym Hp8).
        - exact (eq_sym Hp9).
        - exact (eq_sym Hp6).
        - symmetry. exact (items_string_explode _ _ Hp7).
        - exact Hp5.
        - exact Hivl_left.
        - exact Hp4.
        - exact Hp10. }
      iSplitL "Hrs".
      { iExists ivr, (Some originId), oridcw.
        rewrite Hivr_ol Hivr_or.
        iFrame "Hrs HorightP".
        iSplitR; first (simpl; iFrame "olid"; iPureIntro; exact Holidnn).
        iPureIntro. split_and!.
        - exact (eq_sym Hcrorig).
        - exact (eq_sym Hp17).
        - exact (eq_sym Hp14).
        - symmetry. exact (items_string_explode _ _ Hp15).
        - exact Hp13.
        - exact Hp12.
        - rewrite Hivr_r. exact Hrnull.
        - exact Hp18. }
      iEval (simpl). iPureIntro. split; reflexivity. }
    iPureIntro. simpl. split.
    + rewrite (split_runs_visible runs k o r Hrk Hole). exact Hlen.
    + rewrite (split_runs_flatten runs k o r Hrk). exact Harr.
  - (* lc has a right neighbour d0: relink d0.left := right first *)
    iDestruct (own_dll_runs_cons_unfold with "Hrest") as (nxtd) "(%Hlocd & %Hpcd0 & %Hrund & Hnoded & Hrestd)".
    destruct Hlocd as [Hlocd1n Hlocdnn].
    iDestruct "Hnoded" as (ivd olidd oridd)
      "(Hvald & Holeftd & Horightd & %Hinld & %Hinrd & %Hiddn & %Hcontdn & %Hpard & %Hprevd & %Hnextd & %Hflagsd)".
    have Hlocd1 : itemVal.(yjs.item.right') = d0l by rewrite Hnextcw Hlocd1n.
    have Hrnnd : itemVal.(yjs.item.right') ≠ null by rewrite Hlocd1.
    rewrite (bool_decide_eq_false_2 (itemVal.(yjs.item.right') = null) Hrnnd).
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
    iAssert (own_dll_runs (DfracOwn 1) parent itemVal.(yjs.item.right') tl rs null (d0l :: sufl') (d0r :: sufr'))
      with "[Hvald Holeftd Horightd Hrestd]" as "Hsufdll".
    { rewrite Hlocd1.
      iApply (own_dll_runs_cons_fold (DfracOwn 1) parent tl rs null nxtd d0l sufl' d0r sufr' Hlocdnn Hrund Hpcd0).
      iSplitL "Hvald Holeftd Horightd".
      { iExists ivd2, olidd, oridd.
        rewrite Hd2ol Hd2or.
        iFrame "Hvald Holeftd Horightd".
        iPureIntro. split_and!.
        - exact Hinld.
        - exact Hinrd.
        - rewrite Hd2id. exact Hiddn.
        - rewrite Hd2c. exact Hcontdn.
        - rewrite Hd2p. exact Hpard.
        - exact Hd2l.
        - rewrite Hd2r. exact Hnextd.
        - rewrite Hd2f. exact Hflagsd. }
      iFrame "Hrestd". }
    have Hsl' : split_locs ls k rs = prel ++ [lc; rs] ++ d0l :: sufl'.
    { rewrite /split_locs Hlk -/prel -/sufl Hsufleq //. }
    have Hsr' : split_runs runs k o = prer ++ [leftRun; rightRun] ++ d0r :: sufr'.
    { rewrite /split_runs Hrk -/prer -/sufr Hsufreq //. }
    iApply ("HΦ" $! rs).
    iSplitL; last (iPureIntro; split; [exact Hrsnn | exact Hrsfresh]).
    iExists yt, tl. iFrame "Hparent".
    iSplitL.
    { iEval (cbn [tm_runs]). rewrite Hsl' Hsr'.
      iApply (own_dll_runs_split (DfracOwn 1) parent prel (d0l :: sufl') prer (d0r :: sufr') lc rs r o
                yt.(yjs.yType.start') tl ml itemVal.(yjs.item.right') Hlent Hmfnn Hrsnn Hpcl Hpcr Hp11 Hp19).
      iSplitL "Hseg1"; first iFrame "Hseg1".
      iSplitL "Hval Holeft".
      { iExists ivl, olidcw, oridcw.
        rewrite Hivl_ol Hivl_or.
        iFrame "Hval Holeft HorightP".
        iPureIntro. split_and!.
        - exact (eq_sym Hp8).
        - exact (eq_sym Hp9).
        - exact (eq_sym Hp6).
        - symmetry. exact (items_string_explode _ _ Hp7).
        - exact Hp5.
        - exact Hivl_left.
        - exact Hp4.
        - exact Hp10. }
      iSplitL "Hrs".
      { iExists ivr, (Some originId), oridcw.
        rewrite Hivr_ol Hivr_or.
        iFrame "Hrs HorightP".
        iSplitR; first (simpl; iFrame "olid"; iPureIntro; exact Holidnn).
        iPureIntro. split_and!.
        - exact (eq_sym Hcrorig).
        - exact (eq_sym Hp17).
        - exact (eq_sym Hp14).
        - symmetry. exact (items_string_explode _ _ Hp15).
        - exact Hp13.
        - exact Hp12.
        - exact Hivr_r.
        - exact Hp18. }
      iExact "Hsufdll". }
    iPureIntro. simpl. split.
    + rewrite (split_runs_visible runs k o r Hrk Hole). exact Hlen.
    + rewrite (split_runs_flatten runs k o r Hrk). exact Harr.
Qed.

(** [store.splitNode] at run granularity (plan-item-run-split stage 2):
    split the [k]-th run of the type at [parent] at offset [diff]; the pool
    gets the two halves ([split_runs]) and the address list the fresh right
    half's address after [k] ([split_locs]), the fresh address new to the
    WHOLE address map. The DLL half is [wp_splitItem_runs]; the per-client
    run list ([own_item_map]) gets the right half inserted after the split
    node, the cell-level bookkeeping ([split_pool_*]) applying through the
    materialized registry until C6. *)
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
  destruct str as [client0 k0 locs p bind pend pdel]. simpl in *.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  iDestruct (own_store_runs_to_state with "Hruns") as "(Hstruct & %Haligned)".
  iDestruct "Hstruct" as "(Hfields0 & %Hinvs0)".
  have Hpool : pool_invs (types_of_locs_pool locs p) := proj1 Hinvs0.
  have Hreg0 : registry_coh bind (types_of_locs_pool locs p) := proj2 Hinvs0.
  iDestruct "Hfields0" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iEval (simpl) in "Htypes". iEval (simpl) in "Hitems".
  set (types := types_of_locs_pool locs p) in *.
  have [Hrunfits [Hnodup [Hrangedisj Horiginclk]]] := Hpool.
  have Hprem := locs_aligned_lens _ _ Haligned.
  have Hlsl : length ls = length (tm_runs tm).
  { destruct (Hprem parent tm Hp) as (ls0 & Hls0 & Hlen0). rewrite Hl in Hls0. injection Hls0 as <-. exact Hlen0. }
  set (cells := cells_of_locs_runs parent ls (tm_runs tm)).
  set (cw := MkItemCell l (run_items r) (run_deleted r) parent).
  have Htypes : types !! parent = Some (MkTypeState cells (tm_arr tm)).
  { rewrite /types /types_of_locs_pool map_lookup_imap Hp /= Hl //. }
  have Hcellk : cells !! k = Some cw.
  { rewrite /cells /cells_of_locs_runs lookup_zip_with Hlk Hr //. }
  set (o := uint.nat diff).
  iDestruct "Hitems" as (mref) "(Hitemsf & Hitemmap)".
  have Hcwmem : cw ∈ all_cells types.
  { apply all_cells_elem_of. exists parent, (MkTypeState cells (tm_arr tm)).
    split; [exact Htypes | exact (list_elem_of_lookup_2 _ _ _ Hcellk)]. }
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbnds0.
  have Hckbnd : (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z := proj2 (Hbnds0 cw Hcwmem).
  iDestruct (own_type_pool_runs_wf with "Htypes") as %Hwfs0.
  have Hrun : run_wf (ic_run cw) := Hwfs0 cw Hcwmem.
  have Hnowrapcw : (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) < 2^64)%Z := Hrunfits cw Hcwmem.
  have Hfitsr : run_fits r.
  { have H' : (uint.Z (W64 (clock (item_id (run_head_item r)))) + Z.of_nat (length (run_items r)) < 2^64)%Z := Hnowrapcw.
    have Hb : (Z.of_nat (clock (item_id (run_head_item r))) < 2^64)%Z := Hckbnd.
    change ((Z.of_nat (clock (item_id (run_head_item r))) + Z.of_nat (length (run_items r)) < 2^64)%Z).
    word. }
  (* open [parent]'s cells as the run view, and read the split node's struct
     (its id is what the item-map surgery keys on) *)
  rewrite /own_type_pool.
  iDestruct (big_sepM_delete _ _ parent _ Htypes with "Htypes") as "[(Hpc & %Harrinv) Hrestmap]".
  iEval (cbn [ty_cells ty_arr]) in "Hpc".
  iDestruct (own_ytype_runs_intro with "Hpc") as "Hyt".
  iEval (rewrite /cells (cells_of_locs_runs_loc parent ls (tm_runs tm) Hlsl)
                 (cells_of_locs_runs_run parent ls (tm_runs tm) Hlsl)) in "Hyt".
  iDestruct "Hyt" as (yt0 tl0) "(Hparent0 & Hdll0 & %Hlen0 & %Hrepr0)".
  iDestruct (own_dll_runs_acc (DfracOwn 1) parent _ tl0 ls (tm_runs tm) k l r Hlk Hr with "Hdll0")
    as (prev0 nxt0) "(%Hcl0 & %Hcr0 & %Hrun0 & %Hpc0 & %Hclen0 & Hnode0 & Hback0)".
  iDestruct "Hnode0" as (itemVal olid0 orid0)
    "(Hval0 & Hol0 & Hor0 & %Hinl0 & %Hinr0 & %Hidn0 & %Hcont0 & %Hpar0 & %Hprev0 & %Hnext0 & %Hflags0)".
  have Hid : item_id (run_head cw) = toYjsId itemVal.(yjs.item.id').
  { symmetry. exact Hidn0. }
  iAssert (own_item_node l (DfracOwn 1) (input_of_run r) (run_deleted r) parent prev0 nxt0)
    with "[Hval0 Hol0 Hor0]" as "Hnode0".
  { iExists itemVal, olid0, orid0. iFrame "Hval0 Hol0 Hor0". iPureIntro.
    split_and!; [exact Hinl0 | exact Hinr0 | exact Hidn0 | exact Hcont0 | exact Hpar0
                | exact Hprev0 | exact Hnext0 | exact Hflags0]. }
  iDestruct ("Hback0" with "Hnode0") as "Hdll0".
  iAssert (own_ytype_runs parent (DfracOwn 1) ls (MkTypeModel (tm_runs tm) (tm_arr tm)))
    with "[Hparent0 Hdll0]" as "Hyt".
  { iExists yt0, tl0. iFrame "Hparent0 Hdll0". iPureIntro. split; [exact Hlen0 | exact Hrepr0]. }
  wp_method_call. wp_call. wp_call. wp_auto.
  (* the DLL half *)
  wp_apply (wp_splitItem_runs parent l ls (tm_runs tm) (tm_arr tm) k r diff Hlk Hr Hdiff Hfitsr
              with "[$Hpkg $Hyt]").
  iIntros (rs) "(Hyt2 & %Hrsnn & %Hrsls)".
  (* the fresh address misses the other types too: borrow its node against
     the rest of the pool *)
  have Hlk' : split_locs ls k rs !! S k = Some rs := split_locs_lookup_right ls k rs l Hlk.
  have Hrk' : split_runs (tm_runs tm) k o !! S k = Some (split_run_right r o)
    := split_runs_lookup_right _ _ _ _ Hr.
  iDestruct "Hyt2" as (yt2 tl2) "(Hparent2 & Hdll2 & %Hlen2 & %Hrepr2)".
  iEval (cbn [tm_runs]) in "Hdll2".
  iDestruct (own_dll_runs_lookup_acc _ _ _ _ _ _ _ _ _ _ _ Hlk' Hrk' with "Hdll2") as (pr nr) "(Hnoder & Hbackr)".
  iDestruct "Hnoder" as (ivr olr orr) "(Hrsval & Hrsol & Hrsor & %Hf1 & %Hf2 & %Hf3 & %Hf4 & %Hf5 & %Hf6 & %Hf7 & %Hf8)".
  iDestruct (big_sepM_sep with "Hrestmap") as "[Hrestown Hrestinv]".
  iDestruct (all_cells_fresh rs _ (DfracOwn 1) (delete parent types) with "Hrsval Hrestown") as %Hfr_rest.
  iAssert (own_type_pool (DfracOwn 1) (delete parent types))%I with "[Hrestown Hrestinv]" as "Hrestmap".
  { rewrite /own_type_pool big_sepM_sep. iFrame "Hrestown Hrestinv". }
  iAssert (own_item_node rs (DfracOwn 1) (input_of_run (split_run_right r o)) (run_deleted (split_run_right r o)) parent pr nr)
    with "[Hrsval Hrsol Hrsor]" as "Hnoder".
  { iExists ivr, olr, orr. iFrame "Hrsval Hrsol Hrsor". iPureIntro.
    split_and!; [exact Hf1 | exact Hf2 | exact Hf3 | exact Hf4 | exact Hf5 | exact Hf6 | exact Hf7 | exact Hf8]. }
  iDestruct ("Hbackr" with "Hnoder") as "Hdll2".
  have Hrsfresh : rs ∉ ic_loc <$> all_cells types.
  { move=> Hin. rewrite (all_cells_lookup types parent _ Htypes) /= fmap_app in Hin.
    apply elem_of_app in Hin as [Hin | Hin].
    - rewrite /cells (cells_of_locs_runs_loc parent ls (tm_runs tm) Hlsl) in Hin. exact (Hrsls Hin).
    - exact (Hfr_rest Hin). }
  (* back to the cell registry: the split type is [split_cells] *)
  iAssert (own_ytype_runs parent (DfracOwn 1) (split_locs ls k rs) (MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm)))
    with "[Hparent2 Hdll2]" as "Hyt2".
  { iExists yt2, tl2. iFrame "Hparent2 Hdll2". iPureIntro. split; [exact Hlen2 | exact Hrepr2]. }
  iDestruct (own_ytype_runs_as_cells with "Hyt2") as "[%Hlen2' Hyt2]".
  iEval (cbn [tm_runs tm_arr]) in "Hyt2".
  iEval (rewrite (cells_of_locs_runs_split parent ls (tm_runs tm) k o l rs r Hlsl Hlk Hr) -/cells) in "Hyt2".
  set (types2 := <[parent := MkTypeState (split_cells cells k o rs) (tm_arr tm)]> types).
  iAssert (own_type_pool (DfracOwn 1) types2)%I with "[Hyt2 Hrestmap]" as "Htypes2".
  { rewrite /types2 /own_type_pool -insert_delete_eq big_sepM_insert_delete delete_delete_eq.
    iFrame "Hrestmap". simpl. iFrame "Hyt2". iPureIntro. exact Harrinv. }
  (* ----- the halves' cell facts ----- *)
  have Hdisj : ∀ c, c ∈ all_cells types -> cell_client c = cell_client cw -> ic_loc c ≠ ic_loc cw ->
     (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z (cell_clock cw))%Z ∨
     (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) <= uint.Z (cell_clock c))%Z
    := λ c Hc Hcc Hlocne, Hrangedisj c cw Hc Hcwmem Hcc Hlocne.
  have Hck' : clock (item_id (run_head cw)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clock') by rewrite Hid //.
  have Hcwck : cell_clock cw = itemVal.(yjs.item.id').(yjs.id.clock').
  { rewrite /cell_clock Hck'. word. }
  have Hob : (0 < o < length (ic_run cw))%nat := Hdiff.
  have Hoinrun : (o < length (ic_run cw))%nat by lia.
  have Hopos : (0 < o)%nat by lia.
  set (leftCell := split_cell_left cw o).
  set (rightCell := split_cell_right cw o rs).
  destruct (split_cell_facts cw o rs Hrun Hob) as (Hrhcl & Hlenl & Hlenr & Hcccl & Hcccr & Hclcl & Hclcr).
  have Hrhcl' : run_head leftCell = run_head cw := Hrhcl.
  have Hrhck : clock (item_id (run_head cw)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clock') by (rewrite Hid /toYjsId /=).
  have Hrhcli : clientId (item_id (run_head cw)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clientId') by (rewrite Hid /toYjsId /=).
  have Hccr_clock : uint.Z (cell_clock rightCell) = (uint.Z (cell_clock cw) + Z.of_nat o)%Z.
  { have H1 := Hckbnd. have H2 := Hoinrun. have H3 := Hnowrapcw.
    rewrite /rightCell Hclcr. rewrite /cell_clock in H3 *. clear -H1 H2 H3. word. }
  have Hclloc : ic_loc leftCell = l by reflexivity.
  have Hcrloc : ic_loc rightCell = rs by reflexivity.
  have Hclcli : cell_client leftCell = cell_client cw := Hcccl.
  have Hkpcl : cell_kp leftCell = cell_kp cw.
  { rewrite /cell_kp /cell_pr Hcccl Hclcl Hclloc. reflexivity. }
  destruct (split_pool_perm types parent cells (tm_arr tm) k cw o rs Htypes Hcellk) as (rest & Hperm1 & Hperm2).
  (* ----- read the client run slice (map.lookup1) through the truncated node ----- *)
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
  have Hsck0 : split_cells cells k o rs !! k = Some leftCell := split_cells_lookup_left cells k o rs cw Hcellk.
  have Hlk2 : types2 !! parent = Some (MkTypeState (split_cells cells k o rs) (tm_arr tm)) by apply lookup_insert_eq.
  iDestruct (big_sepM_lookup_acc _ _ parent _ Hlk2 with "Htypes2") as "[(Hpc2 & %Harrinv2) Hclose2]".
  iDestruct "Hpc2" as (yt2b tl2b) "(Hparent2 & Hdll3 & %Hlen3 & %Hrepr3 & %Hcpar3)".
  iDestruct (own_dll_acc_node (DfracOwn 1) (split_cells cells k o rs) yt2b.(yjs.yType.start') tl2b k leftCell Hsck0 with "Hdll3")
    as (prevl2 nxtl2) "(%Hcloc2 & %Hcl2 & %Hcr2 & %Hrun2 & %Hclen2 & %Hpc2 & Hnode2 & Hback2)".
  iDestruct "Hnode2" as (iv2 olid2 orid2)
    "(Hcval2 & Hcol2 & Hcor2 & %Hinl2 & %Hinr2 & %Hid2n & %Hcont2 & %Hpar2 & %Hprev2 & %Hnext2 & %Hflags2)".
  have Hid2 : item_id (run_head leftCell) = toYjsId iv2.(yjs.item.id').
  { symmetry. exact Hid2n. }
  have Hkey : iv2.(yjs.item.id').(yjs.id.clientId') = kc.
  { move: Hid2. rewrite Hrhcl' Hid /toYjsId /=. move=> Heq.
    have Hc1 := f_equal clientId Heq. simpl in Hc1. rewrite /kc. clear -Hc1. word. }
  have Hkeyck : iv2.(yjs.item.id').(yjs.id.clock') = itemVal.(yjs.item.id').(yjs.id.clock').
  { move: Hid2. rewrite Hrhcl' Hid /toYjsId /=. move=> Heq.
    have Hc1 := f_equal clock Heq. simpl in Hc1. clear -Hc1. word. }
  iEval (rewrite Hclloc) in "Hcval2".
  wp_auto.
  wp_apply (wp_map_lookup1 with "Hmap"). iIntros "Hmap".
  rewrite Hkey Hslk /=.
  wp_auto.
  rewrite Hkeyck.
  iEval (rewrite -Hclloc) in "Hcval2".
  iAssert (own_item_node (ic_loc leftCell) (DfracOwn 1) (input_of_run (cell_run leftCell))
             (ic_deleted leftCell) (ic_parent leftCell) prevl2 nxtl2) with "[Hcval2 Hcol2 Hcor2]" as "Hnode2".
  { iExists iv2, olid2, orid2. iFrame "Hcval2 Hcol2 Hcor2".
    iPureIntro. split_and!;
      [exact Hinl2 | exact Hinr2 | exact Hid2n | exact Hcont2 | exact Hpar2
      | exact Hprev2 | exact Hnext2 | exact Hflags2]. }
  iDestruct ("Hback2" with "Hnode2") as "Hdll3".
  iAssert (own_ytype_cells parent (DfracOwn 1) (split_cells cells k o rs) (tm_arr tm)) with "[Hparent2 Hdll3]" as "Hyt2b".
  { iExists yt2b, tl2b. iFrame "Hparent2 Hdll3". iPureIntro.
    split_and!; [exact Hlen3 | exact Hrepr3 | exact Hcpar3]. }
  iDestruct ("Hclose2" with "[Hyt2b]") as "Htypes2"; first (iFrame "Hyt2b"; iPureIntro; exact Harrinv2).
  (* ----- getNodeIndex over the split run, then the append-based surgery ----- *)
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
  have Hmem_half : ∀ c, c ∈ run_half → c ∈ all_cells types2.
  { move=> c Hc. apply list_elem_of_lookup_1 in Hc as [j Hj]. rewrite /run_half in Hj.
    apply list_lookup_insert_Some in Hj as [(_ & <- & _) | (Hne & Hj)].
    - rewrite Hperm2. apply list_elem_of_here.
    - have HcL : c ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hj.
      have Hcne : c ≠ cw. { move=> Heq. rewrite Heq in Hj. exact (Hne (NoDup_lookup _ _ _ _ Hndrun Hkw Hj)). }
      have Hcall : c ∈ all_cells types := proj1 (proj1 (client_run_mem types kc c) HcL).
      rewrite Hperm1 in Hcall. apply elem_of_cons in Hcall as [Heq | Hrest]; [done |].
      rewrite Hperm2. apply elem_of_cons; right. apply elem_of_cons; right. exact Hrest. }
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
  have Hrun_half : sorted_client_run types2 kc run_half.
  { split_and!; [exact Hss_half | rewrite Hlocs; exact HndLocRun |].
    move=> c Hc. apply client_run_mem. split; [exact (Hmem_half c Hc) |].
    destruct (Hsub c Hc) as [-> | HcL]; [rewrite Hclcli; exact Hcwcc |].
    exact (proj2 (proj1 (client_run_mem types kc c) HcL)). }
  have Hpool2 : pool_invs types2
    := pool_invs_split types parent cells (tm_arr tm) k cw o rs Htypes Hcellk Hrun Hdiff Hckbnd Hrsfresh Hpool.
  iEval (rewrite -Hlocs) in "Hslice".
  wp_apply (wp_getNodeIndex slk (DfracOwn 1) types2 kc run_half (itemVal.(yjs.item.id').(yjs.id.clock')) Hrun_half Hpool2 with "[$Hslice $Htypes2]").
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
  have Hsck : split_cells cells k o rs !! k = Some leftCell := split_cells_lookup_left cells k o rs cw Hcellk.
  have Hlk3 : types2 !! parent = Some (MkTypeState (split_cells cells k o rs) (tm_arr tm)) by apply lookup_insert_eq.
  iDestruct (big_sepM_lookup_acc _ _ parent (MkTypeState (split_cells cells k o rs) (tm_arr tm)) Hlk3 with "Htypes2") as "[(Hpc3 & %Harrinv3) Hclose3]".
  iDestruct "Hpc3" as (yt3 tl3) "(Hparent3 & Hdll4 & %Hlen4 & %Hrepr4 & %Hcpar4)".
  iDestruct (own_dll_acc_node (DfracOwn 1) (split_cells cells k o rs) yt3.(yjs.yType.start') tl3 k leftCell Hsck with "Hdll4")
    as (prevl3 nxtl3) "(%Hcloc3 & %Hcl3 & %Hcr3 & %Hrun3 & %Hclen3 & %Hpc3 & Hnode3 & Hback3)".
  iDestruct "Hnode3" as (iv3 olid3 orid3)
    "(Hcval3 & Hcol3 & Hcor3 & %Hinl3 & %Hinr3 & %Hid3n & %Hcont3 & %Hpar3 & %Hprev3 & %Hnext3 & %Hflags3)".
  have Hid3 : item_id (run_head leftCell) = toYjsId iv3.(yjs.item.id').
  { symmetry. exact Hid3n. }
  iEval (rewrite Hclloc) in "Hcval3".
  have Hkey3 : iv3.(yjs.item.id').(yjs.id.clientId') = kc.
  { move: Hid3. rewrite Hrhcl' Hid /toYjsId /=. move=> Heq.
    have Hc1 := f_equal clientId Heq. simpl in Hc1. rewrite /kc.
    clear -Hc1. word. }
  wp_auto.
  wp_apply (wp_map_insert with "Hmap").
  iIntros "Hmap".
  iEval (rewrite Hkey3) in "Hmap".
  iEval (rewrite -Hclloc) in "Hcval3".
  iAssert (own_item_node (ic_loc leftCell) (DfracOwn 1) (input_of_run (cell_run leftCell))
             (ic_deleted leftCell) (ic_parent leftCell) prevl3 nxtl3) with "[Hcval3 Hcol3 Hcor3]" as "Hnode3".
  { iExists iv3, olid3, orid3. iFrame "Hcval3 Hcol3 Hcor3".
    iPureIntro. split_and!;
      [exact Hinl3 | exact Hinr3 | exact Hid3n | exact Hcont3 | exact Hpar3
      | exact Hprev3 | exact Hnext3 | exact Hflags3]. }
  iDestruct ("Hback3" with "Hnode3") as "Hdll4".
  iAssert (own_ytype_cells parent (DfracOwn 1) (split_cells cells k o rs) (tm_arr tm)) with "[Hparent3 Hdll4]" as "Hyt3b".
  { iExists yt3, tl3. iFrame "Hparent3 Hdll4". iPureIntro.
    split_and!; [exact Hlen4 | exact Hrepr4 | exact Hcpar4]. }
  iDestruct ("Hclose3" with "[Hyt3b]") as "Htypes2"; first (iFrame "Hyt3b"; iPureIntro; exact Harrinv3).
  (* the item-map model surgery: the right half's loc lands at position kw+1 *)
  have Hkp : cell_kp <$> all_cells types2 ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp rightCell].
  { etransitivity; [apply Permutation_map; exact Hperm2 |].
    etransitivity; last (apply Permutation_app_tail; apply Permutation_map; symmetry; exact Hperm1).
    simpl. rewrite -/leftCell -/rightCell Hkpcl. apply perm_skip. apply Permutation_cons_append. }
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
  have Hrun_eq := client_run_loc_insert types types2 rightCell (kw + 1) Hkp Hclkloc Hbef Haft.
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
  have Hdecomp : forall c0, c0 ∈ all_cells types2 -> c0 ∈ all_cells types \/ c0 = leftCell \/ c0 = rightCell.
  { move=> c0 Hc0. rewrite Hperm2 in Hc0.
    apply elem_of_cons in Hc0 as [-> | Hc0]; [by right; left |].
    apply elem_of_cons in Hc0 as [-> | Hc0]; [by right; right |].
    left. rewrite Hperm1. apply elem_of_cons. by right. }
  have Hcomplete2 : forall c0 : w64, c0 ∈ cell_client <$> all_cells types2 -> is_Some (<[kc := newSl]> gm !! c0).
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
  have Hclkloc2 : forall c1 c2, c1 ∈ all_cells types2 -> c2 ∈ all_cells types2 -> cell_client c1 = cell_client c2 -> (cell_pr c1).1 = (cell_pr c2).1 -> c1.(ic_loc) = c2.(ic_loc).
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
  iAssert (own_item_map mref (DfracOwn 1) types2) with "[Hmap HnewNodes HnewCap Hruns]" as "Hitemmap2".
  { iExists (<[kc := newSl]> gm). iFrame "Hmap".
    iSplitL "HnewNodes HnewCap Hruns".
    - rewrite big_sepM_insert_delete. iSplitL "HnewNodes HnewCap"; [iFrame |].
      iDestruct (big_sepM_delete _ _ kc slk Hslk with "Hruns") as "[_ Hrest]".
      iApply (big_sepM_impl with "Hrest").
      iIntros "!#" (client s0 Hcs) "H". iNamed "H".
      have Hne2 : client ≠ cell_client rightCell.
      { rewrite Hcccr Hcwcc. move=> Heqc. rewrite Heqc lookup_delete_eq in Hcs. discriminate. }
      rewrite (client_run_loc_other types types2 rightCell client Hkp Hclkloc Hne2). iFrame.
    - iPureIntro. split; [exact Hcomplete2 | exact Hclkloc2]. }
  wp_auto.
  have Hreg' : registry_coh bind types2 := registry_coh_insert bind types parent _ _ Htypes Hreg0.
  iApply ("HΦ" $! rs).
  iSplitL "Hclient Hclock HdeletedSet Hitemsf Hitemmap2 Hregistry Htypes2 Hpending Hpdeletes"; last first.
  { iPureIntro. split; [exact Hrsnn |].
    rewrite -(locs_of_types_of_locs_pool locs p (proj1 Haligned) Hprem) locs_of_concat. exact Hrsfresh. }
  have Haligned' : locs_aligned (<[parent := split_locs ls k rs]> locs)
                     (<[parent := MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm)]> p).
  { apply (locs_aligned_insert_both locs p parent (split_locs ls k rs)
             (MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm))); last exact Haligned.
    rewrite /split_locs Hlk /split_runs Hr /= !length_app /= !length_take !length_drop Hlsl //. }
  iApply (own_store_runs_intro_state _ _ _ _ _ _ _ _ Haligned').
  iEval (rewrite /state_of_runs /=
           (types_of_locs_pool_insert_both locs p parent (split_locs ls k rs)
              (MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm))) /=
           (cells_of_locs_runs_split parent ls (tm_runs tm) k o l rs r Hlsl Hlk Hr) -/cells).
  iApply (own_store_struct_intro _ (MkStoreState client0 k0 types2 bind pend pdel)
            (conj Hpool2 Hreg') with "Hclient Hclock HdeletedSet [Hitemsf Hitemmap2] Hregistry Htypes2 Hpending Hpdeletes").
  iExists mref. iFrame "Hitemsf Hitemmap2".
Qed.



(** [store.splitAtAndGetLeft] at run granularity: make the char [idv],
    covered by the [k]-th run of the type at [parent] (the node at [lc]),
    END a node. Nothing changes when [idv] is the run's last char; else the
    node is split just after [idv] and the truncated left half keeps its
    address. Either way the node at [lc] comes back and the pool and the
    address map step by [pool_split_left_step] (index-explicit; the
    boundary it pins is [pool_split_left_step_ends_at], and it weakens to
    [pool_after_split] through [pool_split_step_of_left]). Proved directly
    from [wp_store__GetNode_runs] and [wp_store__splitNode_runs]. *)
Lemma wp_store__splitAtAndGetLeft_runs (s : loc) (idv : yjs.id.t) (str : store_state_runs)
    (parent : loc) (tm : type_model) (ls : list loc) (k : nat) (r : ItemRun) (lc : loc) :
  sr_pool str !! parent = Some tm ->
  sr_locs str !! parent = Some ls ->
  tm_runs tm !! k = Some r ->
  ls !! k = Some lc ->
  run_covers r (toYjsId idv) ->
  {{{ is_pkg_init yjs ∗ own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetLeft" #idv
  {{{ (p' : pool) (locs' : gmap loc (list loc)), RET (#lc, #true);
      own_store_runs s (str <| sr_pool := p' |> <| sr_locs := locs' |>) ∗
      ⌜pool_split_left_step (sr_pool str) (sr_locs str) parent k (toYjsId idv) p' locs'⌝ }}}.
Proof using Type*.
  move=> Hp Hls Hr Hlk Hcov.
  destruct str as [client0 k0 locs p bind pend pdel]. simpl in *.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  have Hcovp : pool_run_covers p parent k (toYjsId idv) by (exists tm, r).
  wp_apply (wp_store__GetNode_runs s idv (MkStoreStateRuns client0 k0 locs p bind pend pdel)
              with "[$Hpkg $Hruns]").
  iIntros (nl ok) "(Hruns & %Hres)". simpl in Hres.
  destruct ok; last first.
  { exfalso. exact (Hres parent k Hcovp). }
  destruct Hres as (q' & k' & Hcov' & Hloc').
  iDestruct (own_store_runs_covers_unique with "Hruns") as %Huniq.
  destruct (Huniq _ _ _ _ _ Hcov' Hcovp) as [-> ->].
  rewrite Hls /= Hlk in Hloc'. injection Hloc' as <-.
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf.
  iDestruct (own_store_runs_run_pool_invs with "Hruns") as %Hrinv.
  have Hrmem : r ∈ all_runs p.
  { apply (elem_of_all_runs p r). exists parent, tm. split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hr)]. }
  have Hrwf : run_wf (run_items r) := Hwf r Hrmem.
  have Hrfits : run_fits r := proj1 Hrinv r Hrmem.
  wp_auto.
  iDestruct (own_store_runs_node_acc s (MkStoreStateRuns client0 k0 locs p bind pend pdel)
               parent ls tm k lc r Hls Hp Hlk Hr with "Hruns") as (ivR) "H".
  iNamed "H".
  (* the parent pin names [parent]; [wp_if_destruct]'s bare [subst] would take it *)
  clear Haccpar.
  (* the node's clock and length, at the [uint.Z] level ([wp_if_destruct]'s
     bare [subst] must not eat an equation naming a variable) *)
  have Hivclk : uint.Z ivR.(yjs.item.id').(yjs.id.clock') = Z.of_nat (run_clock r).
  { rewrite /run_clock Haccid /toYjsId /=. word. }
  destruct Hcov as (Hcl & Hlo & Hhi). rewrite /toYjsId /= in Hcl Hlo Hhi.
  have Hlenpos : (1 <= length (run_items r))%nat.
  { destruct Hrwf as [Hne _]. destruct (run_items r); [done | simpl; lia]. }
  have Hrfits' : (Z.of_nat (run_clock r) + Z.of_nat (length (run_items r)) < 2^64)%Z := Hrfits.
  have Hosub : uint.Z (w64_word_instance.(word.sub) idv.(yjs.id.clock') ivR.(yjs.item.id').(yjs.id.clock'))
             = Z.of_nat (uint.nat idv.(yjs.id.clock') - run_clock r)%nat.
  { move: Hivclk Hlo. word. }
  wp_auto.
  wp_apply (wp_item__Len lc (DfracOwn 1) ivR with "[$Haccval]"). iIntros "Haccval".
  iDestruct ("Haccback" with "Haccval") as "Hruns".
  rewrite Haccle.
  wp_auto.
  wp_if_destruct.
  - (* offset = Len-1: the run already ends at [idv]; no split *)
    iApply ("HΦ" $! p locs). simpl.
    iFrame "Hruns". iPureIntro.
    exists tm, ls, r. split_and!; [exact Hp | exact Hls | exact Hr |].
    left. split_and!; [| done | done].
    move: Hosub Hlo Hhi Hrfits'. rewrite /toYjsId /=. word.
  - (* the id sits strictly inside the run: split just after it *)
    have Hnlt : (uint.nat idv.(yjs.id.clock') - run_clock r < length (run_items r) - 1)%nat.
    { move: Hosub Hlo Hhi Hrfits'. rewrite /toYjsId /=. word. }
    have Hdiffnat : uint.nat (w64_word_instance.(word.add)
                      (w64_word_instance.(word.sub) idv.(yjs.id.clock') ivR.(yjs.item.id').(yjs.id.clock'))
                      (W64 1))
                  = (uint.nat idv.(yjs.id.clock') - run_clock r + 1)%nat.
    { move: Hosub Hnlt Hrfits' Hlenpos. word. }
    have Hdiffb : (0 < uint.nat (w64_word_instance.(word.add)
                      (w64_word_instance.(word.sub) idv.(yjs.id.clock') ivR.(yjs.item.id').(yjs.id.clock'))
                      (W64 1)) < length (run_items r))%nat.
    { rewrite Hdiffnat. lia. }
    wp_apply (wp_store__splitNode_runs s (MkStoreStateRuns client0 k0 locs p bind pend pdel)
                parent lc ls tm k r _ Hp Hls Hr Hlk Hdiffb with "[$Hpkg $Hruns]").
    iIntros (rloc) "(Hruns & %Hfresh)". simpl in Hfresh.
    wp_auto.
    iApply ("HΦ" $! _ _). simpl.
    iFrame "Hruns". iPureIntro.
    exists tm, ls, r. split_and!; [exact Hp | exact Hls | exact Hr |].
    right. split; [exact Hnlt |].
    exists rloc. split_and!; [exact (proj1 Hfresh) | exact (proj2 Hfresh) | | done].
    rewrite Hdiffnat /toYjsId //=.
Qed.

(** [store.splitAtAndGetRight] at run granularity: make the char [idv],
    covered by the [k]-th run of the type at [parent] (the node at [lc]),
    START a node. Nothing changes when [idv] is the run's head and the node
    itself comes back; else the node is split at [idv] and the fresh right
    half comes back. The returned address and the step are
    [pool_split_right_step] (the boundary it pins is
    [pool_split_right_step_starts_at]). Proved directly from
    [wp_store__GetNode_runs] and [wp_store__splitNode_runs]. *)
Lemma wp_store__splitAtAndGetRight_runs (s : loc) (idv : yjs.id.t) (str : store_state_runs)
    (parent : loc) (tm : type_model) (ls : list loc) (k : nat) (r : ItemRun) (lc : loc) :
  sr_pool str !! parent = Some tm ->
  sr_locs str !! parent = Some ls ->
  tm_runs tm !! k = Some r ->
  ls !! k = Some lc ->
  run_covers r (toYjsId idv) ->
  {{{ is_pkg_init yjs ∗ own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetRight" #idv
  {{{ (l : loc) (p' : pool) (locs' : gmap loc (list loc)), RET (#l, #true);
      own_store_runs s (str <| sr_pool := p' |> <| sr_locs := locs' |>) ∗
      ⌜pool_split_right_step (sr_pool str) (sr_locs str) parent k (toYjsId idv) l p' locs'⌝ }}}.
Proof using Type*.
  move=> Hp Hls Hr Hlk Hcov.
  destruct str as [client0 k0 locs p bind pend pdel]. simpl in *.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  have Hcovp : pool_run_covers p parent k (toYjsId idv) by (exists tm, r).
  wp_apply (wp_store__GetNode_runs s idv (MkStoreStateRuns client0 k0 locs p bind pend pdel)
              with "[$Hpkg $Hruns]").
  iIntros (nl ok) "(Hruns & %Hres)". simpl in Hres.
  destruct ok; last first.
  { exfalso. exact (Hres parent k Hcovp). }
  destruct Hres as (q' & k' & Hcov' & Hloc').
  iDestruct (own_store_runs_covers_unique with "Hruns") as %Huniq.
  destruct (Huniq _ _ _ _ _ Hcov' Hcovp) as [-> ->].
  rewrite Hls /= Hlk in Hloc'. injection Hloc' as <-.
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf.
  iDestruct (own_store_runs_run_pool_invs with "Hruns") as %Hrinv.
  have Hrmem : r ∈ all_runs p.
  { apply (elem_of_all_runs p r). exists parent, tm. split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hr)]. }
  have Hrwf : run_wf (run_items r) := Hwf r Hrmem.
  have Hrfits : run_fits r := proj1 Hrinv r Hrmem.
  wp_auto.
  iDestruct (own_store_runs_node_acc s (MkStoreStateRuns client0 k0 locs p bind pend pdel)
               parent ls tm k lc r Hls Hp Hlk Hr with "Hruns") as (ivR) "H".
  iNamed "H".
  (* the parent pin names [parent]; [wp_if_destruct]'s bare [subst] would take it *)
  clear Haccpar.
  have Hivclk : uint.Z ivR.(yjs.item.id').(yjs.id.clock') = Z.of_nat (run_clock r).
  { rewrite /run_clock Haccid /toYjsId /=. word. }
  destruct Hcov as (Hcl & Hlo & Hhi). rewrite /toYjsId /= in Hcl Hlo Hhi.
  have Hlenpos : (1 <= length (run_items r))%nat.
  { destruct Hrwf as [Hne _]. destruct (run_items r); [done | simpl; lia]. }
  have Hrfits' : (Z.of_nat (run_clock r) + Z.of_nat (length (run_items r)) < 2^64)%Z := Hrfits.
  have Hosub : uint.Z (w64_word_instance.(word.sub) idv.(yjs.id.clock') ivR.(yjs.item.id').(yjs.id.clock'))
             = Z.of_nat (uint.nat idv.(yjs.id.clock') - run_clock r)%nat.
  { move: Hivclk Hlo. word. }
  wp_auto.
  wp_if_destruct.
  - (* offset > 0: split at the offset, return the fresh right half *)
    iDestruct ("Haccback" with "Haccval") as "Hruns".
    have Hopos : (0 < uint.nat idv.(yjs.id.clock') - run_clock r)%nat.
    { move: Hosub. word. }
    have Hdiffnat : uint.nat (w64_word_instance.(word.sub) idv.(yjs.id.clock') ivR.(yjs.item.id').(yjs.id.clock'))
                  = (uint.nat idv.(yjs.id.clock') - run_clock r)%nat.
    { move: Hosub. word. }
    have Hdiffb : (0 < uint.nat (w64_word_instance.(word.sub) idv.(yjs.id.clock') ivR.(yjs.item.id').(yjs.id.clock'))
                   < length (run_items r))%nat.
    { rewrite Hdiffnat. lia. }
    wp_apply (wp_store__splitNode_runs s (MkStoreStateRuns client0 k0 locs p bind pend pdel)
                parent lc ls tm k r _ Hp Hls Hr Hlk Hdiffb with "[$Hpkg $Hruns]").
    iIntros (rloc) "(Hruns & %Hfresh)". simpl in Hfresh.
    wp_auto.
    iApply ("HΦ" $! rloc _ _). simpl.
    iFrame "Hruns". iPureIntro.
    exists tm, ls, r, lc. split_and!; [exact Hp | exact Hls | exact Hr | exact Hlk |].
    right. split_and!; [exact Hopos | exact (proj1 Hfresh) | exact (proj2 Hfresh) | | done].
    rewrite Hdiffnat //.
  - (* offset = 0: the run already starts at [idv]; no split *)
    iDestruct ("Haccback" with "Haccval") as "Hruns".
    iApply ("HΦ" $! lc p locs). simpl.
    iFrame "Hruns". iPureIntro.
    exists tm, ls, r, lc. split_and!; [exact Hp | exact Hls | exact Hr | exact Hlk |].
    left. split_and!; [| done | done | done].
    rewrite /toYjsId /=. move: Hosub. word.
Qed.

End store_update.
