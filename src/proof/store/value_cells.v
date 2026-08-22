(** The [store] VALUE layer, part 1: the CELL BOOKKEEPING the store invariant
    is stated over. Go values but no Iris.

    Definitions
    - [type_state] / [all_cells]: what the invariant tracks per registered
      yType (its DLL cells and its model list), and the cells across the whole
      registry.
    - the per-client node list: [cell_client] / [cell_clock] / [cell_le] /
      [cell_pr] / [cell_kp] and [client_run], the sorted run of one client's
      cells that shadows [store.items].
    - the pool invariants: location [NoDup], clock-range disjointness
      ([cells_range_disjoint]), [cell_fits], [cell_origin_clk], bundled as
      [pool_invs].
    - the registry coherence side conditions [doc_registry_coh] and
      [inputs_rooted_in_bind].

    Laws
    - the pool invariants are preserved by appending a fresh cell ([*_snoc])
      and by any permutation that keeps locations and runs
      ([locs_run_perm_*], [flip_locs_run_perm] / [pool_invs_flip] /
      [flip_pool_perm] for the tombstone flip). These are the two shapes every
      store operation takes.
    - [all_cells] under a registry insert ([all_cells_insert(_snoc/_empty)],
      [all_cells_lookup]).
    - [client_run] is stable under the same steps ([merge_sort_loc_*],
      [client_run_loc_tail] / [_insert] / [_other], [cellctr_locs_run_perm]),
      and [cell_kp] determines client, clock, location and [cell_pr].

    The rest of the value layer: [store/value_live.v] (the live-cell
    refinement and the tombstone set), [store/value_split.v] (the split
    surgery), [store/value_span.v] (id ranges and wire spans). The Iris layer
    over all of it is [store/heap.v]. *)

From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude network_model.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
Local Open Scope Z_scope.
From New.proof.store Require Import model.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.
From New.proof.ytype Require Import model value heap.

Section store_value_cells.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* ===== definitions ======================================================== *)

(* ----- one registered type's state -------------------------------------- *)

(** What [store_inv] tracks per registered YType (keyed by its [parent] loc): the
    DLL cells and the model item list. *)
Record type_state := MkTypeState {
  ty_cells : list item_cell;
  ty_arr   : list (YjsItem A);
}.

(** A cell head's same-client left origin strictly precedes it in clock
    (causal creation order, issue #28 stage C1b): the premise of
    [block_query_head], which lets the scan's whole-run span query collapse
    to [set_find_integration_block_step]'s head-only accumulator test. Only the HEAD's
    origin needs the invariant: tail chars' origins are in-run by [run_wf].
    Local inserts satisfy it by the clock counter; remote integrations by
    per-client causal delivery (the update batch's freshness bound). *)
Definition cell_origin_clk (c : item_cell) : Prop :=
  ∀ originId, origin_id (origin (run_head c)) = Some originId →
    clientId originId = clientId (item_id (run_head c)) →
    (clock originId < clock (item_id (run_head c)))%nat.

(* reader/lock agreement on the [types] map (concurrent read API); declared here,
   after [type_state], since it mentions it. *)

(** All cells across all types (the document-global item pool). *)
Definition all_cells (types : gmap loc type_state) : list item_cell :=
  concat (ty_cells <$> (map_to_list types).*2).

(* ----- the store's item set: map[Client][]*item ------------------------- *)

(** Client / clock a cell's id carries — read off the cell's model item id (a
    [YjsId], whose [nat] fields round-trip through [W64] from the original heap
    id), so [own_item_map] can speak about clocks while owning only the map, not
    the item cells. *)
Definition cell_client (c : item_cell) : w64 := W64 (clientId (item_id (run_head c))).

Definition cell_clock  (c : item_cell) : w64 := W64 (clock (item_id (run_head c))).

Definition cell_le (a b : item_cell) : Prop := (uint.Z (cell_clock a) ≤ uint.Z (cell_clock b))%Z.

#[local] Instance cell_le_dec : RelDecision cell_le.
Proof. rewrite /cell_le. solve_decision. Defined.

#[local] Instance cell_le_trans : Transitive cell_le.
Proof. rewrite /cell_le. move=> x y z. lia. Qed.

#[local] Instance cell_le_total : Total cell_le.
Proof. rewrite /cell_le. move=> x y. lia. Qed.

(** [client_run types client]: [client]'s items across every type, CLOCK-sorted
    — exactly the Go run list [store.items[client]] (AddNode appends in
    integration = clock order). Defining it by [merge_sort] makes sortedness
    DEFINITIONAL: [own_item_map] needs no existential / permutation clause, and
    (clocks being unique per client) the result is the unique clock ordering.
    Preserved per insert by [maximalId] (a fresh max-clock item lands at the
    sorted tail). *)
Definition client_run (types : gmap loc type_state) (client : w64) : list item_cell :=
  merge_sort cell_le (filter (λ c, cell_client c = client) (all_cells types)).

(** [own_item_map]'s backing slice is [ic_loc <$> ...] of a [merge_sort cell_le]
    run, so its content depends only on each cell's (clock, loc) pair. These two
    lemmas express that the loc-sequence of a clock-sorted run is preserved (a)
    under any reshuffle with the same (clock, loc) multiset and (b) when a
    strictly-clock-maximal cell is appended at the tail. *)
Definition cell_pr (c : item_cell) : Z * loc := (uint.Z (cell_clock c), ic_loc c).

Definition pr_le (p q : Z * loc) : Prop := (p.1 <= q.1)%Z.

(* ----- the part-6 pool invariants (issue #28): loc NoDup + range disjointness *)

(** Per-client clock-RANGE disjointness of the document cell pool: two distinct
    same-client cells occupy disjoint clock intervals [clock, clock + len).
    This is [wp_store__splitNode]'s [Hdisj] hypothesis shape: it pins the
    covering cell [getNodeIndex] returns uniquely once runs are multi-char. *)
Definition cells_range_disjoint (pool : list item_cell) : Prop :=
  ∀ c1 c2, c1 ∈ pool → c2 ∈ pool →
    cell_client c1 = cell_client c2 → ic_loc c1 ≠ ic_loc c2 →
    (uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)) ≤ uint.Z (cell_clock c2))%Z ∨
    (uint.Z (cell_clock c2) + Z.of_nat (length (ic_run c2)) ≤ uint.Z (cell_clock c1))%Z.

(** A cell's clock range [clock, clock + len) fits in [w64] arithmetic without
    wrapping (issue #28 part 6). This is the run-aware strengthening of the
    per-cell [+ 1 < 2^64] no-wrap: [getNodeIndex] computes [middleClock + Len()]
    and the conflict scan's [idSpan] range test computes [clock + len], both in
    [w64], so every pooled cell must satisfy it. It cannot be derived per call
    on the [Text.Insert] path (the public spec carries no premise about remote
    clients' clocks), hence it lives in the store invariant. *)
Definition cell_fits (c : item_cell) : Prop :=
  (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z.

(** [cell_kp] bundles a cell's (client, clock, loc). The slice/run preservation
    consumes a [cell_kp] multiset permutation; on this base the integrate splice
    gives an EXACT [item_cell] permutation [cells' ≡ₚ cells ++ [new]] (the cell
    carries only the model item + loc, both invariant under the neighbour relink
    that lives existentially in [own_dll]), so the [cell_kp] permutation follows by
    [fmap]. *)
Definition cell_kp (c : item_cell) : w64 * (Z * loc) := (cell_client c, cell_pr c).

(** [inputs_rooted_in_bind inputs bind]: every origin-free tagged input targets
    a root name that is already bound in [bind]. An op with neither a left nor a
    right origin attaches directly under a registered root, so that root must
    exist for the op to integrate. *)
Definition inputs_rooted_in_bind (inputs : list (TId * IntegrateInput (A := A)))
    (bind : gmap P loc) : Prop :=
  ∀ typedInput, typedInput ∈ inputs ->
    in_originId typedInput.2 = None -> in_rightOriginId typedInput.2 = None ->
    ∃ name, typedInput.1 = RootId name ∧ is_Some (bind !! name).

(** The store's *registry coherence*: the name->loc bindings [bind], the
    per-type heap state [types], and the replayed doc model [m] fit together:
    every bound name has a live type and vice versa, [bind] is injective, the
    model agrees with each bound type's item list, and the model is populated
    only at bound names. This is exactly the [bind]/[types]/[m] invariant
    [store_inv] maintains inline; naming it keeps [own_store] (and through
    it the [applyUpdate] spec) readable instead of a wall of raw quantified
    side conditions. *)
Definition doc_registry_coh (m : DocModel) (bind : gmap P loc)
    (types : gmap loc type_state) : Prop :=
  (∀ nm p, bind !! nm = Some p -> is_Some (types !! p)) /\
  (∀ n1 n2 p, bind !! n1 = Some p -> bind !! n2 = Some p -> n1 = n2) /\
  (∀ p, is_Some (types !! p) -> ∃ nm, bind !! nm = Some p) /\
  (∀ nm p ts, bind !! nm = Some p -> types !! p = Some ts ->
     doc_model_get m (RootId nm) = ty_arr ts) /\
  (∀ t, doc_model_get m t ≠ [] -> ∃ nm p, t = RootId nm /\ bind !! nm = Some p).

(** [pool_invs types]: the invariants of the document cell pool that the model
    does not determine: every cell's clock range fits in [w64] ([cell_fits]),
    node locations are distinct, same-client cells occupy disjoint clock
    ranges ([cells_range_disjoint]) and every head's same-client origin is
    strictly older ([cell_origin_clk]). Carried by [store_inv] / [own_store]
    and preserved by every store method; the splice ([*_snoc]) and the
    tombstone flip ([pool_invs_flip]) are its two transition laws. *)
Definition pool_invs (types : gmap loc type_state) : Prop :=
  (∀ c, c ∈ all_cells types -> cell_fits c) ∧
  NoDup (ic_loc <$> all_cells types) ∧
  cells_range_disjoint (all_cells types) ∧
  (∀ c, c ∈ all_cells types -> cell_origin_clk c).

(* ===== lemmas ============================================================= *)

(** [NoDup] of the pool's locations survives an integrate splice: the pool
    grows by exactly one cell at a fresh location ([all_cells_fresh]). *)
Lemma nodup_locs_snoc (pool1 pool2 : list item_cell) (c : item_cell) :
  pool2 ≡ₚ pool1 ++ [c] ->
  ic_loc c ∉ ic_loc <$> pool1 ->
  NoDup (ic_loc <$> pool1) ->
  NoDup (ic_loc <$> pool2).
Proof.
  move=> Hperm Hfresh Hnd.
  rewrite Hperm fmap_app /=.
  apply NoDup_app. split_and!; [exact Hnd | | apply NoDup_singleton].
  move=> x Hx Hx1. apply list_elem_of_singleton in Hx1. subst x. done.
Qed.

(** Both pool invariants only read a cell's location and run; transport them
    across a pool reshuffle preserving those (what [Text.Delete]'s
    [ic_deleted] flip is). *)
Lemma locs_run_perm_nodup (pool1 pool2 : list item_cell) :
  (λ c, (ic_loc c, ic_run c)) <$> pool2 ≡ₚ (λ c, (ic_loc c, ic_run c)) <$> pool1 ->
  NoDup (ic_loc <$> pool1) -> NoDup (ic_loc <$> pool2).
Proof.
  move=> Hperm Hnd.
  have Hcomp : ∀ (l : list item_cell), (fst ∘ (λ c, (ic_loc c, ic_run c))) <$> l = ic_loc <$> l.
  { elim => [//| a l' IH] /=. by f_equal. }
  have Hf : (fst ∘ (λ c, (ic_loc c, ic_run c))) <$> pool2 ≡ₚ (fst ∘ (λ c, (ic_loc c, ic_run c))) <$> pool1.
  { rewrite !list_fmap_compose Hperm //. }
  rewrite !Hcomp in Hf. by rewrite Hf.
Qed.

Lemma originclk_snoc (pool1 pool2 : list item_cell) (c : item_cell) :
  pool2 ≡ₚ pool1 ++ [c] ->
  cell_origin_clk c ->
  (∀ c0, c0 ∈ pool1 → cell_origin_clk c0) ->
  (∀ c0, c0 ∈ pool2 → cell_origin_clk c0).
Proof.
  move=> Hperm Hoc Hall c0 Hc0.
  rewrite Hperm in Hc0. apply elem_of_app in Hc0 as [Hc0 | Hc0].
  - exact (Hall c0 Hc0).
  - apply list_elem_of_singleton in Hc0 as ->. exact Hoc.
Qed.

(** [cell_origin_clk] only reads a cell's run; the same reshuffle transport
    as the other pool invariants. *)
Lemma locs_run_perm_originclk (pool1 pool2 : list item_cell) :
  (λ c, (ic_loc c, ic_run c)) <$> pool2 ≡ₚ (λ c, (ic_loc c, ic_run c)) <$> pool1 ->
  (∀ c, c ∈ pool1 → cell_origin_clk c) -> (∀ c, c ∈ pool2 → cell_origin_clk c).
Proof.
  move=> Hperm Hall c Hc.
  have Hin : (ic_loc c, ic_run c) ∈ ((λ c0, (ic_loc c0, ic_run c0)) <$> pool1).
  { rewrite -Hperm. exact (list_elem_of_fmap_2 _ _ _ Hc). }
  apply list_elem_of_fmap in Hin as (c' & Heq & Hc').
  have Hr : ic_run c = ic_run c' := f_equal snd Heq.
  have Hoc := Hall c' Hc'.
  rewrite /cell_origin_clk /run_head Hr. exact Hoc.
Qed.

Lemma ic_loc_fmap_pr (l : list item_cell) : ic_loc <$> l = snd <$> (cell_pr <$> l).
Proof. rewrite -list_fmap_compose. reflexivity. Qed.

Lemma SS_cell_pr_merge (l : list item_cell) :
  StronglySorted pr_le (cell_pr <$> merge_sort cell_le l).
Proof.
  apply (StronglySorted_fmap cell_pr cell_le pr_le).
  - move=> x y Hxy. rewrite /pr_le /cell_pr /cell_le in Hxy |- *. exact Hxy.
  - apply (StronglySorted_merge_sort cell_le).
Qed.

Lemma merge_sort_loc_perm (l1 l2 : list item_cell) :
  (∀ x1 x2, x1 ∈ l1 → x2 ∈ l2 → (cell_pr x1).1 = (cell_pr x2).1 → ic_loc x1 = ic_loc x2) ->
  cell_pr <$> l1 ≡ₚ cell_pr <$> l2 ->
  ic_loc <$> merge_sort cell_le l1 = ic_loc <$> merge_sort cell_le l2.
Proof.
  move=> Hkd Hperm.
  rewrite (ic_loc_fmap_pr (merge_sort cell_le l1)) (ic_loc_fmap_pr (merge_sort cell_le l2)).
  f_equal.
  apply (StronglySorted_unique_strong pr_le).
  - move=> p1 p2 Hp1 Hp2 H12 H21.
    apply list_elem_of_fmap in Hp1 as (x1 & -> & Hx1).
    apply list_elem_of_fmap in Hp2 as (x2 & -> & Hx2).
    rewrite (merge_sort_Permutation cell_le l1) in Hx1.
    rewrite (merge_sort_Permutation cell_le l2) in Hx2.
    rewrite /pr_le in H12 H21.
    have Hkeq : (cell_pr x1).1 = (cell_pr x2).1 by lia.
    rewrite /cell_pr /=. f_equal; [exact Hkeq | exact (Hkd x1 x2 Hx1 Hx2 Hkeq)].
  - apply SS_cell_pr_merge.
  - apply SS_cell_pr_merge.
  - rewrite (merge_sort_Permutation cell_le l1) (merge_sort_Permutation cell_le l2). exact Hperm.
Qed.

Lemma merge_sort_loc_snoc (L : list item_cell) (x : item_cell) :
  (∀ y1 y2, y1 ∈ L → y2 ∈ L → (cell_pr y1).1 = (cell_pr y2).1 → ic_loc y1 = ic_loc y2) ->
  (∀ y, y ∈ L → ((cell_pr y).1 < (cell_pr x).1)%Z) ->
  ic_loc <$> merge_sort cell_le (L ++ [x]) = (ic_loc <$> merge_sort cell_le L) ++ [ic_loc x].
Proof.
  move=> Hkd Hmax.
  rewrite (ic_loc_fmap_pr (merge_sort cell_le (L ++ [x]))) (ic_loc_fmap_pr (merge_sort cell_le L)).
  replace ((snd <$> (cell_pr <$> merge_sort cell_le L)) ++ [ic_loc x])
    with (snd <$> ((cell_pr <$> merge_sort cell_le L) ++ [cell_pr x]))
    by (rewrite fmap_app /=; reflexivity).
  f_equal.
  apply (StronglySorted_unique_strong pr_le).
  - move=> p1 p2 Hp1 Hp2 H12 H21.
    apply list_elem_of_fmap in Hp1 as (x1 & -> & Hx1).
    rewrite (merge_sort_Permutation cell_le (L ++ [x])) in Hx1.
    apply elem_of_app in Hp2 as [Hp2 | Hp2].
    + apply list_elem_of_fmap in Hp2 as (x2 & -> & Hx2).
      rewrite (merge_sort_Permutation cell_le L) in Hx2.
      rewrite /pr_le in H12 H21.
      have Hkeq : (cell_pr x1).1 = (cell_pr x2).1 by lia.
      apply elem_of_app in Hx1 as [Hx1L | Hx1x].
      * rewrite /cell_pr /=. f_equal; [exact Hkeq | exact (Hkd x1 x2 Hx1L Hx2 Hkeq)].
      * apply list_elem_of_singleton in Hx1x as ->. exfalso. have := Hmax x2 Hx2. rewrite /pr_le in H12 H21. lia.
    + apply list_elem_of_singleton in Hp2 as ->.
      rewrite /pr_le in H12 H21.
      apply elem_of_app in Hx1 as [Hx1L | Hx1x].
      * exfalso. have := Hmax x1 Hx1L. lia.
      * apply list_elem_of_singleton in Hx1x as ->. reflexivity.
  - apply SS_cell_pr_merge.
  - apply StronglySorted_app_2.
    + move=> p z Hp Hz. apply list_elem_of_singleton in Hz as ->.
      apply list_elem_of_fmap in Hp as (y & -> & Hy). rewrite (merge_sort_Permutation cell_le L) in Hy.
      rewrite /pr_le. have := Hmax y Hy. lia.
    + apply SS_cell_pr_merge.
    + repeat constructor.
  - rewrite (merge_sort_Permutation cell_le (L ++ [x])) fmap_app /=.
    apply Permutation_app; [| reflexivity].
    apply Permutation_map. symmetry. apply (merge_sort_Permutation cell_le L).
Qed.

Lemma merge_sort_loc_insert (L : list item_cell) (x : item_cell) (i : nat) :
  (∀ y1 y2, y1 ∈ L → y2 ∈ L → (cell_pr y1).1 = (cell_pr y2).1 → ic_loc y1 = ic_loc y2) ->
  (∀ y, y ∈ take i (merge_sort cell_le L) → ((cell_pr y).1 < (cell_pr x).1)%Z) ->
  (∀ y, y ∈ drop i (merge_sort cell_le L) → ((cell_pr x).1 < (cell_pr y).1)%Z) ->
  ic_loc <$> merge_sort cell_le (L ++ [x])
  = take i (ic_loc <$> merge_sort cell_le L) ++ ic_loc x :: drop i (ic_loc <$> merge_sort cell_le L).
Proof.
  move=> Hkd Hbef Haft.
  remember (merge_sort cell_le L) as S eqn:HS.
  have HinL : ∀ z, z ∈ S -> z ∈ L.
  { move=> z Hz. rewrite HS in Hz. by rewrite (merge_sort_Permutation cell_le L) in Hz. }
  have HinS_take : ∀ z, z ∈ take i S -> z ∈ S.
  { move=> z Hz. rewrite -(take_drop i S). apply elem_of_app. by left. }
  have HinS_drop : ∀ z, z ∈ drop i S -> z ∈ S.
  { move=> z Hz. rewrite -(take_drop i S). apply elem_of_app. by right. }
  have HSSp : StronglySorted pr_le (cell_pr <$> S).
  { rewrite HS. apply SS_cell_pr_merge. }
  have HABeq : cell_pr <$> S = (cell_pr <$> take i S) ++ (cell_pr <$> drop i S).
  { by rewrite -fmap_app take_drop. }
  have HpermSL : cell_pr <$> S ≡ₚ cell_pr <$> L.
  { rewrite HS. apply Permutation_map. apply (merge_sort_Permutation cell_le L). }
  have Hpr : cell_pr <$> merge_sort cell_le (L ++ [x])
           = (cell_pr <$> take i S) ++ cell_pr x :: (cell_pr <$> drop i S).
  { apply (StronglySorted_unique_strong pr_le).
    - move=> p1 p2 Hp1 Hp2 H12 H21.
      have Hkeq : p1.1 = p2.1 by (rewrite /pr_le in H12 H21; lia).
      apply list_elem_of_fmap in Hp1 as (x1 & -> & Hx1).
      rewrite (merge_sort_Permutation cell_le (L ++ [x])) in Hx1.
      have Hp2c : (∃ x2, p2 = cell_pr x2 ∧ x2 ∈ S) ∨ p2 = cell_pr x.
      { apply elem_of_app in Hp2 as [Hp2 | Hp2].
        - apply list_elem_of_fmap in Hp2 as (x2 & -> & Hx2).
          left. exists x2. split; [reflexivity | exact (HinS_take x2 Hx2)].
        - apply elem_of_cons in Hp2 as [-> | Hp2]; [by right |].
          apply list_elem_of_fmap in Hp2 as (x2 & -> & Hx2).
          left. exists x2. split; [reflexivity | exact (HinS_drop x2 Hx2)]. }
      apply elem_of_app in Hx1 as [Hx1L | Hx1x]; last apply list_elem_of_singleton in Hx1x as ->.
      + destruct Hp2c as [(x2 & -> & Hx2S) | ->].
        * have Hx2L := HinL x2 Hx2S.
          rewrite /cell_pr /=. rewrite /cell_pr /= in Hkeq. f_equal;
            [exact Hkeq | exact (Hkd x1 x2 Hx1L Hx2L Hkeq)].
        * exfalso.
          have Hx1S : x1 ∈ S.
          { rewrite HS. by rewrite (merge_sort_Permutation cell_le L). }
          rewrite -(take_drop i S) in Hx1S. apply elem_of_app in Hx1S as [Ht | Hd].
          -- have := Hbef x1 Ht. lia.
          -- have := Haft x1 Hd. lia.
      + destruct Hp2c as [(x2 & -> & Hx2S) | ->]; [| reflexivity].
        exfalso.
        rewrite -(take_drop i S) in Hx2S. apply elem_of_app in Hx2S as [Ht | Hd].
        * have := Hbef x2 Ht. lia.
        * have := Haft x2 Hd. lia.
    - apply SS_cell_pr_merge.
    - apply StronglySorted_app_2.
      + move=> a c Ha Hc.
        apply list_elem_of_fmap in Ha as (ya & -> & Hya).
        apply elem_of_cons in Hc as [-> | Hc].
        * rewrite /pr_le. have := Hbef ya Hya. lia.
        * apply list_elem_of_fmap in Hc as (yc & -> & Hyc).
          rewrite /pr_le. have := Hbef ya Hya. have := Haft yc Hyc. lia.
      + rewrite HABeq in HSSp. exact (StronglySorted_app_1_l _ _ _ HSSp).
      + change (cell_pr x :: (cell_pr <$> drop i S)) with ([cell_pr x] ++ (cell_pr <$> drop i S)).
        apply StronglySorted_app_2.
        * move=> a c Ha Hc. apply list_elem_of_singleton in Ha as ->.
          apply list_elem_of_fmap in Hc as (yc & -> & Hyc).
          rewrite /pr_le. have := Haft yc Hyc. lia.
        * repeat constructor.
        * rewrite HABeq in HSSp. exact (StronglySorted_app_1_r _ _ _ HSSp).
    - transitivity ((cell_pr <$> L) ++ [cell_pr x]).
      { rewrite (merge_sort_Permutation cell_le (L ++ [x])) fmap_app //. }
      symmetry. transitivity (cell_pr x :: (cell_pr <$> S)).
      { rewrite -Permutation_middle -HABeq //. }
      rewrite HpermSL.
      by rewrite Permutation_cons_append. }
  rewrite (ic_loc_fmap_pr (merge_sort cell_le (L ++ [x]))) Hpr.
  rewrite fmap_app fmap_cons -!ic_loc_fmap_pr -fmap_take -fmap_drop.
  done.
Qed.

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

(** Updating one registered type's cell list reshuffles the document-global cell
    pool [all_cells] only at that type. *)
Lemma all_cells_insert (types : gmap loc type_state) (parent : loc) (ts ts' : type_state) :
  types !! parent = Some ts ->
  all_cells (<[parent:=ts']> types) ≡ₚ ty_cells ts' ++ all_cells (delete parent types).
Proof.
  move=> Hp. rewrite /all_cells.
  apply (concat_perm (ty_cells <$> (map_to_list (<[parent:=ts']> types)).*2)
                     (ty_cells ts' :: (ty_cells <$> (map_to_list (delete parent types)).*2))).
  rewrite (map_to_list_insert_existing types parent ts ts' Hp). simpl. reflexivity.
Qed.

Lemma all_cells_lookup (types : gmap loc type_state) (parent : loc) (ts : type_state) :
  types !! parent = Some ts ->
  all_cells types ≡ₚ ty_cells ts ++ all_cells (delete parent types).
Proof.
  move=> Hp.
  pose proof (all_cells_insert types parent ts ts Hp) as H.
  rewrite (insert_id types parent ts Hp) in H. exact H.
Qed.

(** Replacing the registered type at [parent] by one whose cell list is the old
    one with one cell [c] appended (modulo permutation) grows the document-global
    cell pool by exactly [c]. This is the cell-pool view of [Store.Integrate]'s
    splice ([cells' ≡ₚ cells ++ [c]]): the inserted item adds a single cell, and
    the neighbour relink (invisible to the abstract cells) moves nothing else. It
    feeds both the wrapper's [cell_kp] growth and [Text.Insert]'s loop-carried
    heap-clock bound. *)
Lemma all_cells_insert_snoc (types : gmap loc type_state) (parent : loc)
    (cells arr cells' arr' : list _) (c : item_cell) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells' ≡ₚ cells ++ [c] ->
  all_cells (<[parent := MkTypeState cells' arr']> types) ≡ₚ all_cells types ++ [c].
Proof.
  move=> Hp Hperm.
  rewrite (all_cells_insert types parent (MkTypeState cells arr) (MkTypeState cells' arr') Hp).
  rewrite (all_cells_lookup types parent (MkTypeState cells arr) Hp).
  simpl. rewrite Hperm.
  rewrite -!app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
Qed.

(** Registering a fresh EMPTY type (no cells) leaves the document-global cell
    pool unchanged up to permutation: [getOrCreateYType]'s miss branch (issue
    #54) adds a [type_state] with [ty_cells = []], contributing nothing to
    [all_cells]. Every per-cell pool invariant (NoDup / range-disjointness /
    fits / origin-clk / counter) and [own_item_map] (a function of
    [cell_kp <$> all_cells] up to permutation) therefore survive the grow. *)
Lemma all_cells_insert_empty (types : gmap loc type_state) (parent : loc)
    (arr : list (YjsItem A)) :
  types !! parent = None ->
  all_cells (<[parent := MkTypeState [] arr]> types) ≡ₚ all_cells types.
Proof.
  move=> Hp. rewrite /all_cells.
  apply (concat_perm (ty_cells <$> (map_to_list (<[parent := MkTypeState [] arr]> types)).*2)
                     ([] :: (ty_cells <$> (map_to_list types).*2))).
  rewrite (map_to_list_insert types parent (MkTypeState [] arr) Hp). simpl. reflexivity.
Qed.

(** Range disjointness survives an integrate splice whose new cell's range sits
    fully above every same-client range (the range-aware maximality that the
    insert counter / remote-op freshness provides). *)
Lemma rangedisj_snoc (pool1 pool2 : list item_cell) (c : item_cell) :
  pool2 ≡ₚ pool1 ++ [c] ->
  (∀ c0, c0 ∈ pool1 → cell_client c0 = cell_client c →
     (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) ≤ uint.Z (cell_clock c))%Z) ->
  cells_range_disjoint pool1 ->
  cells_range_disjoint pool2.
Proof.
  move=> Hperm Hmax Hdisj c1 c2 Hc1 Hc2 Hcc Hne.
  rewrite Hperm in Hc1 Hc2.
  apply elem_of_app in Hc1 as [Hc1 | Hc1]; apply elem_of_app in Hc2 as [Hc2 | Hc2].
  - exact (Hdisj c1 c2 Hc1 Hc2 Hcc Hne).
  - apply list_elem_of_singleton in Hc2 as ->. left. exact (Hmax c1 Hc1 Hcc).
  - apply list_elem_of_singleton in Hc1 as ->. right. apply (Hmax c2 Hc2). symmetry. exact Hcc.
  - apply list_elem_of_singleton in Hc1 as ->. apply list_elem_of_singleton in Hc2 as ->. done.
Qed.

Lemma locs_run_perm_rangedisj (pool1 pool2 : list item_cell) :
  (λ c, (ic_loc c, ic_run c)) <$> pool2 ≡ₚ (λ c, (ic_loc c, ic_run c)) <$> pool1 ->
  cells_range_disjoint pool1 -> cells_range_disjoint pool2.
Proof.
  move=> Hperm Hdisj c1 c2 Hc1 Hc2 Hcc Hne.
  have Hlift : ∀ c', c' ∈ pool2 → ∃ c'', c'' ∈ pool1 ∧
      ic_loc c' = ic_loc c'' ∧ ic_run c' = ic_run c''.
  { move=> c' Hc'.
    have Hin : (ic_loc c', ic_run c') ∈ ((λ c0, (ic_loc c0, ic_run c0)) <$> pool1).
    { rewrite -Hperm. exact (list_elem_of_fmap_2 _ _ _ Hc'). }
    apply list_elem_of_fmap in Hin as (c'' & Heq & Hc'').
    exists c''. split; [exact Hc'' |].
    split; [exact (f_equal fst Heq) | exact (f_equal snd Heq)]. }
  destruct (Hlift c1 Hc1) as (c1' & Hc1' & Hl1 & Hr1).
  destruct (Hlift c2 Hc2) as (c2' & Hc2' & Hl2 & Hr2).
  have Hcl1 : cell_client c1' = cell_client c1 by (rewrite /cell_client /run_head -Hr1 //).
  have Hcl2 : cell_client c2' = cell_client c2 by (rewrite /cell_client /run_head -Hr2 //).
  have Hck1 : cell_clock c1' = cell_clock c1 by (rewrite /cell_clock /run_head -Hr1 //).
  have Hck2 : cell_clock c2' = cell_clock c2 by (rewrite /cell_clock /run_head -Hr2 //).
  have Hd := Hdisj c1' c2' Hc1' Hc2' ltac:(rewrite Hcl1 Hcl2 //) ltac:(rewrite -Hl1 -Hl2 //).
  rewrite Hck1 Hck2 -Hr1 -Hr2 in Hd. exact Hd.
Qed.

(** [cell_fits] only reads a cell's run; the same reshuffle transport as the
    other two pool invariants. *)
Lemma locs_run_perm_fits (pool1 pool2 : list item_cell) :
  (λ c, (ic_loc c, ic_run c)) <$> pool2 ≡ₚ (λ c, (ic_loc c, ic_run c)) <$> pool1 ->
  (∀ c, c ∈ pool1 → cell_fits c) -> (∀ c, c ∈ pool2 → cell_fits c).
Proof.
  move=> Hperm Hfits c Hc.
  have Hin : (ic_loc c, ic_run c) ∈ ((λ c0, (ic_loc c0, ic_run c0)) <$> pool1).
  { rewrite -Hperm. exact (list_elem_of_fmap_2 _ _ _ Hc). }
  apply list_elem_of_fmap in Hin as (c' & Heq & Hc').
  have Hr : ic_run c = ic_run c' := f_equal snd Heq.
  have Hf := Hfits c' Hc'.
  rewrite /cell_fits /cell_clock /run_head Hr. exact Hf.
Qed.

(** The [(loc, run)] projection of the pool is what all four pool invariants
    read, and tombstoning changes neither: [flip_cell] only sets the Deleted
    bit. So a flip transports [pool_invs] wholesale. *)
Lemma flip_locs_run_perm (types : gmap loc type_state) (p : loc)
    (ts : type_state) (k : nat) (c : item_cell) :
  types !! p = Some ts -> ty_cells ts !! k = Some c ->
  (λ c0, (ic_loc c0, ic_run c0))
    <$> all_cells (<[p := MkTypeState (<[k := flip_cell c]> (ty_cells ts)) (ty_arr ts)]> types)
  ≡ₚ (λ c0, (ic_loc c0, ic_run c0)) <$> all_cells types.
Proof.
  move=> Hp Hck.
  rewrite (all_cells_insert types p ts _ Hp) (all_cells_lookup types p ts Hp).
  rewrite !fmap_app. apply Permutation_app_tail.
  simpl. rewrite list_fmap_insert /flip_cell /=.
  rewrite list_insert_id; first reflexivity.
  rewrite list_lookup_fmap Hck //.
Qed.

(** [cell_kp] is a function of the [(loc, run)] projection, so the [own_item_map]
    side of a flip transports on the same permutation. *)
Lemma locs_run_perm_kp (pool1 pool2 : list item_cell) :
  (λ c, (ic_loc c, ic_run c)) <$> pool2 ≡ₚ (λ c, (ic_loc c, ic_run c)) <$> pool1 ->
  cell_kp <$> pool2 ≡ₚ cell_kp <$> pool1.
Proof.
  move=> Hperm.
  have Hfac : ∀ l : list item_cell, cell_kp <$> l
      = (λ pr : loc * list (YjsItem A),
           (W64 (clientId (item_id (hd inhabitant pr.2))),
            (uint.Z (W64 (clock (item_id (hd inhabitant pr.2)))), pr.1)))
        <$> ((λ c, (ic_loc c, ic_run c)) <$> l).
  { move=> l. rewrite -list_fmap_compose //. }
  rewrite !Hfac Hperm //.
Qed.

Lemma pool_invs_flip (types : gmap loc type_state) (p : loc)
    (ts : type_state) (k : nat) (c : item_cell) :
  types !! p = Some ts -> ty_cells ts !! k = Some c ->
  pool_invs types ->
  pool_invs (<[p := MkTypeState (<[k := flip_cell c]> (ty_cells ts)) (ty_arr ts)]> types).
Proof.
  move=> Hp Hck [Hfits [Hnodup [Hdisj Horig]]].
  have Hlr := flip_locs_run_perm types p ts k c Hp Hck.
  split_and!.
  - exact (locs_run_perm_fits _ _ Hlr Hfits).
  - exact (locs_run_perm_nodup _ _ Hlr Hnodup).
  - exact (locs_run_perm_rangedisj _ _ Hlr Hdisj).
  - exact (locs_run_perm_originclk _ _ Hlr Horig).
Qed.

(** The cell-level form of the flip: the pool is the same list with the
    tombstoned cell in place of the live one. [flip_locs_run_perm] above is
    the (location, run) projection of this and cannot see the flipped bit,
    which is precisely what [live_refine_flip] needs. *)
Lemma flip_pool_perm (types : gmap loc type_state) (p : loc)
    (ts : type_state) (k : nat) (c : item_cell) :
  types !! p = Some ts -> ty_cells ts !! k = Some c ->
  ∃ rest : list item_cell,
    all_cells types ≡ₚ c :: rest ∧
    all_cells (<[p := MkTypeState (<[k := flip_cell c]> (ty_cells ts)) (ty_arr ts)]> types)
      ≡ₚ flip_cell c :: rest.
Proof.
  move=> Hp Hck.
  exists (take k (ty_cells ts) ++ drop (S k) (ty_cells ts) ++ all_cells (delete p types)).
  split.
  - rewrite (all_cells_lookup types p ts Hp).
    rewrite -{1}(take_drop_middle (ty_cells ts) k c Hck).
    rewrite -app_assoc /=. rewrite -Permutation_middle //.
  - rewrite (all_cells_insert types p ts _ Hp) /=.
    rewrite (insert_take_drop (ty_cells ts) k (flip_cell c)
               (lookup_lt_Some _ _ _ Hck)).
    rewrite -app_assoc /=. rewrite -Permutation_middle //.
Qed.

(** [cell_fits] survives an integrate splice: membership transport over the
    snoc permutation. *)
Lemma fits_snoc (pool1 pool2 : list item_cell) (c : item_cell) :
  pool2 ≡ₚ pool1 ++ [c] ->
  cell_fits c ->
  (∀ c0, c0 ∈ pool1 → cell_fits c0) ->
  (∀ c0, c0 ∈ pool2 → cell_fits c0).
Proof.
  move=> Hperm Hfc Hfits c0 Hc0.
  rewrite Hperm in Hc0. apply elem_of_app in Hc0 as [Hc0 | Hc0].
  - exact (Hfits c0 Hc0).
  - apply list_elem_of_singleton in Hc0 as ->. exact Hfc.
Qed.

(** [cell_kp] projections: a cell's (client, clock, loc) is exactly what its
    key-pair records, so equal key-pairs give equal components. Used to transfer
    the run-map / clock-bound side conditions across a [cell_kp]-preserving
    reshuffle (what [Text.Delete]'s [ic_deleted] flip is — [flip_cell] touches
    neither [ic_run] nor [ic_loc], so [cell_kp (flip_cell c) = cell_kp c]). *)
Lemma cell_kp_client (a b : item_cell) : cell_kp a = cell_kp b -> cell_client a = cell_client b.
Proof. move=> H. exact (f_equal fst H). Qed.

Lemma cell_kp_pr (a b : item_cell) : cell_kp a = cell_kp b -> cell_pr a = cell_pr b.
Proof. move=> H. exact (f_equal snd H). Qed.

Lemma cell_kp_clock (a b : item_cell) : cell_kp a = cell_kp b -> uint.Z (cell_clock a) = uint.Z (cell_clock b).
Proof. move=> H. exact (f_equal (fun p => p.2.1) H). Qed.

Lemma cell_kp_loc (a b : item_cell) : cell_kp a = cell_kp b -> ic_loc a = ic_loc b.
Proof. move=> H. exact (f_equal snd (cell_kp_pr a b H)). Qed.

Lemma cell_kp_flip (c : item_cell) : cell_kp (flip_cell c) = cell_kp c.
Proof. reflexivity. Qed.

Lemma cell_pr_filter_kp (client : w64) (l : list item_cell) :
  cell_pr <$> filter (λ c, cell_client c = client) l
  = snd <$> filter (λ kp : w64 * (Z * loc), kp.1 = client) (cell_kp <$> l).
Proof.
  induction l as [|c l IH]; [reflexivity|].
  rewrite fmap_cons filter_cons filter_cons /cell_kp /=.
  case_decide as Hc.
  - rewrite fmap_cons IH /=. reflexivity.
  - exact IH.
Qed.

Lemma cell_pr_filter_perm (client : w64) (l1 l2 : list item_cell) :
  cell_kp <$> l1 ≡ₚ cell_kp <$> l2 ->
  cell_pr <$> filter (λ c, cell_client c = client) l1
  ≡ₚ cell_pr <$> filter (λ c, cell_client c = client) l2.
Proof.
  move=> H. rewrite !cell_pr_filter_kp. apply Permutation_map. rewrite H. reflexivity.
Qed.

(** Re-establishing the run after [Store.Integrate]'s [AddNode]: the new cell's
    loc lands at the TAIL of its client's clock-sorted run, and other clients'
    runs are untouched — at the loc-sequence level (what the slice stores), given
    the document-global [cell_kp] multiset grows by exactly the new cell ([Hkp])
    and clock determines loc per client ([Hclkloc], the [own_item_map] side cond).
    [Hmax] (the new cell is strictly clock-maximal for its client) puts it last. *)
Lemma client_run_loc_tail (types types2 : gmap loc type_state) (newcell : item_cell) :
  cell_kp <$> all_cells types2 ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp newcell] ->
  (∀ c1 c2, c1 ∈ all_cells types → c2 ∈ all_cells types → cell_client c1 = cell_client c2 →
            (cell_pr c1).1 = (cell_pr c2).1 → ic_loc c1 = ic_loc c2) ->
  (∀ c, c ∈ all_cells types → cell_client c = cell_client newcell → ((cell_pr c).1 < (cell_pr newcell).1)%Z) ->
  ic_loc <$> client_run types2 (cell_client newcell)
  = (ic_loc <$> client_run types (cell_client newcell)) ++ [ic_loc newcell].
Proof.
  move=> Hkp Hclkloc Hmax.
  set client := cell_client newcell.
  set Lpre := filter (λ c, cell_client c = client) (all_cells types).
  set Lpost := filter (λ c, cell_client c = client) (all_cells types2).
  have Hkp2 : cell_kp <$> all_cells types2 ≡ₚ cell_kp <$> (all_cells types ++ [newcell]).
  { rewrite fmap_app /=. exact Hkp. }
  have Hfilt : filter (λ c, cell_client c = client) (all_cells types ++ [newcell])
             = Lpre ++ [newcell].
  { rewrite filter_app /Lpre. f_equal. rewrite filter_cons.
    rewrite decide_True; [reflexivity | rewrite /client; reflexivity]. }
  have Hpermf : cell_pr <$> Lpost ≡ₚ (cell_pr <$> Lpre) ++ [cell_pr newcell].
  { rewrite /Lpost (cell_pr_filter_perm client (all_cells types2) (all_cells types ++ [newcell]) Hkp2).
    rewrite Hfilt fmap_app /=. reflexivity. }
  have Hkdl2 : ∀ x y, x ∈ Lpre ++ [newcell] → y ∈ Lpre ++ [newcell] →
                (cell_pr x).1 = (cell_pr y).1 → ic_loc x = ic_loc y.
  { move=> x y Hx Hy Hxy.
    have Hin : ∀ z, z ∈ Lpre ++ [newcell] → (z ∈ all_cells types ∧ cell_client z = client) ∨ z = newcell.
    { move=> z Hz. apply elem_of_app in Hz as [Hz | Hz].
      - left. rewrite /Lpre list_elem_of_filter in Hz. tauto.
      - right. by apply list_elem_of_singleton in Hz. }
    destruct (Hin x Hx) as [[Hxa Hxc] | ->]; destruct (Hin y Hy) as [[Hya Hyc] | ->].
    - apply (Hclkloc x y Hxa Hya); [rewrite Hxc Hyc // | exact Hxy].
    - exfalso. have := Hmax x Hxa Hxc. lia.
    - exfalso. have := Hmax y Hya Hyc. lia.
    - reflexivity. }
  have Hcross : ∀ x1 x2, x1 ∈ Lpost → x2 ∈ Lpre ++ [newcell] →
                  (cell_pr x1).1 = (cell_pr x2).1 → ic_loc x1 = ic_loc x2.
  { move=> x1 x2 Hx1 Hx2 H12.
    have Hp1 : cell_pr x1 ∈ cell_pr <$> Lpost by apply list_elem_of_fmap_2.
    rewrite Hpermf in Hp1.
    have Hp1' : cell_pr x1 ∈ cell_pr <$> (Lpre ++ [newcell]) by (rewrite fmap_app /=; exact Hp1).
    apply list_elem_of_fmap in Hp1' as (x2' & Hx1eq & Hx2').
    have Hloc1 : ic_loc x1 = ic_loc x2' by (rewrite /cell_pr /= in Hx1eq; injection Hx1eq; auto).
    rewrite Hloc1. apply (Hkdl2 x2' x2 Hx2' Hx2). rewrite -Hx1eq. exact H12. }
  rewrite /client_run -/client.
  rewrite (merge_sort_loc_perm Lpost (Lpre ++ [newcell]) Hcross).
  { rewrite (merge_sort_loc_snoc Lpre newcell).
    - reflexivity.
    - move=> y1 y2 Hy1 Hy2 Hk. rewrite /Lpre list_elem_of_filter in Hy1.
      rewrite /Lpre list_elem_of_filter in Hy2.
      apply (Hclkloc y1 y2 (proj2 Hy1) (proj2 Hy2)); [rewrite (proj1 Hy1) (proj1 Hy2) // | exact Hk].
    - move=> y Hy. rewrite /Lpre list_elem_of_filter in Hy. apply (Hmax y (proj2 Hy) (proj1 Hy)). }
  rewrite fmap_app /=. exact Hpermf.
Qed.

(** The insert-at-position-[i] analogue of [client_run_loc_tail]: when the new
    cell's clock is NOT maximal but sits strictly between the sorted-run cells
    at [i-1] and [i] (the two [take]/[drop] strict-clock premises), its loc lands
    at position [i]. This is the [store.splitNode] item-map effect: the right
    half is inserted just after its (unchanged-loc) left half in the client run.
    Wraps [merge_sort_loc_insert] the way the tail lemma wraps
    [merge_sort_loc_snoc]. *)
Lemma client_run_loc_insert (types types2 : gmap loc type_state) (newcell : item_cell) (i : nat) :
  cell_kp <$> all_cells types2 ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp newcell] ->
  (∀ c1 c2, c1 ∈ all_cells types → c2 ∈ all_cells types → cell_client c1 = cell_client c2 →
            (cell_pr c1).1 = (cell_pr c2).1 → ic_loc c1 = ic_loc c2) ->
  (∀ y, y ∈ take i (client_run types (cell_client newcell)) → ((cell_pr y).1 < (cell_pr newcell).1)%Z) ->
  (∀ y, y ∈ drop i (client_run types (cell_client newcell)) → ((cell_pr newcell).1 < (cell_pr y).1)%Z) ->
  ic_loc <$> client_run types2 (cell_client newcell)
  = take i (ic_loc <$> client_run types (cell_client newcell))
      ++ ic_loc newcell :: drop i (ic_loc <$> client_run types (cell_client newcell)).
Proof.
  move=> Hkp Hclkloc Hbef Haft.
  set client := cell_client newcell.
  set Lpre := filter (λ c, cell_client c = client) (all_cells types).
  set Lpost := filter (λ c, cell_client c = client) (all_cells types2).
  have Hkp2 : cell_kp <$> all_cells types2 ≡ₚ cell_kp <$> (all_cells types ++ [newcell]).
  { rewrite fmap_app /=. exact Hkp. }
  have Hfilt : filter (λ c, cell_client c = client) (all_cells types ++ [newcell])
             = Lpre ++ [newcell].
  { rewrite filter_app /Lpre. f_equal. rewrite filter_cons.
    rewrite decide_True; [reflexivity | rewrite /client; reflexivity]. }
  have Hpermf : cell_pr <$> Lpost ≡ₚ (cell_pr <$> Lpre) ++ [cell_pr newcell].
  { rewrite /Lpost (cell_pr_filter_perm client (all_cells types2) (all_cells types ++ [newcell]) Hkp2).
    rewrite Hfilt fmap_app /=. reflexivity. }
  have HLpre_CR : ∀ z, z ∈ Lpre → z ∈ client_run types client.
  { move=> z Hz. change (client_run types client) with (merge_sort cell_le Lpre).
    by rewrite (merge_sort_Permutation cell_le Lpre). }
  have Hkd_pre : ∀ y1 y2, y1 ∈ Lpre → y2 ∈ Lpre → (cell_pr y1).1 = (cell_pr y2).1 → ic_loc y1 = ic_loc y2.
  { move=> y1 y2 Hy1 Hy2 Hk. rewrite /Lpre list_elem_of_filter in Hy1.
    rewrite /Lpre list_elem_of_filter in Hy2.
    apply (Hclkloc y1 y2 (proj2 Hy1) (proj2 Hy2)); [rewrite (proj1 Hy1) (proj1 Hy2) // | exact Hk]. }
  have Hkdl2 : ∀ x y, x ∈ Lpre ++ [newcell] → y ∈ Lpre ++ [newcell] →
                (cell_pr x).1 = (cell_pr y).1 → ic_loc x = ic_loc y.
  { move=> x y Hx Hy Hxy.
    have Hin : ∀ z, z ∈ Lpre ++ [newcell] → (z ∈ all_cells types ∧ cell_client z = client) ∨ z = newcell.
    { move=> z Hz. apply elem_of_app in Hz as [Hz | Hz].
      - left. rewrite /Lpre list_elem_of_filter in Hz. tauto.
      - right. by apply list_elem_of_singleton in Hz. }
    destruct (Hin x Hx) as [[Hxa Hxc] | ->]; destruct (Hin y Hy) as [[Hya Hyc] | ->].
    - apply (Hclkloc x y Hxa Hya); [rewrite Hxc Hyc // | exact Hxy].
    - exfalso.
      have HxLpre : x ∈ Lpre by (rewrite /Lpre list_elem_of_filter; split; [exact Hxc | exact Hxa]).
      have HxS : x ∈ client_run types client := HLpre_CR x HxLpre.
      rewrite -(take_drop i (client_run types client)) in HxS. apply elem_of_app in HxS as [Ht|Hd].
      + have := Hbef x Ht. lia.
      + have := Haft x Hd. lia.
    - exfalso.
      have HyLpre : y ∈ Lpre by (rewrite /Lpre list_elem_of_filter; split; [exact Hyc | exact Hya]).
      have HyS : y ∈ client_run types client := HLpre_CR y HyLpre.
      rewrite -(take_drop i (client_run types client)) in HyS. apply elem_of_app in HyS as [Ht|Hd].
      + have := Hbef y Ht. lia.
      + have := Haft y Hd. lia.
    - reflexivity. }
  have Hcross : ∀ x1 x2, x1 ∈ Lpost → x2 ∈ Lpre ++ [newcell] →
                  (cell_pr x1).1 = (cell_pr x2).1 → ic_loc x1 = ic_loc x2.
  { move=> x1 x2 Hx1 Hx2 H12.
    have Hp1 : cell_pr x1 ∈ cell_pr <$> Lpost by apply list_elem_of_fmap_2.
    rewrite Hpermf in Hp1.
    have Hp1' : cell_pr x1 ∈ cell_pr <$> (Lpre ++ [newcell]) by (rewrite fmap_app /=; exact Hp1).
    apply list_elem_of_fmap in Hp1' as (x2' & Hx1eq & Hx2').
    have Hloc1 : ic_loc x1 = ic_loc x2' by (rewrite /cell_pr /= in Hx1eq; injection Hx1eq; auto).
    rewrite Hloc1. apply (Hkdl2 x2' x2 Hx2' Hx2). rewrite -Hx1eq. exact H12. }
  rewrite /client_run -/client.
  rewrite (merge_sort_loc_perm Lpost (Lpre ++ [newcell]) Hcross).
  { rewrite (merge_sort_loc_insert Lpre newcell i Hkd_pre).
    - reflexivity.
    - move=> y Hy. apply Hbef. exact Hy.
    - move=> y Hy. apply Haft. exact Hy. }
  rewrite fmap_app /=. exact Hpermf.
Qed.

Lemma client_run_loc_other (types types2 : gmap loc type_state) (newcell : item_cell) (c' : w64) :
  cell_kp <$> all_cells types2 ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp newcell] ->
  (∀ c1 c2, c1 ∈ all_cells types → c2 ∈ all_cells types → cell_client c1 = cell_client c2 →
            (cell_pr c1).1 = (cell_pr c2).1 → ic_loc c1 = ic_loc c2) ->
  c' ≠ cell_client newcell ->
  ic_loc <$> client_run types2 c' = ic_loc <$> client_run types c'.
Proof.
  move=> Hkp Hclkloc Hne.
  set Lpre := filter (λ c, cell_client c = c') (all_cells types).
  set Lpost := filter (λ c, cell_client c = c') (all_cells types2).
  have Hkp2 : cell_kp <$> all_cells types2 ≡ₚ cell_kp <$> (all_cells types ++ [newcell]).
  { rewrite fmap_app /=. exact Hkp. }
  have Hfilt : filter (λ c, cell_client c = c') (all_cells types ++ [newcell]) = Lpre.
  { rewrite filter_app /Lpre. rewrite filter_cons.
    rewrite decide_False; [rewrite app_nil_r // | move=> H; apply Hne; by rewrite H]. }
  have Hpermf : cell_pr <$> Lpost ≡ₚ cell_pr <$> Lpre.
  { rewrite /Lpost (cell_pr_filter_perm c' (all_cells types2) (all_cells types ++ [newcell]) Hkp2).
    rewrite Hfilt. reflexivity. }
  have Hcross : ∀ x1 x2, x1 ∈ Lpost → x2 ∈ Lpre → (cell_pr x1).1 = (cell_pr x2).1 → ic_loc x1 = ic_loc x2.
  { move=> x1 x2 Hx1 Hx2 H12.
    have Hp1 : cell_pr x1 ∈ cell_pr <$> Lpost by apply list_elem_of_fmap_2.
    rewrite Hpermf in Hp1.
    apply list_elem_of_fmap in Hp1 as (x2' & Hx1eq & Hx2').
    have Hloc1 : ic_loc x1 = ic_loc x2' by (rewrite /cell_pr /= in Hx1eq; injection Hx1eq; auto).
    rewrite Hloc1.
    rewrite /Lpre list_elem_of_filter in Hx2'. rewrite /Lpre list_elem_of_filter in Hx2.
    apply (Hclkloc x2' x2 (proj2 Hx2') (proj2 Hx2)); [rewrite (proj1 Hx2') (proj1 Hx2) // |].
    rewrite -Hx1eq. exact H12. }
  rewrite /client_run.
  apply (merge_sort_loc_perm Lpost Lpre Hcross Hpermf).
Qed.

(** The cell-clock range bound ([store_inv]'s [Hcellctr]) transfers across a
    (loc, run)-preserving reshuffle: client, clock, and run length all derive
    from the run. *)
Lemma cellctr_locs_run_perm (pool1 pool2 : list item_cell) (client k : w64) :
  (λ c, (ic_loc c, ic_run c)) <$> pool2 ≡ₚ (λ c, (ic_loc c, ic_run c)) <$> pool1 ->
  (∀ c, c ∈ pool1 → cell_client c = client →
     (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z k)%Z) ->
  (∀ c, c ∈ pool2 → cell_client c = client →
     (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z k)%Z).
Proof.
  move=> Hperm Hbnd c Hc Hcc.
  have Hin : (ic_loc c, ic_run c) ∈ ((λ c0, (ic_loc c0, ic_run c0)) <$> pool1).
  { rewrite -Hperm. exact (list_elem_of_fmap_2 _ _ _ Hc). }
  apply list_elem_of_fmap in Hin as (c' & Heq & Hc').
  have Hr : ic_run c = ic_run c' := f_equal snd Heq.
  have Hcc' : cell_client c' = client.
  { rewrite -Hcc /cell_client /run_head Hr //. }
  have Hb := Hbnd c' Hc' Hcc'.
  rewrite /cell_clock /run_head Hr. exact Hb.
Qed.

End store_value_cells.
