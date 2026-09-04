(** The [store] VALUE layer, part 3: the SPLIT SURGERY on abstract cells and
    the per-step transport records, over [store/value_cells.v] and
    [store/value_live.v].

    Definitions
    - the split surgery [split_cell_left] / [split_cell_right] / [split_cells],
      and its address-list half [split_locs]; across a split the pool's
      entries and address map go by [pool_entries_split] / [locs_wf_split].
    - the records one store step hands its caller: [split_types_update_rel] (one
      [splitNode]), [repair_types_update_rel] (the at-most-two splits of [repair])
      and [delete_types_update_rel] (the unbounded split-and-tombstone loop of the
      wire delete path).
    - what the node lookups and splits say about the pool: [pool_cell_covers]
      (a pool cell holds an id), [cell_covers_clock] (a clock within a run),
      [cell_starts_at] / [cell_ends_at] (the cell at a location begins / ends at an id),
      [fresh_loc] (a location no pool cell uses), and the [repair] contract
      [origins_covered] / [repair_parent] / [origins_split]; that contract at
      run granularity, [pool_origins_covered] / [pool_repair_parent] /
      [pool_origins_split] (slots [(q, k)] instead of cells, the addresses
      read off the address map).

    Laws
    - [pool_cell_covers] translates to the projected pool and back
      ([pool_cell_covers_to_run] / [pool_run_covers_to_cell]): what carries
      [GetNode]'s postcondition to [(locs, p)].
    - under parent coherence the location-keyed statements translate to slot
      indices and back: [cell_starts_at_to_run] / [cell_ends_at_to_run],
      [pool_run_starts_at_to_cell] / [pool_run_ends_at_to_cell], and both at
      ONE slot under the address [NoDup] ([cell_starts_ends_at_to_run]);
      [split_types_update_rel] projects onto [pool_after_split]
      ([split_types_update_rel_to_pool]), [repair_types_update_rel] onto
      [pool_after_repair] ([repair_types_update_rel_to_pool]) and
      [delete_types_update_rel] onto [pool_after_delete]
      ([delete_types_update_rel_to_pool], and back,
      [pool_after_delete_of_types]): what carries the splitAtAndGet,
      [repair] and delete-path postconditions to [(locs, p)].
    - the index-explicit split steps at [(locs, p)]: [pool_split_step] (one
      surgery or nothing, weakening to [pool_after_split] through
      [pool_after_split_of_split_step]) and the precise
      [pool_split_left_step] / [pool_split_right_step] the split helpers
      report ([pool_split_step_of_left] / [_of_right]; the boundary they pin,
      [pool_split_left_step_ends_at] / [pool_split_right_step_starts_at]);
      [split_locs] slot laws ([split_locs_lookup_left] / [_right]) and a
      run's head id as its client and clock ([run_head_item_id]).
    - the split projects along [cell_run] ([cell_run_split_left] /
      [cell_run_split_right], [split_cells_runs]; [cell_covers_clock_run]),
      the fresh node's address being all the pure [split_runs] does not see,
      and [split_locs] on the address list ([split_cells_locs]), and a
      split address list with a split run list materializes to the split
      cell list ([cells_of_locs_runs_split]);
      [runs_start_at] / [runs_end_at] over a projected cell list read back on
      the cells ([runs_start_at_fmap] / [runs_end_at_fmap]).
    - splitting a node is invisible to the model: [split_cells_flatten] and
      [split_cells_num_visible].
    - [delete_types_update_rel] is reflexive and transitive (which is what lets the
      delete loop compose one record per step), and is implied by a split step
      ([delete_types_update_rel_of_split]) and by a tombstone flip
      ([delete_types_update_rel_of_flip]).
    - [cell_covers_w64] reads [cell_covers] at a runtime id in [w64] arithmetic;
      [pool_cell_covers_loc]: one id lives in one node; [split_cell_right_head_id]:
      the id the right half of a split starts at.

    Sits above [store/value_cells.v] and [store/value_live.v]. *)

From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude algebra network_model.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
Local Open Scope Z_scope.
From New.proof.store Require Import model value_cells value_live value_span.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.
From New.proof.ytype Require Import model value heap.

Section store_value_split.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* ===== definitions ======================================================== *)

(* ===== the split surgery on abstract cells (issue #28 M2) ================
   Splitting a run node is pure cell surgery: the left half keeps the node
   location and the first [o] model items, the right half is a fresh node
   carrying the rest, and BOTH halves inherit the deleted bit and parent (the
   yjs splitItem semantics; y-octo drops the right half's flags, a reported
   divergence). The flatten and the visible count are unchanged, which is why
   every public predicate is invariant under splits. *)

Definition split_cell_left (c : item_cell) (o : nat) : item_cell :=
  MkItemCell (ic_loc c) (take o (ic_run c)) (ic_deleted c) (ic_parent c).

Definition split_cell_right (c : item_cell) (o : nat) (r_loc : loc) : item_cell :=
  MkItemCell r_loc (drop o (ic_run c)) (ic_deleted c) (ic_parent c).

Definition split_cells (cells : list item_cell) (k o : nat) (r_loc : loc) : list item_cell :=
  match cells !! k with
  | Some c => take k cells ++ [split_cell_left c o; split_cell_right c o r_loc] ++ drop (S k) cells
  | None => cells
  end.

(** The address-list half of the split: the left half keeps the node's
    address at [k], the fresh right half's address [r_loc] lands after it
    (what [split_cells] does to [ic_loc <$> cells], [split_cells_locs]). *)
Definition split_locs (ls : list loc) (k : nat) (r_loc : loc) : list loc :=
  match ls !! k with
  | Some l => take k ls ++ [l; r_loc] ++ drop (S k) ls
  | None => ls
  end.

(** [split_types_update_rel before after w]: what one [splitNode] step does to
    the type map, as everything a caller is told about the two maps. The
    clauses are of mixed character on purpose, because re-establishing the
    store invariant needs all of them: each type's model list and flattened
    run survive, no type disappears, one client's run list grows by at most
    one, cells away from the split location survive verbatim, a covered clock
    stays covered (with provenance for the two halves), a type of unit cells
    is untouched, every new cell sits inside an old one's range, and the live
    and dead chars refine ([live_refine] / [dead_chars_kept]).

    Used as: the postcondition of [wp_store__splitAtAndGetLeft] and
    [wp_store__splitAtAndGetRight], composed by [repair] into
    [repair_types_update_rel] and weakened by the delete loop into
    [delete_types_update_rel]. *)
Definition split_types_update_rel (before after : gmap loc type_state) (w : item_cell) : Prop :=
  (∀ p ts', after !! p = Some ts' ->
     ∃ ts, before !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
           run_flatten (ty_cells ts') = run_flatten (ty_cells ts)) ∧
  (∀ p, is_Some (before !! p) -> is_Some (after !! p)) ∧
  (∀ kc, (length (client_run after kc) <= S (length (client_run before kc)))%nat) ∧
  (∀ c, c ∈ all_cells before -> ic_loc c ≠ ic_loc w -> c ∈ all_cells after) ∧
  (∀ (ccl : w64) (clkZ : Z) (c : item_cell), c ∈ all_cells before ->
     cell_client c = ccl -> (uint.Z (cell_clock c) <= clkZ)%Z ->
     (clkZ < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z ->
     ∃ c', c' ∈ all_cells after ∧ cell_client c' = ccl ∧
           (uint.Z (cell_clock c') <= clkZ)%Z ∧
           (clkZ < uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')))%Z ∧
           ic_parent c' = ic_parent c ∧
           (c' = c ∨ (c = w ∧ (1 < length (ic_run w))%nat ∧
                      (ic_loc c' = ic_loc w ∨
                       ic_loc c' ∉ (ic_loc <$> all_cells before))))) ∧
  (∀ p ts ts', before !! p = Some ts -> after !! p = Some ts' ->
     Forall cell_unit (ty_cells ts) -> ts' = ts) ∧
  cells_within (all_cells before) (all_cells after) ∧
  live_refine before after ∧
  dead_chars_kept before after.

(** [repair_types_update_rel before after]: what [store.repair] does to the type
    map. The same shape as [split_types_update_rel] minus the clauses about a
    single split location, since repair performs up to two of them: each
    client's run list therefore grows by at most two.

    Used as: the postcondition of [wp_store__repair], consumed by
    [store/applyUpdate] to carry the pool invariants across the origin
    resolution. *)
Definition repair_types_update_rel (before after : gmap loc type_state) : Prop :=
  (∀ p ts', after !! p = Some ts' ->
     ∃ ts, before !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
           run_flatten (ty_cells ts') = run_flatten (ty_cells ts)) ∧
  (∀ p, is_Some (before !! p) -> is_Some (after !! p)) ∧
  (∀ kc, (length (client_run after kc) <= 2 + length (client_run before kc))%nat) ∧
  (∀ p ts ts', before !! p = Some ts -> after !! p = Some ts' ->
     Forall cell_unit (ty_cells ts) -> ts' = ts) ∧
  cells_within (all_cells before) (all_cells after) ∧
  live_refine before after.

(** [delete_types_update_rel before after]: what the wire delete path does to the
    type map (issue #133). Both surgeries it performs, a split and a
    tombstone, are model no-ops, so the per-type model lists are untouched and
    no type disappears; the live chars only shrink and the dead ones stay dead
    ([live_refine] / [dead_chars_kept]).

    It carries NO run-length bound, unlike the two above, because the delete
    loop splits an unbounded number of times. That is also what makes it
    TRANSITIVE, which is what lets the loop compose one of these per iteration
    instead of tracking the whole surgery at once.

    Used as: the postcondition of [wp_store__deleteRange] and
    [wp_store__applyDeleteSpans], and the source of the [dead_chars_kept] step
    the delete loop needs to carry its coverage record forward. *)
Definition delete_types_update_rel (before after : gmap loc type_state) : Prop :=
  (∀ p ts', after !! p = Some ts' ->
     ∃ ts, before !! p = Some ts ∧ ty_arr ts' = ty_arr ts) ∧
  (∀ p, is_Some (before !! p) -> is_Some (after !! p)) ∧
  live_refine before after ∧
  dead_chars_kept before after ∧
  cells_within (all_cells before) (all_cells after).

(* ===== what lookups and splits say about the pool ======================= *)

(** [cell_covers_clock c k]: the run of [c] has a char with clock [k], whatever
    the client ([getNodeIndex] searches one client's run). *)
Definition cell_covers_clock (c : item_cell) (k : nat) : Prop :=
  (clock (item_id (run_head c)) <= k)%nat ∧
  (k < clock (item_id (run_head c)) + length (ic_run c))%nat.

(** [pool_cell_covers types c d]: [c] is a cell of the pool [types] and its run
    has the char with id [d]. *)
Definition pool_cell_covers (types : gmap loc type_state) (c : item_cell) (d : YjsId) : Prop :=
  c ∈ all_cells types ∧ cell_covers c d.

(** [cell_starts_at types parent l d]: the pool [types] holds, under the type
    [parent], a cell at location [l] whose first char has id [d]. *)
Definition cell_starts_at (types : gmap loc type_state) (parent l : loc) (d : YjsId) : Prop :=
  ∃ c, c ∈ all_cells types ∧ ic_loc c = l ∧ ic_parent c = parent ∧
       item_id (run_head c) = d.

(** [cell_ends_at types parent l d]: the pool [types] holds, under the type
    [parent], a cell at location [l] whose last char has id [d]. *)
Definition cell_ends_at (types : gmap loc type_state) (parent l : loc) (d : YjsId) : Prop :=
  ∃ c, c ∈ all_cells types ∧ ic_loc c = l ∧ ic_parent c = parent ∧
       clientId (item_id (run_head c)) = clientId d ∧
       (clock (item_id (run_head c)) + length (ic_run c) = clock d + 1)%nat.

(** [fresh_loc l types]: [l] is a non-null location no cell of the pool [types]
    lives at (where a split puts its new right half). *)
Definition fresh_loc (l : loc) (types : gmap loc type_state) : Prop :=
  l ≠ null ∧ l ∉ ic_loc <$> all_cells types.

(** [locs_fresh l ls]: [l] is a non-null location outside every type's
    address list: [fresh_loc] read at the address map alone
    ([fresh_loc_locs] is the transport along [locs_of]). *)
Definition locs_fresh (l : loc) (ls : gmap loc (list loc)) : Prop :=
  l ≠ null ∧ (∀ q lsq, ls !! q = Some lsq -> l ∉ lsq).

(** [origin_covered types o oc]: the optional origin id [o] resolves to the
    optional cell [oc]: both absent, or [oc] the pool cell whose run has [o]. *)
Definition origin_covered (types : gmap loc type_state) (o : option YjsId)
    (oc : option item_cell) : Prop :=
  match o, oc with
  | Some d, Some c => pool_cell_covers types c d
  | None, None => True
  | _, _ => False
  end.

(** [origins_covered types input ocL ocR]: both origins of [input] resolve in
    the pool ([origin_covered]), and when they fall in one cell the left origin
    precedes the right one in clock (so splitting at the left origin leaves the
    right one in place). *)
Definition origins_covered (types : gmap loc type_state) (input : IntegrateInput (A := A))
    (ocL ocR : option item_cell) : Prop :=
  origin_covered types (in_originId input) ocL ∧
  origin_covered types (in_rightOriginId input) ocR ∧
  match in_originId input, in_rightOriginId input, ocL, ocR with
  | Some a, Some b, Some cL0, Some cR0 => cL0 = cR0 -> (clock a < clock b)%nat
  | _, _, _, _ => True
  end.

(** [repair_parent bind opn ocL ocR p_t]: the type a repaired item lands in:
    the root bound to its wire parent name when it carries one, otherwise the
    type of its left, else right, origin cell. *)
Definition repair_parent (bind : gmap P loc) (opn : option go_string)
    (ocL ocR : option item_cell) (p_t : loc) : Prop :=
  match opn with
  | Some nm => bind !! nm = Some p_t
  | None => match ocL with
            | Some c => p_t = ic_parent c
            | None => match ocR with
                      | Some c => p_t = ic_parent c
                      | None => False
                      end
            end
  end.

(** [origins_split types input ocL ocR lft rgt]: after [repair] the item's
    [left] is the origin cell's location, now a cell ending at the left origin
    (in the origin cell's type), and its [right] a cell starting at the right
    origin; an absent origin links to [null]. *)
Definition origins_split (types : gmap loc type_state) (input : IntegrateInput (A := A))
    (ocL ocR : option item_cell) (lft rgt : loc) : Prop :=
  match in_originId input, ocL with
  | Some d, Some c0 => lft = ic_loc c0 ∧ cell_ends_at types (ic_parent c0) lft d
  | None, None => lft = null
  | _, _ => False
  end ∧
  match in_rightOriginId input, ocR with
  | Some d, Some c0 => cell_starts_at types (ic_parent c0) rgt d
  | None, None => rgt = null
  | _, _ => False
  end.

(** [pool_origin_covered p o or]: the optional origin id [o] resolves at run
    granularity to the optional pool slot [or = Some (q, k)]: the [k]-th run
    of the type at [q] has the char [o]. [origin_covered] with the cell
    named by its indices. *)
Definition pool_origin_covered (p : pool) (o : option YjsId)
    (or : option (loc * nat)) : Prop :=
  match o, or with
  | Some d, Some qk => pool_run_covers p qk.1 qk.2 d
  | None, None => True
  | _, _ => False
  end.

(** [pool_origins_covered p input orL orR]: [origins_covered] at run
    granularity: both origins resolve ([pool_origin_covered]), and when they
    fall in one slot the left origin precedes the right one in clock. *)
Definition pool_origins_covered (p : pool) (input : IntegrateInput (A := A))
    (orL orR : option (loc * nat)) : Prop :=
  pool_origin_covered p (in_originId input) orL ∧
  pool_origin_covered p (in_rightOriginId input) orR ∧
  match in_originId input, in_rightOriginId input, orL, orR with
  | Some a, Some b, Some qkL, Some qkR => qkL = qkR -> (clock a < clock b)%nat
  | _, _, _, _ => True
  end.

(** [pool_repair_parent bind opn orL orR p_t]: [repair_parent] at run
    granularity: the type a repaired item lands in is the root bound to its
    wire parent name, otherwise the pool key of its left, else right, origin
    slot. *)
Definition pool_repair_parent (bind : gmap P loc) (opn : option go_string)
    (orL orR : option (loc * nat)) (p_t : loc) : Prop :=
  match opn with
  | Some nm => bind !! nm = Some p_t
  | None => match orL with
            | Some qk => p_t = qk.1
            | None => match orR with
                      | Some qk => p_t = qk.1
                      | None => False
                      end
            end
  end.

(** [pool_origins_split p' locs' input orL orR lft rgt]: [origins_split] at
    run granularity: after [repair] the item's [left] is the address of a
    run ending at the left origin, its [right] of a run starting at the
    right origin, each in its origin slot's type and read off the address
    map [locs']; an absent origin links to [null]. *)
Definition pool_origins_split (p' : pool) (locs' : gmap loc (list loc))
    (input : IntegrateInput (A := A)) (orL orR : option (loc * nat))
    (lft rgt : loc) : Prop :=
  match in_originId input, orL with
  | Some d, Some qk => ∃ k', pool_run_ends_at p' qk.1 k' d ∧
                             (locs' !! qk.1) ≫= (λ ls, ls !! k') = Some lft
  | None, None => lft = null
  | _, _ => False
  end ∧
  match in_rightOriginId input, orR with
  | Some d, Some qk => ∃ k', pool_run_starts_at p' qk.1 k' d ∧
                             (locs' !! qk.1) ≫= (λ ls, ls !! k') = Some rgt
  | None, None => rgt = null
  | _, _ => False
  end.

(** [origin_slot_names types or oc]: the slot [(q, k)] names the cell [oc]
    in the registry [types]: how the run-granular repair premises pick the
    concrete cells the cell-level contract mentions
    ([pool_origins_covered_to_cell] produces it,
    [pool_repair_parent_to_cell] / [origins_split_to_pool] consume it). *)
Definition origin_slot_names (types : gmap loc type_state)
    (or : option (loc * nat)) (oc : option item_cell) : Prop :=
  match or, oc with
  | Some qk, Some c => ∃ ts, types !! qk.1 = Some ts ∧ ty_cells ts !! qk.2 = Some c
  | None, None => True
  | _, _ => False
  end.

(* ===== lemmas ============================================================= *)

(** [pool_cell_covers] at the projected pool: the covering cell named by its
    type and run index plus its address ([locs_of]); and back. What
    translates [GetNode]'s postcondition to [(locs, p)]. *)
Lemma pool_cell_covers_to_run (types : gmap loc type_state) (c : item_cell) (d : YjsId) :
  pool_cell_covers types c d ->
  ∃ parent k, pool_run_covers (pool_of types) parent k d ∧
    (locs_of types !! parent) ≫= (λ ls, ls !! k) = Some (ic_loc c).
Proof.
  intros [Hmem Hcov].
  apply all_cells_elem_of in Hmem as (parent & ts & Hts & Hcts).
  apply list_elem_of_lookup_1 in Hcts as (k & Hk).
  exists parent, k. split.
  - exists (type_model_of ts), (cell_run c).
    rewrite /pool_of lookup_fmap Hts /=.
    split_and!; [done | | by apply cell_covers_run].
    rewrite /type_model_of /= list_lookup_fmap Hk //.
  - rewrite /locs_of lookup_fmap Hts /= list_lookup_fmap Hk //.
Qed.

Lemma pool_run_covers_to_cell (types : gmap loc type_state) (parent : loc) (k : nat) (d : YjsId) :
  pool_run_covers (pool_of types) parent k d ->
  ∃ c, pool_cell_covers types c d.
Proof.
  intros (tm & r & Hp & Hr & Hcov).
  rewrite /pool_of lookup_fmap in Hp.
  destruct (types !! parent) as [ts|] eqn:Hts; simplify_eq/=.
  rewrite /type_model_of /= list_lookup_fmap in Hr.
  destruct (ty_cells ts !! k) as [c|] eqn:Hk; simplify_eq/=.
  exists c. split.
  - apply all_cells_elem_of. exists parent, ts.
    split; [done | exact (list_elem_of_lookup_2 _ _ _ Hk)].
  - by apply cell_covers_run.
Qed.


(** The split surgery projects along [cell_run]: the fresh node's address
    [r_loc] is the only thing the pure [split_runs] does not see
    (docs/plan-item-run-split.md stage 1). *)
Lemma cell_run_split_left (c : item_cell) (o : nat) :
  cell_run (split_cell_left c o) = split_run_left (cell_run c) o.
Proof. reflexivity. Qed.

Lemma cell_run_split_right (c : item_cell) (o : nat) (r_loc : loc) :
  cell_run (split_cell_right c o r_loc) = split_run_right (cell_run c) o.
Proof. reflexivity. Qed.

Lemma split_cells_runs (cells : list item_cell) (k o : nat) (r_loc : loc) :
  cell_run <$> split_cells cells k o r_loc = split_runs (cell_run <$> cells) k o.
Proof.
  rewrite /split_cells /split_runs list_lookup_fmap.
  destruct (cells !! k) as [c|] eqn:Hk; simpl; [| reflexivity].
  rewrite !fmap_app !fmap_cons /= !fmap_take !fmap_drop //.
Qed.

(** [runs_start_at] / [runs_end_at] over a projected cell list, read back on
    the cells: the bridge [cell_starts_at] / [cell_ends_at] will cross once
    the pool is run-granular (the pool-level forms also fix the node's
    address and owning type). *)
Lemma runs_start_at_fmap (cells : list item_cell) (k : nat) (d : YjsId) :
  runs_start_at (cell_run <$> cells) k d ↔
  ∃ c, cells !! k = Some c ∧ item_id (run_head c) = d.
Proof.
  rewrite /runs_start_at. split.
  - intros (r & Hk & Hd). rewrite list_lookup_fmap in Hk.
    destruct (cells !! k) as [c|] eqn:Hc; last done.
    simplify_eq/=. eauto.
  - intros (c & Hk & Hd). exists (cell_run c).
    rewrite list_lookup_fmap Hk /=. eauto.
Qed.

Lemma runs_end_at_fmap (cells : list item_cell) (k : nat) (d : YjsId) :
  runs_end_at (cell_run <$> cells) k d ↔
  ∃ c, cells !! k = Some c ∧ clientId (item_id (run_head c)) = clientId d ∧
       (clock (item_id (run_head c)) + length (ic_run c) = clock d + 1)%nat.
Proof.
  rewrite /runs_end_at. split.
  - intros (r & Hk & Hcl & Hck). rewrite list_lookup_fmap in Hk.
    destruct (cells !! k) as [c|] eqn:Hc; last done.
    simplify_eq/=. eauto.
  - intros (c & Hk & Hcl & Hck). exists (cell_run c).
    rewrite list_lookup_fmap Hk /=. eauto.
Qed.

Lemma cell_covers_clock_run (c : item_cell) (k : nat) :
  cell_covers_clock c k ↔ run_covers_clock (cell_run c) k.
Proof. reflexivity. Qed.

(** [split_types_update_rel] at the projected pools: the loc-identified
    clauses become index facts through [all_cells_same_loc_same_slot], the
    [w64] clock and client readings become [nat] under the id no-wrap
    bounds, and the client-run growth rides [client_run_runs]. The premises
    are what the heap layer extracts per pool: parent coherence
    ([own_ytype_cells]'s [Hcpar]), the id bounds
    ([own_type_pool_id_bounds]), nonempty runs ([own_type_pool_runs_wf])
    and [pool_invs]. *)
Lemma split_types_update_rel_to_pool (before after : gmap loc type_state)
    (w : item_cell) (parent : loc) (tsw : type_state) (k : nat) :
  before !! parent = Some tsw ->
  ty_cells tsw !! k = Some w ->
  (∀ q ts c, before !! q = Some ts -> c ∈ ty_cells ts -> ic_parent c = q) ->
  (∀ q ts c, after !! q = Some ts -> c ∈ ty_cells ts -> ic_parent c = q) ->
  (∀ c, c ∈ all_cells before -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells before -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells after -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells after -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells before -> ic_run c ≠ []) ->
  (∀ c, c ∈ all_cells after -> ic_run c ≠ []) ->
  pool_invs before -> pool_invs after ->
  split_types_update_rel before after w ->
  pool_after_split (pool_of before) (pool_of after) parent k.
Proof.
  move=> Htsw Hkw Hparb Hpara Hckb Hclb Hcka Hcla Hneb Hnea Hinvb Hinva Hrel.
  have [Hfb [Hndb [Hdjb Hocb]]] := Hinvb.
  have [Hfa [Hnda [Hdja Hoca]]] := Hinva.
  destruct Hrel as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  have Hzb : ∀ c, c ∈ all_cells before ->
      uint.Z (cell_clock c) = Z.of_nat (run_clock (cell_run c)).
  { move=> c Hc. have := Hckb c Hc.
    rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  have Hza : ∀ c, c ∈ all_cells after ->
      uint.Z (cell_clock c) = Z.of_nat (run_clock (cell_run c)).
  { move=> c Hc. have := Hcka c Hc.
    rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  split_and!.
  - (* per-type document and flatten survive *)
    move=> q tm' Hq. rewrite /pool_of lookup_fmap in Hq.
    destruct (after !! q) as [ts'|] eqn:Ha; simplify_eq/=.
    destruct (H1 q ts' Ha) as (ts & Hb & Harr & Hflat).
    exists (type_model_of ts). rewrite lookup_fmap Hb /=.
    split_and!; [done | exact Harr |].
    rewrite /type_model_of /= -!run_flatten_runs //.
  - (* no type disappears *)
    move=> q [tm Hq]. rewrite /pool_of lookup_fmap in Hq.
    destruct (before !! q) as [ts|] eqn:Hb; simplify_eq/=.
    destruct (H2 q (mk_is_Some _ _ Hb)) as [ts' Ha].
    rewrite /pool_of lookup_fmap Ha /=. by eexists.
  - (* runs away from the split spot survive *)
    move=> q tm k' r Hq Hr Hne.
    rewrite /pool_of lookup_fmap in Hq.
    destruct (before !! q) as [ts|] eqn:Hb; simplify_eq/=.
    rewrite /type_model_of /= list_lookup_fmap in Hr.
    destruct (ty_cells ts !! k') as [c|] eqn:Hk'; simplify_eq/=.
    have Hlocne : ic_loc c ≠ ic_loc w.
    { move=> Heq.
      destruct (all_cells_same_loc_same_slot before q parent ts tsw k' k c w
                  Hndb Hb Hk' Htsw Hkw Heq) as (?&?&?).
      apply Hne. by split. }
    have Hmem : c ∈ all_cells before.
    { apply all_cells_elem_of. exists q, ts.
      split; [done | exact (list_elem_of_lookup_2 _ _ _ Hk')]. }
    rewrite all_runs_pool_of. apply list_elem_of_fmap_2.
    exact (H4 c Hmem Hlocne).
  - (* a covered clock stays covered in the same type *)
    move=> ccl clk q tm k0 r Hq Hr Hccl Hle Hlt.
    rewrite /pool_of lookup_fmap in Hq.
    destruct (before !! q) as [ts|] eqn:Hb; simplify_eq/=.
    rewrite /type_model_of /= list_lookup_fmap in Hr.
    destruct (ty_cells ts !! k0) as [c|] eqn:Hk0; simplify_eq/=.
    have Hmem : c ∈ all_cells before.
    { apply all_cells_elem_of. exists q, ts.
      split; [done | exact (list_elem_of_lookup_2 _ _ _ Hk0)]. }
    have HleZ : (uint.Z (cell_clock c) <= Z.of_nat clk)%Z.
    { rewrite (Hzb c Hmem). lia. }
    have HltZ : (Z.of_nat clk < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z.
    { rewrite (Hzb c Hmem).
      have Hl : length (run_items (cell_run c)) = length (ic_run c) by reflexivity.
      rewrite -Hl. lia. }
    destruct (H5 (cell_client c) (Z.of_nat clk) c Hmem eq_refl HleZ HltZ)
      as (c' & Hm' & Hccl' & HleZ' & HltZ' & Hpar' & Hdisj').
    have Hm'2 := Hm'.
    apply all_cells_elem_of in Hm'2 as (q' & ts' & Ha' & Hcts').
    have Hq' : q' = q.
    { rewrite -(Hpara q' ts' c' Ha' Hcts') Hpar' (Hparb q ts c Hb (list_elem_of_lookup_2 _ _ _ Hk0)) //. }
    subst q'.
    apply list_elem_of_lookup_1 in Hcts' as (k' & Hk').
    exists (type_model_of ts'), k', (cell_run c').
    rewrite lookup_fmap Ha' /=.
    have Hclient : run_client (cell_run c') = run_client (cell_run c).
    { have Huz := f_equal uint.Z Hccl'.
      move: Huz. rewrite !cell_client_run /=.
      have HB1 := Hcla c' Hm'. have HB2 := Hclb c Hmem.
      move=> Huz. word. }
    split_and!.
    + done.
    + rewrite /type_model_of /= list_lookup_fmap Hk' //.
    + exact Hclient.
    + have Hz' := Hza c' Hm'. lia.
    + have Hz' := Hza c' Hm'. lia.
    + destruct Hdisj' as [-> | (Hcw & Hlen & _)].
      * by left.
      * right. subst c.
        destruct (all_cells_same_loc_same_slot before q parent ts tsw k0 k w w
                    Hndb Hb Hk0 Htsw Hkw eq_refl) as (Hq2 & Hk2 & _).
        split_and!; [exact Hq2 | exact Hk2 |].
        rewrite /cell_run /=. exact Hlen.
  - (* one-char types untouched *)
    move=> q tm tm' Hq Hq'.
    rewrite /pool_of lookup_fmap in Hq.
    destruct (before !! q) as [ts|] eqn:Hb; simplify_eq/=.
    rewrite /pool_of lookup_fmap in Hq'.
    destruct (after !! q) as [ts'|] eqn:Ha; simplify_eq/=.
    rewrite /type_model_of /= Forall_fmap.
    move=> Hunit.
    have Hcu : Forall cell_unit (ty_cells ts).
    { eapply Forall_impl; [exact Hunit |]. move=> c Hc. exact Hc. }
    rewrite (H6 q ts ts' Hb Ha Hcu) //.
  - (* every new run sits inside an old one's range *)
    rewrite /runs_within !all_runs_pool_of.
    move=> r Hr. apply list_elem_of_fmap in Hr as (c & -> & Hc).
    destruct (H7 c Hc) as (c0 & Hc0 & Hcl0 & Hle0 & Hhi0).
    exists (cell_run c0). split_and!.
    + apply list_elem_of_fmap_2. exact Hc0.
    + have Huz := f_equal uint.Z Hcl0.
      move: Huz. rewrite !cell_client_run /=.
      have HB1 := Hcla c Hc. have HB0 := Hclb c0 Hc0.
      move=> Huz. word.
    + have Hz1 := Hza c Hc. have Hz0 := Hzb c0 Hc0. lia.
    + have Hz1 := Hza c Hc. have Hz0 := Hzb c0 Hc0.
      have Hl1 : length (run_items (cell_run c)) = length (ic_run c) by reflexivity.
      have Hl0 : length (run_items (cell_run c0)) = length (ic_run c0) by reflexivity.
      rewrite Hl1 Hl0. lia.
  - (* live chars refine *)
    rewrite /runs_live_refine !all_runs_pool_of.
    move=> r' Hr' Hdel.
    apply list_elem_of_fmap in Hr' as (c' & -> & Hc').
    rewrite /cell_run /= in Hdel.
    destruct (H8 c' Hc' Hdel) as (c & Hc & Hcdel & Hsub).
    exists (cell_run c). split_and!.
    + apply list_elem_of_fmap_2. exact Hc.
    + rewrite /cell_run /= Hcdel //.
    + move=> y Hy. rewrite /cell_run /= in Hy |- *. exact (Hsub y Hy).
  - (* dead chars kept *)
    rewrite /runs_dead_kept !all_runs_pool_of.
    move=> r Hr Hdel y Hy.
    apply list_elem_of_fmap in Hr as (c & -> & Hc).
    rewrite /cell_run /= in Hdel Hy.
    destruct (H9 c Hc Hdel y Hy) as (c' & Hc' & Hcdel' & Hy').
    exists (cell_run c'). split_and!.
    + apply list_elem_of_fmap_2. exact Hc'.
    + rewrite /cell_run /= Hcdel' //.
    + rewrite /cell_run /=. exact Hy'.
Qed.

(** [repair_types_update_rel] carried to the projected pool: the loc-free
    clauses of [pool_after_repair], each read off its cell counterpart the
    way [split_types_update_rel_to_pool] does, minus the split-spot ones.
    What carries [wp_store__repair]'s step record to [(locs, p)]
    ([wp_store__repair_runs]). *)
Lemma repair_types_update_rel_to_pool (before after : gmap loc type_state) :
  (∀ c, c ∈ all_cells before -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells before -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells after -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells after -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells before -> ic_run c ≠ []) ->
  (∀ c, c ∈ all_cells after -> ic_run c ≠ []) ->
  pool_invs before -> pool_invs after ->
  repair_types_update_rel before after ->
  pool_after_repair (pool_of before) (pool_of after).
Proof.
  move=> Hckb Hclb Hcka Hcla Hneb Hnea Hinvb Hinva Hrel.
  have [Hfb [Hndb [Hdjb Hocb]]] := Hinvb.
  have [Hfa [Hnda [Hdja Hoca]]] := Hinva.
  destruct Hrel as (H1 & H2 & H3 & H4 & H5 & H6).
  have Hzb : ∀ c, c ∈ all_cells before ->
      uint.Z (cell_clock c) = Z.of_nat (run_clock (cell_run c)).
  { move=> c Hc. have := Hckb c Hc.
    rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  have Hza : ∀ c, c ∈ all_cells after ->
      uint.Z (cell_clock c) = Z.of_nat (run_clock (cell_run c)).
  { move=> c Hc. have := Hcka c Hc.
    rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  split_and!.
  - move=> q tm' Hq. rewrite /pool_of lookup_fmap in Hq.
    destruct (after !! q) as [ts'|] eqn:Ha; simplify_eq/=.
    destruct (H1 q ts' Ha) as (ts & Hb & Harr & Hflat).
    exists (type_model_of ts). rewrite lookup_fmap Hb /=.
    split_and!; [done | exact Harr |].
    rewrite /type_model_of /= -!run_flatten_runs //.
  - move=> q [tm Hq]. rewrite /pool_of lookup_fmap in Hq.
    destruct (before !! q) as [ts|] eqn:Hb; simplify_eq/=.
    destruct (H2 q (mk_is_Some _ _ Hb)) as [ts' Ha].
    rewrite /pool_of lookup_fmap Ha /=. by eexists.
  - move=> q tm tm' Hq Hq'.
    rewrite /pool_of lookup_fmap in Hq.
    destruct (before !! q) as [ts|] eqn:Hb; simplify_eq/=.
    rewrite /pool_of lookup_fmap in Hq'.
    destruct (after !! q) as [ts'|] eqn:Ha; simplify_eq/=.
    rewrite /type_model_of /= Forall_fmap.
    move=> Hunit.
    have Hcu : Forall cell_unit (ty_cells ts).
    { eapply Forall_impl; [exact Hunit |]. move=> c Hc. exact Hc. }
    rewrite (H4 q ts ts' Hb Ha Hcu) //.
  - rewrite /runs_within !all_runs_pool_of.
    move=> r Hr. apply list_elem_of_fmap in Hr as (c & -> & Hc).
    destruct (H5 c Hc) as (c0 & Hc0 & Hcl0 & Hle0 & Hhi0).
    exists (cell_run c0). split_and!.
    + apply list_elem_of_fmap_2. exact Hc0.
    + have Huz := f_equal uint.Z Hcl0.
      move: Huz. rewrite !cell_client_run /=.
      have HB1 := Hcla c Hc. have HB0 := Hclb c0 Hc0.
      move=> Huz. word.
    + have Hz1 := Hza c Hc. have Hz0 := Hzb c0 Hc0. lia.
    + have Hz1 := Hza c Hc. have Hz0 := Hzb c0 Hc0.
      have Hl1 : length (run_items (cell_run c)) = length (ic_run c) by reflexivity.
      have Hl0 : length (run_items (cell_run c0)) = length (ic_run c0) by reflexivity.
      rewrite Hl1 Hl0. lia.
  - rewrite /runs_live_refine !all_runs_pool_of.
    move=> r' Hr' Hdel.
    apply list_elem_of_fmap in Hr' as (c' & -> & Hc').
    rewrite /cell_run /= in Hdel.
    destruct (H6 c' Hc' Hdel) as (c & Hc & Hcdel & Hsub).
    exists (cell_run c). split_and!.
    + apply list_elem_of_fmap_2. exact Hc.
    + rewrite /cell_run /= Hcdel //.
    + move=> y Hy. rewrite /cell_run /= in Hy |- *. exact (Hsub y Hy).
Qed.
(** [cell_starts_at] / [cell_ends_at] at the projected pool: the node named
    by its type and run index, its address the address list's entry there;
    and back. Needs the parent coherence (every cell sits in its own
    parent's list, [own_ytype_cells]'s per-type fact), which ties
    [ic_parent] to the pool key. *)
Lemma cell_starts_at_to_run (types : gmap loc type_state) (parent l : loc) (d : YjsId) :
  (∀ q ts c, types !! q = Some ts -> c ∈ ty_cells ts -> ic_parent c = q) ->
  cell_starts_at types parent l d ->
  ∃ k, pool_run_starts_at (pool_of types) parent k d ∧
       (locs_of types !! parent) ≫= (λ ls, ls !! k) = Some l.
Proof.
  intros Hpar (c & Hmem & Hloc & Hcpar & Hd).
  apply all_cells_elem_of in Hmem as (q & ts & Hts & Hcts).
  have Hq : q = parent by (rewrite -(Hpar q ts c Hts Hcts) Hcpar //).
  subst q l d.
  apply list_elem_of_lookup_1 in Hcts as (k & Hk).
  exists k. split.
  - exists (type_model_of ts).
    rewrite /pool_of lookup_fmap Hts /=. split; [done |].
    exists (cell_run c).
    rewrite /type_model_of /= list_lookup_fmap Hk /=. done.
  - rewrite /locs_of lookup_fmap Hts /= list_lookup_fmap Hk //.
Qed.

Lemma pool_run_starts_at_to_cell (types : gmap loc type_state) (parent : loc) (k : nat) (d : YjsId) (l : loc) :
  (∀ q ts c, types !! q = Some ts -> c ∈ ty_cells ts -> ic_parent c = q) ->
  pool_run_starts_at (pool_of types) parent k d ->
  (locs_of types !! parent) ≫= (λ ls, ls !! k) = Some l ->
  cell_starts_at types parent l d.
Proof.
  intros Hpar (tm & Hp & (r & Hr & Hd)) Hl.
  rewrite /pool_of lookup_fmap in Hp.
  destruct (types !! parent) as [ts|] eqn:Hts; simplify_eq/=.
  rewrite /type_model_of /= list_lookup_fmap in Hr.
  destruct (ty_cells ts !! k) as [c|] eqn:Hk; simplify_eq/=.
  rewrite /locs_of lookup_fmap Hts /= list_lookup_fmap Hk /= in Hl. simplify_eq/=.
  have Hcts := list_elem_of_lookup_2 _ _ _ Hk.
  exists c. split_and!.
  - apply all_cells_elem_of. by exists parent, ts.
  - done.
  - exact (Hpar parent ts c Hts Hcts).
  - done.
Qed.

(** Starts and ends at the SAME address land on the same slot (the address
    determines it, [all_cells_same_loc_same_slot]). *)
Lemma cell_starts_ends_at_to_run (types : gmap loc type_state) (parent l : loc) (d1 d2 : YjsId) :
  (∀ q ts c, types !! q = Some ts -> c ∈ ty_cells ts -> ic_parent c = q) ->
  NoDup (ic_loc <$> all_cells types) ->
  cell_starts_at types parent l d1 ->
  cell_ends_at types parent l d2 ->
  ∃ k, pool_run_starts_at (pool_of types) parent k d1 ∧
       pool_run_ends_at (pool_of types) parent k d2 ∧
       (locs_of types !! parent) ≫= (λ ls, ls !! k) = Some l.
Proof.
  intros Hpar Hnd Hst Hen.
  have Hen' := Hen.
  destruct Hst as (c1 & Hmem1 & Hloc1 & Hcpar1 & Hd1).
  destruct Hen' as (c2 & Hmem2 & Hloc2 & Hcpar2 & Hcl2 & Hck2).
  have Hm1 := Hmem1. apply all_cells_elem_of in Hm1 as (q1 & ts1 & Hq1 & Hc1).
  have Hm2 := Hmem2. apply all_cells_elem_of in Hm2 as (q2 & ts2 & Hq2 & Hc2).
  apply list_elem_of_lookup_1 in Hc1 as (k1 & Hk1).
  apply list_elem_of_lookup_1 in Hc2 as (k2 & Hk2).
  have Hll : ic_loc c1 = ic_loc c2 by congruence.
  destruct (all_cells_same_loc_same_slot types q1 q2 ts1 ts2 k1 k2 c1 c2
              Hnd Hq1 Hk1 Hq2 Hk2 Hll) as (Hqq & Hkk & Hcc).
  subst q2 k2 c2.
  have Hqp : q1 = parent by (rewrite -(Hpar q1 ts1 c1 Hq1 (list_elem_of_lookup_2 _ _ _ Hk1)) Hcpar1 //).
  subst q1 l.
  exists k1. split_and!.
  - exists (type_model_of ts1).
    rewrite /pool_of lookup_fmap Hq1 /=. split; [done |].
    exists (cell_run c1).
    rewrite /type_model_of /= list_lookup_fmap Hk1 /=. done.
  - exists (type_model_of ts1).
    rewrite /pool_of lookup_fmap Hq1 /=. split; [done |].
    exists (cell_run c1).
    rewrite /type_model_of /= list_lookup_fmap Hk1 /=. split_and!; [done | exact Hcl2 | exact Hck2].
  - rewrite /locs_of lookup_fmap Hq1 /= list_lookup_fmap Hk1 //.
Qed.

Lemma cell_ends_at_to_run (types : gmap loc type_state) (parent l : loc) (d : YjsId) :
  (∀ q ts c, types !! q = Some ts -> c ∈ ty_cells ts -> ic_parent c = q) ->
  cell_ends_at types parent l d ->
  ∃ k, pool_run_ends_at (pool_of types) parent k d ∧
       (locs_of types !! parent) ≫= (λ ls, ls !! k) = Some l.
Proof.
  intros Hpar (c & Hmem & Hloc & Hcpar & Hcl & Hck).
  apply all_cells_elem_of in Hmem as (q & ts & Hts & Hcts).
  have Hq : q = parent by (rewrite -(Hpar q ts c Hts Hcts) Hcpar //).
  subst q l.
  apply list_elem_of_lookup_1 in Hcts as (k & Hk).
  exists k. split.
  - exists (type_model_of ts).
    rewrite /pool_of lookup_fmap Hts /=. split; [done |].
    exists (cell_run c).
    rewrite /type_model_of /= list_lookup_fmap Hk /=. done.
  - rewrite /locs_of lookup_fmap Hts /= list_lookup_fmap Hk //.
Qed.

Lemma pool_run_ends_at_to_cell (types : gmap loc type_state) (parent : loc) (k : nat) (d : YjsId) (l : loc) :
  (∀ q ts c, types !! q = Some ts -> c ∈ ty_cells ts -> ic_parent c = q) ->
  pool_run_ends_at (pool_of types) parent k d ->
  (locs_of types !! parent) ≫= (λ ls, ls !! k) = Some l ->
  cell_ends_at types parent l d.
Proof.
  intros Hpar (tm & Hp & (r & Hr & Hcl & Hck)) Hl.
  rewrite /pool_of lookup_fmap in Hp.
  destruct (types !! parent) as [ts|] eqn:Hts; simplify_eq/=.
  rewrite /type_model_of /= list_lookup_fmap in Hr.
  destruct (ty_cells ts !! k) as [c|] eqn:Hk; simplify_eq/=.
  rewrite /locs_of lookup_fmap Hts /= list_lookup_fmap Hk /= in Hl. simplify_eq/=.
  have Hcts := list_elem_of_lookup_2 _ _ _ Hk.
  exists c. split_and!.
  - apply all_cells_elem_of. by exists parent, ts.
  - done.
  - exact (Hpar parent ts c Hts Hcts).
  - exact Hcl.
  - exact Hck.
Qed.

(** The run-granular repair premises give the cell-level ones: the origin
    slots name their cells (under the address [NoDup], one cell for both
    origins when the slots coincide), and the pool key is the named cell's
    parent (under parent coherence). *)
Lemma pool_origins_covered_to_cell (types : gmap loc type_state)
    (input : IntegrateInput (A := A)) (orL orR : option (loc * nat)) :
  NoDup (ic_loc <$> all_cells types) ->
  pool_origins_covered (pool_of types) input orL orR ->
  ∃ ocL ocR,
    origins_covered types input ocL ocR ∧
    origin_slot_names types orL ocL ∧ origin_slot_names types orR ocR.
Proof.
  move=> Hnd Hcov. destruct Hcov as (HcL & HcR & Hsame).
  have Hpick : ∀ (o : option YjsId) (or : option (loc * nat)),
      pool_origin_covered (pool_of types) o or ->
      ∃ oc, origin_covered types o oc ∧ origin_slot_names types or oc.
  { move=> o or.
    destruct o as [d|]; destruct or as [[q k]|]; rewrite /pool_origin_covered //=.
    - intros (tm & r & Hp & Hr & Hcovr).
      rewrite /pool_of lookup_fmap in Hp.
      destruct (types !! q) as [ts|] eqn:Hts; simplify_eq/=.
      rewrite /type_model_of /= list_lookup_fmap in Hr.
      destruct (ty_cells ts !! k) as [c|] eqn:Hk; simplify_eq/=.
      exists (Some c). split_and!.
      + split.
        * apply all_cells_elem_of. exists q, ts.
          split; [done | exact (list_elem_of_lookup_2 _ _ _ Hk)].
        * by apply cell_covers_run.
      + exists ts. by split.
    - move=> _. by exists None. }
  destruct (Hpick _ _ HcL) as (ocL & HoL & HsL).
  destruct (Hpick _ _ HcR) as (ocR & HoR & HsR).
  exists ocL, ocR. split_and!; [| exact HsL | exact HsR].
  split_and!; [exact HoL | exact HoR |].
  destruct (in_originId input) as [a|]; destruct (in_rightOriginId input) as [b|]; try done.
  destruct ocL as [cL|]; destruct ocR as [cR|]; try done.
  destruct orL as [[qL kL]|]; [| done]. destruct orR as [[qR kR]|]; [| done].
  move=> Heq.
  destruct HsL as (tsL & HtsL & HkL). destruct HsR as (tsR & HtsR & HkR).
  destruct (all_cells_same_loc_same_slot types qL qR tsL tsR kL kR cL cR
              Hnd HtsL HkL HtsR HkR (f_equal ic_loc Heq)) as (Hq & Hk & _).
  apply Hsame. rewrite Hq Hk //.
Qed.

Lemma pool_repair_parent_to_cell (types : gmap loc type_state) (bind : gmap P loc)
    (opn : option go_string) (orL orR : option (loc * nat))
    (ocL ocR : option item_cell) (p_t : loc) :
  (∀ q ts c, types !! q = Some ts -> c ∈ ty_cells ts -> ic_parent c = q) ->
  origin_slot_names types orL ocL ->
  origin_slot_names types orR ocR ->
  pool_repair_parent bind opn orL orR p_t ->
  repair_parent bind opn ocL ocR p_t.
Proof.
  move=> Hcoh HsL HsR.
  rewrite /pool_repair_parent /repair_parent.
  destruct opn as [nm|]; [done |].
  destruct orL as [[qL kL]|]; destruct ocL as [cL|]; try done.
  - destruct HsL as (tsL & HtsL & HkL).
    move=> /= ->.
    rewrite (Hcoh qL tsL cL HtsL (list_elem_of_lookup_2 _ _ _ HkL)) //.
  - destruct orR as [[qR kR]|]; destruct ocR as [cR|]; try done.
    destruct HsR as (tsR & HtsR & HkR).
    move=> /= ->.
    rewrite (Hcoh qR tsR cR HtsR (list_elem_of_lookup_2 _ _ _ HkR)) //.
Qed.

(** [origins_split] carried to [(locs, p)]: the boundary cells become
    run-boundary slots of the updated pool, their addresses read off the
    updated address map. What carries [wp_store__repair]'s postcondition to
    the run-granular spec. *)
Lemma origins_split_to_pool (types types2 : gmap loc type_state)
    (input : IntegrateInput (A := A)) (orL orR : option (loc * nat))
    (ocL ocR : option item_cell) (lft rgt : loc) :
  (∀ q ts c, types !! q = Some ts -> c ∈ ty_cells ts -> ic_parent c = q) ->
  (∀ q ts c, types2 !! q = Some ts -> c ∈ ty_cells ts -> ic_parent c = q) ->
  origin_slot_names types orL ocL ->
  origin_slot_names types orR ocR ->
  origins_split types2 input ocL ocR lft rgt ->
  pool_origins_split (pool_of types2) (locs_of types2) input orL orR lft rgt.
Proof.
  move=> Hcohb Hcoha HsL HsR [HL HR].
  split.
  - destruct (in_originId input) as [d|].
    + destruct orL as [[qL kL]|]; [| by destruct ocL].
      destruct ocL as [cL|]; [| done].
      destruct HsL as (tsL & HtsL & HkL).
      destruct HL as [Hlft Hends].
      have Hq : ic_parent cL = qL
        := Hcohb qL tsL cL HtsL (list_elem_of_lookup_2 _ _ _ HkL).
      rewrite Hq in Hends. simpl.
      exact (cell_ends_at_to_run types2 qL lft d Hcoha Hends).
    + destruct orL as [qk|]; [by destruct ocL | destruct ocL as [cL|]; [done | exact HL]].
  - destruct (in_rightOriginId input) as [d|].
    + destruct orR as [[qR kR]|]; [| by destruct ocR].
      destruct ocR as [cR|]; [| done].
      destruct HsR as (tsR & HtsR & HkR).
      have Hq : ic_parent cR = qR
        := Hcohb qR tsR cR HtsR (list_elem_of_lookup_2 _ _ _ HkR).
      rewrite Hq in HR. simpl.
      exact (cell_starts_at_to_run types2 qR rgt d Hcoha HR).
    + destruct orR as [qk|]; [by destruct ocR | destruct ocR as [cR|]; [done | exact HR]].
Qed.
Lemma split_cells_locs (cells : list item_cell) (k o : nat) (r_loc : loc) :
  ic_loc <$> split_cells cells k o r_loc = split_locs (ic_loc <$> cells) k r_loc.
Proof.
  rewrite /split_cells /split_locs list_lookup_fmap.
  destruct (cells !! k) as [c|] eqn:Hk; simpl; [| reflexivity].
  rewrite !fmap_app !fmap_cons /= !fmap_take !fmap_drop //.
Qed.

(** [cell_covers] at a runtime id, read in the [w64] arithmetic the node
    lookups compute with; needs the cell's ids to fit a word. *)
Lemma cell_covers_w64 (c : item_cell) (idv : yjs.id.t) :
  (Z.of_nat (clientId (item_id (run_head c))) < 2^64)%Z ->
  (Z.of_nat (clock (item_id (run_head c))) < 2^64)%Z ->
  cell_fits c ->
  cell_covers c (toYjsId idv) <->
  (cell_client c = idv.(yjs.id.clientId') ∧
   (uint.Z (cell_clock c) <= uint.Z idv.(yjs.id.clock'))%Z ∧
   (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z).
Proof.
  move=> Hcl Hck Hfit.
  rewrite /cell_covers /cell_client /cell_clock /cell_fits /toYjsId /= in Hfit |- *.
  split.
  - move=> [H1 [H2 H3]]. split_and!; [rewrite H1; word | word | word].
  - move=> [H1 [H2 H3]]. split_and!; [| word | word].
    have H1' := f_equal uint.Z H1. word.
Qed.

(** One id lives in one node: two pool cells covering the same id share a
    location ([cells_range_disjoint]). *)
Lemma pool_cell_covers_loc (types : gmap loc type_state) (c1 c2 : item_cell) (d : YjsId) :
  pool_invs types ->
  (∀ c, c ∈ all_cells types -> (Z.of_nat (clock (item_id (run_head c))) < 2^64)%Z) ->
  pool_cell_covers types c1 d -> pool_cell_covers types c2 d -> ic_loc c1 = ic_loc c2.
Proof.
  move=> [Hfits [_ [Hdisj _]]] Hbnd [Hc1 [Hcl1 [Hle1 Hlt1]]] [Hc2 [Hcl2 [Hle2 Hlt2]]].
  destruct (decide (ic_loc c1 = ic_loc c2)) as [He | Hne]; [exact He | exfalso].
  have Hcc : cell_client c1 = cell_client c2 by rewrite /cell_client Hcl1 Hcl2.
  have Hb1 := Hbnd c1 Hc1. have Hb2 := Hbnd c2 Hc2.
  have Hf1 := Hfits c1 Hc1. have Hf2 := Hfits c2 Hc2.
  rewrite /cell_fits /cell_clock in Hf1 Hf2.
  destruct (Hdisj c1 c2 Hc1 Hc2 Hcc Hne) as [H | H]; rewrite /cell_clock in H; word.
Qed.

(** The right half of a split starts [o] chars into the run. *)
Lemma split_cell_right_head_id (cw : item_cell) (o : nat) (rloc : loc) :
  run_wf (ic_run cw) -> (o < length (ic_run cw))%nat ->
  item_id (run_head (split_cell_right cw o rloc))
    = MkYjsId (clientId (item_id (run_head cw))) (clock (item_id (run_head cw)) + o).
Proof.
  move=> Hwf Ho.
  destruct (lookup_lt_is_Some_2 (ic_run cw) o Ho) as [yo Hyo].
  have Hheadr : run_head (split_cell_right cw o rloc) = yo.
  { rewrite /run_head /split_cell_right /= (drop_S _ _ _ Hyo) //. }
  rewrite Hheadr. exact (run_wf_char_id (ic_run cw) o yo Hwf Hyo).
Qed.

(** A split step keeps the registry coherent: no type appears or disappears. *)
Lemma registry_coh_split_step (bind : gmap P loc) (before after : gmap loc type_state)
    (w : item_cell) :
  split_types_update_rel before after w ->
  registry_coh bind before -> registry_coh bind after.
Proof.
  move=> [Hpres [Hdom _]] Hreg.
  apply (registry_coh_dom_eq bind before after); [exact Hdom | | exact Hreg].
  move=> p [ts' Hts']. destruct (Hpres p ts' Hts') as (ts & Hts & _). by exists ts.
Qed.

(** The same along a repair, which is at most two splits. *)
Lemma registry_coh_repair_step (bind : gmap P loc) (before after : gmap loc type_state) :
  repair_types_update_rel before after ->
  registry_coh bind before -> registry_coh bind after.
Proof.
  move=> [Hpres [Hdom _]] Hreg.
  apply (registry_coh_dom_eq bind before after); [exact Hdom | | exact Hreg].
  move=> p [ts' Hts']. destruct (Hpres p ts' Hts') as (ts & Hts & _). by exists ts.
Qed.

(** And along the wire delete path. *)
Lemma registry_coh_delete_step (bind : gmap P loc) (before after : gmap loc type_state) :
  delete_types_update_rel before after ->
  registry_coh bind before -> registry_coh bind after.
Proof.
  move=> [Hpres [Hdom _]] Hreg.
  apply (registry_coh_dom_eq bind before after); [exact Hdom | | exact Hreg].
  move=> p [ts' Hts']. destruct (Hpres p ts' Hts') as (ts & Hts & _). by exists ts.
Qed.

(** The split is invisible to the per-char document: the flatten is unchanged. *)
Lemma split_cells_flatten (cells : list item_cell) (k o : nat) (r_loc : loc) (c : item_cell) :
  cells !! k = Some c ->
  run_flatten (split_cells cells k o r_loc) = run_flatten cells.
Proof.
  move=> Hk. rewrite /split_cells Hk.
  rewrite -[in X in _ = X](take_drop_middle cells k c Hk).
  rewrite !run_flatten_app !run_flatten_cons run_flatten_nil.
  rewrite /split_cell_left /split_cell_right /=.
  rewrite app_nil_r take_drop //.
Qed.

(** ... and to the visible count. *)
Lemma split_cells_num_visible (cells : list item_cell) (k o : nat) (r_loc : loc) (c : item_cell) :
  cells !! k = Some c ->
  num_visible (split_cells cells k o r_loc) = num_visible cells.
Proof.
  move=> Hk. rewrite /split_cells Hk.
  rewrite -[in X in _ = X](take_drop_middle cells k c Hk).
  rewrite /num_visible !fmap_app !fmap_cons !list_sum_app /=.
  rewrite /split_cell_left /split_cell_right /=.
  destruct (ic_deleted c); [lia |].
  rewrite !length_take !length_drop. lia.
Qed.

Lemma delete_types_update_rel_refl (types : gmap loc type_state) :
  delete_types_update_rel types types.
Proof.
  split_and!; [move=> p ts' Hp; by exists ts' | done | exact (live_refine_refl types)
              | exact (dead_chars_kept_refl types) |].
  move=> c' Hc'. exists c'. split_and!; [exact Hc' | done | lia | lia].
Qed.

Lemma delete_types_update_rel_trans (t1 t2 t3 : gmap loc type_state) :
  delete_types_update_rel t1 t2 -> delete_types_update_rel t2 t3 -> delete_types_update_rel t1 t3.
Proof.
  move=> [Harr1 [Hdom1 [Hlr1 [Hdk1 Hco1]]]] [Harr2 [Hdom2 [Hlr2 [Hdk2 Hco2]]]]. split_and!.
  - move=> p ts3 Hp3.
    destruct (Harr2 p ts3 Hp3) as (ts2 & Hp2 & Heq2).
    destruct (Harr1 p ts2 Hp2) as (ts1 & Hp1 & Heq1).
    exists ts1. split; [exact Hp1 | congruence].
  - move=> p Hp. exact (Hdom2 p (Hdom1 p Hp)).
  - exact (live_refine_trans t1 t2 t3 Hlr1 Hlr2).
  - exact (dead_chars_kept_trans t1 t2 t3 Hdk1 Hdk2).
  - move=> c3 Hc3.
    destruct (Hco2 c3 Hc3) as (c2 & Hc2 & Hcc2 & Hlo2 & Hhi2).
    destruct (Hco1 c2 Hc2) as (c1 & Hc1 & Hcc1 & Hlo1 & Hhi1).
    exists c1. split_and!; [exact Hc1 | congruence | lia | lia].
Qed.

(** A split step is a delete step: [split_types_update_rel]'s model and coordinate
    clauses. *)
Lemma delete_types_update_rel_of_split (types types' : gmap loc type_state) (w : item_cell) :
  split_types_update_rel types types' w -> delete_types_update_rel types types'.
Proof.
  move=> [Harr [Hdom [_ [_ [_ [_ [Hco [Hlr Hdk]]]]]]]].
  split_and!; [| exact Hdom | exact Hlr | exact Hdk | exact Hco].
  move=> p ts' Hp'. destruct (Harr p ts' Hp') as (ts & Hp & Heq & _).
  exists ts. split; [exact Hp | exact Heq].
Qed.

(** A tombstone step is a delete step: one type is replaced by one whose
    cells changed but whose model list did not, and (in the only use,
    [flip_cell] at one index) whose cells keep their coordinates. *)
Lemma delete_types_update_rel_of_flip (types : gmap loc type_state) (p : loc)
    (ts : type_state) (k : nat) (c : item_cell) :
  types !! p = Some ts -> ty_cells ts !! k = Some c ->
  delete_types_update_rel types
    (<[p := MkTypeState (<[k := flip_cell c]> (ty_cells ts)) (ty_arr ts)]> types).
Proof.
  move=> Hp Hck. split_and!.
  - move=> q tq Hq.
    destruct (decide (q = p)) as [-> | Hne].
    + rewrite lookup_insert_eq in Hq. injection Hq as <-.
      exists ts. split; [exact Hp | reflexivity].
    + rewrite lookup_insert_ne // in Hq. by exists tq.
  - move=> q Hq.
    destruct (decide (q = p)) as [-> | Hne].
    + rewrite lookup_insert_eq. by eexists.
    + rewrite lookup_insert_ne //.
  - exact (live_refine_flip types p ts k c Hp Hck).
  - exact (dead_chars_kept_flip types p ts k c Hp Hck).
  - (* the pool is the same up to the flipped cell, which keeps its run and
       hence its coordinates *)
    move=> c' Hc'.
    have Hlr := flip_locs_run_perm types p ts k c Hp Hck.
    have Hin : (ic_loc c', ic_run c') ∈ ((λ c0, (ic_loc c0, ic_run c0)) <$> all_cells types).
    { rewrite -Hlr. apply list_elem_of_fmap.
      exists c'. split; [reflexivity | exact Hc']. }
    apply list_elem_of_fmap in Hin as (cw0 & Heq & Hcw0).
    have Hrun : ic_run c' = ic_run cw0 := f_equal snd Heq.
    exists cw0. rewrite /cell_client /cell_clock /run_head Hrun.
    split_and!; [exact Hcw0 | done | lia | lia].
Qed.

(** [delete_types_update_rel] carried to the projected pool: the loc-free
    clauses of [pool_after_delete]. What carries the delete path's step
    record to [(locs, p)] ([wp_store__deleteRange_runs] /
    [wp_store__applyDeleteSpans_runs]). *)
Lemma delete_types_update_rel_to_pool (before after : gmap loc type_state) :
  (∀ c, c ∈ all_cells before -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells before -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells after -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells after -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  delete_types_update_rel before after ->
  pool_after_delete (pool_of before) (pool_of after).
Proof.
  move=> Hckb Hclb Hcka Hcla Hrel.
  destruct Hrel as (H1 & H2 & H3 & H4 & H5).
  have Hzb : ∀ c, c ∈ all_cells before ->
      uint.Z (cell_clock c) = Z.of_nat (run_clock (cell_run c)).
  { move=> c Hc. have := Hckb c Hc.
    rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  have Hza : ∀ c, c ∈ all_cells after ->
      uint.Z (cell_clock c) = Z.of_nat (run_clock (cell_run c)).
  { move=> c Hc. have := Hcka c Hc.
    rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  split_and!.
  - move=> q tm' Hq. rewrite /pool_of lookup_fmap in Hq.
    destruct (after !! q) as [ts'|] eqn:Ha; simplify_eq/=.
    destruct (H1 q ts' Ha) as (ts & Hb & Harr).
    exists (type_model_of ts). rewrite lookup_fmap Hb /=.
    split; [done | exact Harr].
  - move=> q [tm Hq]. rewrite /pool_of lookup_fmap in Hq.
    destruct (before !! q) as [ts|] eqn:Hb; simplify_eq/=.
    destruct (H2 q (mk_is_Some _ _ Hb)) as [ts' Ha].
    rewrite /pool_of lookup_fmap Ha /=. by eexists.
  - rewrite /runs_live_refine !all_runs_pool_of.
    move=> r' Hr' Hdel.
    apply list_elem_of_fmap in Hr' as (c' & -> & Hc').
    rewrite /cell_run /= in Hdel.
    destruct (H3 c' Hc' Hdel) as (c & Hc & Hcdel & Hsub).
    exists (cell_run c). split_and!.
    + apply list_elem_of_fmap_2. exact Hc.
    + rewrite /cell_run /= Hcdel //.
    + move=> y Hy. rewrite /cell_run /= in Hy |- *. exact (Hsub y Hy).
  - rewrite /runs_dead_kept !all_runs_pool_of.
    move=> r Hr Hdel y Hy.
    apply list_elem_of_fmap in Hr as (c & -> & Hc).
    rewrite /cell_run /= in Hdel Hy.
    destruct (H4 c Hc Hdel y Hy) as (c' & Hc' & Hcdel' & Hy').
    exists (cell_run c'). split_and!.
    + apply list_elem_of_fmap_2. exact Hc'.
    + rewrite /cell_run /= Hcdel' //.
    + rewrite /cell_run /=. exact Hy'.
  - rewrite /runs_within !all_runs_pool_of.
    move=> r Hr. apply list_elem_of_fmap in Hr as (c & -> & Hc).
    destruct (H5 c Hc) as (c0 & Hc0 & Hcl0 & Hle0 & Hhi0).
    exists (cell_run c0). split_and!.
    + apply list_elem_of_fmap_2. exact Hc0.
    + have Huz := f_equal uint.Z Hcl0.
      move: Huz. rewrite !cell_client_run /=.
      have HB1 := Hcla c Hc. have HB0 := Hclb c0 Hc0.
      move=> Huz. word.
    + have Hz1 := Hza c Hc. have Hz0 := Hzb c0 Hc0. lia.
    + have Hz1 := Hza c Hc. have Hz0 := Hzb c0 Hc0.
      have Hl1 : length (run_items (cell_run c)) = length (ic_run c) by reflexivity.
      have Hl0 : length (run_items (cell_run c0)) = length (ic_run c0) by reflexivity.
      rewrite Hl1 Hl0. lia.
Qed.

(** [pool_after_delete] read back at the cells: the converse of
    [delete_types_update_rel_to_pool]. What derives the cell-level
    [wp_store__applyDeleteSpans] (the shape [own_store] still speaks)
    from the run-granular proof. *)
Lemma pool_after_delete_of_types (before after : gmap loc type_state) :
  (∀ c, c ∈ all_cells before -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells before -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells after -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells after -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  pool_after_delete (pool_of before) (pool_of after) ->
  delete_types_update_rel before after.
Proof.
  move=> Hckb Hclb Hcka Hcla [H1 [H2 [H3 [H4 H5]]]].
  have Hzb : ∀ c, c ∈ all_cells before ->
      uint.Z (cell_clock c) = Z.of_nat (run_clock (cell_run c)).
  { move=> c Hc. have := Hckb c Hc.
    rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  have Hza : ∀ c, c ∈ all_cells after ->
      uint.Z (cell_clock c) = Z.of_nat (run_clock (cell_run c)).
  { move=> c Hc. have := Hcka c Hc.
    rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  have Hclb' : ∀ c, c ∈ all_cells before ->
      uint.Z (cell_client c) = Z.of_nat (run_client (cell_run c)).
  { move=> c Hc. have := Hclb c Hc.
    rewrite /cell_client /run_client /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  have Hcla' : ∀ c, c ∈ all_cells after ->
      uint.Z (cell_client c) = Z.of_nat (run_client (cell_run c)).
  { move=> c Hc. have := Hcla c Hc.
    rewrite /cell_client /run_client /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  have Hmemb : ∀ r, r ∈ all_runs (pool_of before) -> ∃ c, c ∈ all_cells before ∧ r = cell_run c.
  { move=> r. rewrite all_runs_pool_of list_elem_of_fmap. move=> [c [-> Hc]]. eauto. }
  have Hmema : ∀ r, r ∈ all_runs (pool_of after) -> ∃ c, c ∈ all_cells after ∧ r = cell_run c.
  { move=> r. rewrite all_runs_pool_of list_elem_of_fmap. move=> [c [-> Hc]]. eauto. }
  have Hinb : ∀ c, c ∈ all_cells before -> cell_run c ∈ all_runs (pool_of before).
  { move=> c Hc. rewrite all_runs_pool_of. apply list_elem_of_fmap. eauto. }
  have Hina : ∀ c, c ∈ all_cells after -> cell_run c ∈ all_runs (pool_of after).
  { move=> c Hc. rewrite all_runs_pool_of. apply list_elem_of_fmap. eauto. }
  split_and!.
  - move=> q ts' Hq.
    have Hq' : pool_of after !! q = Some (type_model_of ts') by rewrite /pool_of lookup_fmap Hq.
    destruct (H1 q _ Hq') as (tm & Htm & Harr).
    rewrite /pool_of lookup_fmap in Htm.
    destruct (before !! q) as [ts|] eqn:Hts; last done.
    injection Htm as <-. exists ts. split; [done | exact Harr].
  - move=> q Hq.
    have Hq' : is_Some (pool_of before !! q) by rewrite /pool_of lookup_fmap fmap_is_Some.
    have := H2 q Hq'. rewrite /pool_of lookup_fmap fmap_is_Some //.
  - move=> c' Hc' Hd.
    destruct (H3 (cell_run c') (Hina c' Hc') Hd) as (r & Hr & Hrd & Hrin).
    destruct (Hmemb r Hr) as (c & Hc & ->).
    exists c. split_and!; [exact Hc | exact Hrd | exact Hrin].
  - move=> c Hc Hd y Hy.
    destruct (H4 (cell_run c) (Hinb c Hc) Hd y Hy) as (r' & Hr' & Hrd' & Hy').
    destruct (Hmema r' Hr') as (c' & Hc' & ->).
    exists c'. split_and!; [exact Hc' | exact Hrd' | exact Hy'].
  - move=> c Hc.
    destruct (H5 (cell_run c) (Hina c Hc)) as (r0 & Hr0 & Hcl & Hlo & Hhi).
    destruct (Hmemb r0 Hr0) as (c0 & Hc0 & ->).
    exists c0. split_and!; [exact Hc0 | | |].
    + apply (inj uint.Z). rewrite (Hcla' c Hc) (Hclb' c0 Hc0). lia.
    + rewrite (Hza c Hc) (Hzb c0 Hc0). lia.
    + rewrite (Hza c Hc) (Hzb c0 Hc0). move: Hhi. rewrite /cell_run /=. lia.
Qed.

(** [pool_split_step p locs parent k p' locs']: what one of the split
    helpers ([splitAtAndGetLeft] / [splitAtAndGetRight]) does to the run
    pool and the address map at slot [(parent, k)]: nothing, or one
    [split_runs] / [split_locs] surgery at a proper offset with a fresh
    address for the right half. The index-explicit form of
    [pool_after_split], which it implies ([pool_after_split_of_split_step]);
    what the two precise forms below weaken to and what
    [store.repair]'s run-granular proof steps by. *)
Definition pool_split_step (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (p' : pool) (locs' : gmap loc (list loc)) : Prop :=
  (p' = p ∧ locs' = locs) ∨
  (∃ (tm : type_model) (ls : list loc) (r : ItemRun) (o : nat) (rloc : loc),
     p !! parent = Some tm ∧ locs !! parent = Some ls ∧ tm_runs tm !! k = Some r ∧
     (0 < o < length (run_items r))%nat ∧
     rloc ≠ null ∧ rloc ∉ concat ((map_to_list locs).*2) ∧
     p' = <[parent := MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm)]> p ∧
     locs' = <[parent := split_locs ls k rloc]> locs).

Lemma pool_after_split_of_split_step (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (p' : pool) (locs' : gmap loc (list loc)) :
  (∀ r, r ∈ all_runs p -> run_wf (run_items r)) ->
  pool_split_step p locs parent k p' locs' ->
  pool_after_split p p' parent k.
Proof.
  move=> Hwf Hstep.
  destruct Hstep as [[-> ->] | (tm & ls & r & o & rloc & Hp & Hls & Hr & Ho & _ & _ & -> & ->)].
  - exact (pool_after_split_refl p parent k).
  - apply (pool_after_split_of_split_runs p parent tm k o r Hp Hr); last exact Ho.
    apply Hwf. apply (elem_of_all_runs p r). exists parent, tm.
    split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hr)].
Qed.

(** Where the address surgery leaves each slot: the split node's address at
    [k], the fresh right address at [S k] (the address half of
    [split_runs_lookup_left] / [_right]). *)
Lemma split_locs_lookup_left (ls : list loc) (k : nat) (rloc lc : loc) :
  ls !! k = Some lc ->
  split_locs ls k rloc !! k = Some lc.
Proof.
  move=> Hk. rewrite /split_locs Hk.
  have Hklen : (k < length ls)%nat := lookup_lt_Some _ _ _ Hk.
  have Htk : length (take k ls) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_r; last lia.
  rewrite Htk Nat.sub_diag //.
Qed.

Lemma split_locs_lookup_right (ls : list loc) (k : nat) (rloc lc : loc) :
  ls !! k = Some lc ->
  split_locs ls k rloc !! (S k) = Some rloc.
Proof.
  move=> Hk. rewrite /split_locs Hk.
  have Hklen : (k < length ls)%nat := lookup_lt_Some _ _ _ Hk.
  have Htk : length (take k ls) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_r; last lia.
  rewrite Htk.
  have -> : (S k - k)%nat = 1%nat by lia.
  done.
Qed.

Lemma split_locs_lookup_before (ls : list loc) (k : nat) (rloc : loc) (j : nat) :
  (j < k)%nat ->
  split_locs ls k rloc !! j = ls !! j.
Proof.
  move=> Hj. rewrite /split_locs.
  destruct (ls !! k) as [lc|] eqn:Hk; last done.
  have Hklen : (k < length ls)%nat := lookup_lt_Some _ _ _ Hk.
  have Htk : length (take k ls) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_l; last lia.
  rewrite lookup_take_lt; [done | lia].
Qed.

Lemma split_locs_lookup_after (ls : list loc) (k : nat) (rloc lc : loc) (j : nat) :
  ls !! k = Some lc -> (k < j)%nat ->
  split_locs ls k rloc !! (S j) = ls !! j.
Proof.
  move=> Hk Hj. rewrite /split_locs Hk.
  have Hklen : (k < length ls)%nat := lookup_lt_Some _ _ _ Hk.
  have Htk : length (take k ls) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_r; last lia.
  rewrite Htk /=.
  have -> : (S j - k)%nat = S (S (j - S k)) by lia.
  simpl. rewrite lookup_drop. f_equal. lia.
Qed.

(** Materializing a run list split at slot [k] (with the fresh right address
    [rloc]): the cell list split at [k]. *)
Lemma cells_of_locs_runs_split (parent : loc) (ls : list loc) (runs : list ItemRun)
    (k o : nat) (lc rloc : loc) (r : ItemRun) :
  length ls = length runs ->
  ls !! k = Some lc -> runs !! k = Some r ->
  cells_of_locs_runs parent (split_locs ls k rloc) (split_runs runs k o)
  = split_cells (cells_of_locs_runs parent ls runs) k o rloc.
Proof.
  move=> Hlen Hlk Hrk.
  have Hck : cells_of_locs_runs parent ls runs !! k = Some (MkItemCell lc (run_items r) (run_deleted r) parent).
  { rewrite /cells_of_locs_runs lookup_zip_with Hlk Hrk //. }
  rewrite /split_locs Hlk /split_runs Hrk /split_cells Hck /cells_of_locs_runs.
  rewrite zip_with_app; last by rewrite !length_take Hlen.
  rewrite -zip_with_take /=. rewrite -zip_with_drop. done.
Qed.


(** [pool_split_left_step p locs parent k d p' locs'] /
    [pool_split_right_step p locs parent k d l p' locs']: what
    [splitAtAndGetLeft] / [splitAtAndGetRight] do at the slot [(parent, k)]
    whose run covers [d]. Left: nothing when [d] is the run's last char,
    else the split just after [d]. Right: nothing when [d] is the run's
    head (the node's own address [l] comes back), else the split at [d]
    with the fresh right address [l] coming back. Both are one
    [pool_split_step] ([pool_split_step_of_left] / [_of_right]), and both
    pin where the requested boundary now sits
    ([pool_split_left_step_ends_at], [pool_split_right_step_starts_at]).
    What [wp_store__splitAtAndGetLeft_runs] / [_Right_runs] report. *)
Definition pool_split_left_step (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (d : YjsId) (p' : pool) (locs' : gmap loc (list loc)) : Prop :=
  ∃ (tm : type_model) (ls : list loc) (r : ItemRun),
    p !! parent = Some tm ∧ locs !! parent = Some ls ∧ tm_runs tm !! k = Some r ∧
    (((clock d - run_clock r)%nat = (length (run_items r) - 1)%nat ∧ p' = p ∧ locs' = locs) ∨
     ((clock d - run_clock r < length (run_items r) - 1)%nat ∧
      ∃ rloc : loc, rloc ≠ null ∧ rloc ∉ concat ((map_to_list locs).*2) ∧
        p' = <[parent := MkTypeModel (split_runs (tm_runs tm) k (clock d - run_clock r + 1)) (tm_arr tm)]> p ∧
        locs' = <[parent := split_locs ls k rloc]> locs)).

Definition pool_split_right_step (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (d : YjsId) (l : loc) (p' : pool) (locs' : gmap loc (list loc)) : Prop :=
  ∃ (tm : type_model) (ls : list loc) (r : ItemRun) (lc : loc),
    p !! parent = Some tm ∧ locs !! parent = Some ls ∧ tm_runs tm !! k = Some r ∧ ls !! k = Some lc ∧
    (((clock d - run_clock r)%nat = 0%nat ∧ l = lc ∧ p' = p ∧ locs' = locs) ∨
     ((0 < clock d - run_clock r)%nat ∧ l ≠ null ∧ l ∉ concat ((map_to_list locs).*2) ∧
      p' = <[parent := MkTypeModel (split_runs (tm_runs tm) k (clock d - run_clock r)) (tm_arr tm)]> p ∧
      locs' = <[parent := split_locs ls k l]> locs)).

Lemma pool_split_step_of_left (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (d : YjsId) (p' : pool) (locs' : gmap loc (list loc)) (r : ItemRun) :
  (∃ tm, p !! parent = Some tm ∧ tm_runs tm !! k = Some r) ->
  run_covers r d ->
  pool_split_left_step p locs parent k d p' locs' ->
  pool_split_step p locs parent k p' locs'.
Proof.
  move=> [tm0 [Hp0 Hr0]] [Hcl [Hlo Hhi]] [tm [ls [r' [Hp [Hls [Hr Hcase]]]]]].
  rewrite Hp0 in Hp. injection Hp as <-. rewrite Hr0 in Hr. injection Hr as <-.
  destruct Hcase as [[_ [-> ->]] | [Hlt (rloc & Hnn & Hfresh & -> & ->)]]; [by left | right].
  exists tm0, ls, r, (clock d - run_clock r + 1)%nat, rloc.
  split_and!; [exact Hp0 | exact Hls | exact Hr0 | lia | lia | exact Hnn | exact Hfresh | done | done].
Qed.

Lemma pool_split_step_of_right (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (d : YjsId) (l : loc) (p' : pool) (locs' : gmap loc (list loc)) (r : ItemRun) :
  (∃ tm, p !! parent = Some tm ∧ tm_runs tm !! k = Some r) ->
  run_covers r d ->
  pool_split_right_step p locs parent k d l p' locs' ->
  pool_split_step p locs parent k p' locs'.
Proof.
  move=> [tm0 [Hp0 Hr0]] [Hcl [Hlo Hhi]] [tm [ls [r' [lc [Hp [Hls [Hr [Hlk Hcase]]]]]]]].
  rewrite Hp0 in Hp. injection Hp as <-. rewrite Hr0 in Hr. injection Hr as <-.
  destruct Hcase as [[_ [_ [-> ->]]] | [Hpos (Hnn & Hfresh & -> & ->)]]; [by left | right].
  exists tm0, ls, r, (clock d - run_clock r)%nat, l.
  split_and!; [exact Hp0 | exact Hls | exact Hr0 | lia | lia | exact Hnn | exact Hfresh | done | done].
Qed.

(** The head id of a run is its client and clock. *)
Lemma run_head_item_id (r : ItemRun) :
  item_id (run_head_item r) = MkYjsId (run_client r) (run_clock r).
Proof. rewrite /run_client /run_clock. by destruct (item_id (run_head_item r)). Qed.

Lemma pool_split_left_step_ends_at (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (d : YjsId) (p' : pool) (locs' : gmap loc (list loc)) (r : ItemRun) (lc : loc) :
  (∃ tm, p !! parent = Some tm ∧ tm_runs tm !! k = Some r) ->
  (locs !! parent) ≫= (λ ls, ls !! k) = Some lc ->
  run_wf (run_items r) ->
  run_covers r d ->
  pool_split_left_step p locs parent k d p' locs' ->
  pool_run_starts_at p' parent k (item_id (run_head_item r)) ∧
  pool_run_ends_at p' parent k d ∧
  (locs' !! parent) ≫= (λ ls, ls !! k) = Some lc.
Proof.
  move=> [tm0 [Hp0 Hr0]] Hlc Hwf [Hcl [Hlo Hhi]] [tm [ls [r' [Hp [Hls [Hr Hcase]]]]]].
  rewrite Hp0 in Hp. injection Hp as <-. rewrite Hr0 in Hr. injection Hr as <-.
  rewrite Hls /= in Hlc.
  destruct Hcase as [[Hlast [-> ->]] | [Hlt (rloc & _ & _ & -> & ->)]].
  - split_and!.
    + exists tm0. split; first exact Hp0. exists r. done.
    + exists tm0. split; first exact Hp0. exists r. split_and!; [exact Hr0 | exact Hcl | lia].
    + rewrite Hls /=. exact Hlc.
  - have Ho : (0 < clock d - run_clock r + 1 < length (run_items r))%nat by lia.
    destruct (split_run_facts r _ Hwf Ho)
      as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
    split_and!.
    + exists (MkTypeModel (split_runs (tm_runs tm0) k (clock d - run_clock r + 1)) (tm_arr tm0)).
      rewrite lookup_insert_eq. split; first done.
      exists (split_run_left r (clock d - run_clock r + 1)). simpl.
      split; [exact (split_runs_lookup_left _ _ _ _ Hr0) | rewrite Hheadl //].
    + exists (MkTypeModel (split_runs (tm_runs tm0) k (clock d - run_clock r + 1)) (tm_arr tm0)).
      rewrite lookup_insert_eq. split; first done.
      exists (split_run_left r (clock d - run_clock r + 1)). simpl.
      split_and!; [exact (split_runs_lookup_left _ _ _ _ Hr0) | rewrite Hclientl // | rewrite Hclockl Hlenl; lia].
    + rewrite lookup_insert_eq /=. exact (split_locs_lookup_left ls k rloc lc Hlc).
Qed.

Lemma pool_split_right_step_starts_at (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (d : YjsId) (l : loc) (p' : pool) (locs' : gmap loc (list loc)) (r : ItemRun) :
  (∃ tm, p !! parent = Some tm ∧ tm_runs tm !! k = Some r) ->
  run_wf (run_items r) ->
  run_covers r d ->
  pool_split_right_step p locs parent k d l p' locs' ->
  ∃ k', pool_run_starts_at p' parent k' d ∧ (locs' !! parent) ≫= (λ ls, ls !! k') = Some l.
Proof.
  move=> [tm0 [Hp0 Hr0]] Hwf [Hcl [Hlo Hhi]] [tm [ls [r' [lc [Hp [Hls [Hr [Hlk Hcase]]]]]]]].
  rewrite Hp0 in Hp. injection Hp as <-. rewrite Hr0 in Hr. injection Hr as <-.
  destruct Hcase as [[Hhead [-> [-> ->]]] | [Hpos (_ & _ & -> & ->)]].
  - exists k. split.
    + exists tm0. split; first exact Hp0. exists r. split; first exact Hr0.
      rewrite run_head_item_id. destruct d as [dc dk]. simpl in *. f_equal; lia.
    + rewrite Hls /=. exact Hlk.
  - have Ho : (0 < clock d - run_clock r < length (run_items r))%nat by lia.
    destruct (split_run_facts r _ Hwf Ho)
      as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
    exists (S k). split.
    + exists (MkTypeModel (split_runs (tm_runs tm0) k (clock d - run_clock r)) (tm_arr tm0)).
      rewrite lookup_insert_eq. split; first done.
      exists (split_run_right r (clock d - run_clock r)). simpl.
      split; first exact (split_runs_lookup_right _ _ _ _ Hr0).
      rewrite run_head_item_id Hclientr Hclockr. destruct d as [dc dk]. simpl in *. f_equal; lia.
    + rewrite lookup_insert_eq /=. exact (split_locs_lookup_right ls k l lc Hlk).
Qed.

(** Under one split step at [(parent, k)], the run at another slot
    [(q, j)] survives at [j] (a different type, or [j < k]) or at [S j]
    ([k < j]), with its address. *)
Lemma pool_split_step_other_slot (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (p' : pool) (locs' : gmap loc (list loc)) (q : loc) (j : nat) (tm : type_model) (r : ItemRun) (l : loc) :
  pool_split_step p locs parent k p' locs' ->
  p !! q = Some tm -> tm_runs tm !! j = Some r ->
  (locs !! q) ≫= (λ ls, ls !! j) = Some l ->
  ¬ (q = parent ∧ j = k) ->
  ∃ j' tm', p' !! q = Some tm' ∧ tm_runs tm' !! j' = Some r ∧
            (locs' !! q) ≫= (λ ls, ls !! j') = Some l ∧
            (j' = j ∨ (q = parent ∧ (k < j)%nat ∧ j' = S j)).
Proof.
  move=> Hstep Hq Hr Hl Hnot.
  destruct Hstep as [[-> ->] | (tm0 & ls0 & r0 & o & rloc & Hp0 & Hls0 & Hr0 & Ho & _ & _ & -> & ->)].
  { exists j, tm. split_and!; [exact Hq | exact Hr | exact Hl | by left]. }
  destruct (decide (parent = q)) as [<- | Hne]; last first.
  { exists j, tm. rewrite !lookup_insert_ne; [| exact Hne | exact Hne].
    split_and!; [exact Hq | exact Hr | exact Hl | by left]. }
  rewrite Hq in Hp0. injection Hp0 as <-.
  destruct (locs !! parent) as [ls|] eqn:Hls; last done. simpl in Hl.
  injection Hls0 as <-.
  rewrite !lookup_insert_eq /=.
  destruct (decide (j < k)%nat) as [Hlt | Hge].
  - exists j, (MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm)). simpl.
    split_and!; [done | rewrite (split_runs_lookup_before _ _ _ _ _ Hr0 Hlt) // |
                 rewrite (split_locs_lookup_before _ _ _ _ Hlt) // | by left].
  - have Hgt : (k < j)%nat.
    { destruct (decide (j = k)) as [-> | Hne']; [exfalso; apply Hnot; done | lia]. }
    exists (S j), (MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm)). simpl.
    destruct (ls !! k) as [lk|] eqn:Hlk; last first.
    { exfalso. apply lookup_ge_None in Hlk.
      have := lookup_lt_Some _ _ _ Hl. lia. }
    split_and!; [done | rewrite (split_runs_lookup_after _ _ _ _ _ Hr0 Hgt) // |
                 rewrite (split_locs_lookup_after _ _ _ _ _ Hlk Hgt) // | right; done].
Qed.

Lemma fresh_loc_locs (l : loc) (types : gmap loc type_state) :
  fresh_loc l types <-> locs_fresh l (locs_of types).
Proof.
  rewrite /fresh_loc /locs_fresh /locs_of.
  split; move=> [Hnn H]; split; try exact Hnn.
  - move=> q lsq. rewrite lookup_fmap.
    destruct (types !! q) as [ts|] eqn:Hts; last by [].
    move=> /= [<-] Hin.
    apply H. apply list_elem_of_fmap in Hin as (c & -> & Hc).
    apply list_elem_of_fmap_2.
    apply all_cells_elem_of. exists q, ts. split; [exact Hts | exact Hc].
  - move=> Hin. apply list_elem_of_fmap in Hin as (c & -> & Hc).
    apply all_cells_elem_of in Hc as (q & ts & Hts & Hc).
    apply (H q (ic_loc <$> ty_cells ts)).
    + rewrite lookup_fmap Hts //.
    + apply list_elem_of_fmap_2. exact Hc.
Qed.

(** The pool's entries across a node split: the split entry becomes its two
    halves (the right one at the fresh address), every other entry stays
    (the run form of [split_pool_perm]). *)
Lemma pool_entries_split (locs : gmap loc (list loc)) (p : pool) (parent : loc)
    (ls : list loc) (tm : type_model) (k : nat) (l : loc) (r : ItemRun) (o : nat) (rloc : loc) :
  locs !! parent = Some ls -> p !! parent = Some tm ->
  ls !! k = Some l -> tm_runs tm !! k = Some r ->
  length ls = length (tm_runs tm) ->
  ∃ rest : list (loc * ItemRun),
    pool_entries locs p ≡ₚ (l, r) :: rest ∧
    pool_entries (<[parent := split_locs ls k rloc]> locs)
                 (<[parent := MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm)]> p)
      ≡ₚ (l, split_run_left r o) :: (rloc, split_run_right r o) :: rest.
Proof.
  move=> Hls Hp Hlk Hrk Hlen.
  set (F := λ (locs' : gmap loc (list loc)) (kv : loc * type_model),
              zip (default [] (locs' !! kv.1)) (tm_runs kv.2)).
  set (others := concat (F locs <$> map_to_list (delete parent p))).
  have Hpe : ∀ (locs' : gmap loc (list loc)) (tm' : type_model),
      (∀ q, q ≠ parent -> locs' !! q = locs !! q) ->
      pool_entries locs' (<[parent := tm']> p) ≡ₚ F locs' (parent, tm') ++ others.
  { move=> locs' tm' Hq. rewrite /pool_entries.
    have Hm : F locs' <$> map_to_list (<[parent := tm']> p)
            ≡ₚ F locs' <$> ((parent, tm') :: map_to_list (delete parent p)).
    { apply Permutation_map. exact (map_to_list_insert_existing p parent tm tm' Hp). }
    rewrite (concat_perm _ _ Hm) fmap_cons concat_cons. apply Permutation_app_head. rewrite /others.
    have -> : F locs' <$> map_to_list (delete parent p) = F locs <$> map_to_list (delete parent p);
      last reflexivity.
    apply list_fmap_ext. move=> i [q tmq] Hi. rewrite /F /=.
    have Hq' : delete parent p !! q = Some tmq
      by (apply elem_of_map_to_list; exact (list_elem_of_lookup_2 _ _ _ Hi)).
    apply lookup_delete_Some in Hq' as [Hne _]. rewrite (Hq q (λ H, Hne (eq_sym H))) //. }
  set (A := zip (take k ls) (take k (tm_runs tm))).
  set (B := zip (drop (S k) ls) (drop (S k) (tm_runs tm))).
  have HlenA : length (take k ls) = length (take k (tm_runs tm)) by rewrite !length_take Hlen.
  have Hother : ∀ q, q ≠ parent -> <[parent := split_locs ls k rloc]> locs !! q = locs !! q.
  { move=> q Hne. rewrite lookup_insert_ne //. }
  exists (A ++ B ++ others). split.
  - rewrite -{1}(insert_id p parent tm Hp) (Hpe locs tm (λ q _, eq_refl)) /F /= Hls /=.
    rewrite -{1}(take_drop_middle ls k l Hlk) -{1}(take_drop_middle (tm_runs tm) k r Hrk).
    rewrite zip_with_app; last exact HlenA.
    simpl. rewrite -/A -/B -app_assoc /=.
    symmetry. apply Permutation_middle.
  - rewrite (Hpe (<[parent := split_locs ls k rloc]> locs) _ Hother) /F /=.
    rewrite lookup_insert_eq /= /split_locs /split_runs Hlk Hrk /=.
    rewrite zip_with_app; last exact HlenA.
    simpl. rewrite -/A -/B -app_assoc /=.
    etransitivity; first (symmetry; apply Permutation_middle).
    apply perm_skip. symmetry. apply Permutation_middle.
Qed.

(** The address map stays well formed across a split whose right half lands
    at a fresh address. *)
Lemma locs_wf_split (locs : gmap loc (list loc)) (p : pool) (parent : loc)
    (ls : list loc) (tm : type_model) (k : nat) (l : loc) (r : ItemRun) (o : nat) (rloc : loc) :
  locs !! parent = Some ls -> p !! parent = Some tm ->
  ls !! k = Some l -> tm_runs tm !! k = Some r ->
  rloc ∉ concat ((map_to_list locs).*2) ->
  locs_wf locs p ->
  locs_wf (<[parent := split_locs ls k rloc]> locs)
          (<[parent := MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm)]> p).
Proof.
  move=> Hls Hp Hlk Hrk Hfresh [Hdom [Hnd Hlens]].
  have Hklt : (k < length ls)%nat := lookup_lt_Some _ _ _ Hlk.
  have Hperm0 : concat ((map_to_list locs).*2) ≡ₚ ls ++ concat ((map_to_list (delete parent locs)).*2).
  { rewrite -{1}(insert_id locs parent ls Hls).
    rewrite (concat_perm _ _ (Permutation_map snd (map_to_list_insert_existing locs parent ls ls Hls))) //. }
  have Hperm : concat ((map_to_list (<[parent := split_locs ls k rloc]> locs)).*2)
             ≡ₚ split_locs ls k rloc ++ concat ((map_to_list (delete parent locs)).*2).
  { rewrite (concat_perm _ _ (Permutation_map snd (map_to_list_insert_existing locs parent ls _ Hls))) //. }
  have Hsl : split_locs ls k rloc ≡ₚ rloc :: ls.
  { rewrite /split_locs Hlk -{3}(take_drop_middle ls k l Hlk).
    have -> : take k ls ++ [l; rloc] ++ drop (S k) ls = (take k ls ++ [l]) ++ rloc :: drop (S k) ls
      by rewrite -app_assoc //.
    have -> : take k ls ++ l :: drop (S k) ls = (take k ls ++ [l]) ++ drop (S k) ls
      by rewrite -app_assoc //.
    symmetry. apply Permutation_middle. }
  split_and!.
  - rewrite !dom_insert_L Hdom //.
  - rewrite Hperm Hsl. rewrite Hperm0 in Hnd Hfresh.
    apply NoDup_cons. split; [exact Hfresh | exact Hnd].
  - move=> q lsq tmq. destruct (decide (q = parent)) as [-> | Hne].
    + rewrite !lookup_insert_eq. move=> [<-] [<-]. simpl.
      have Hlsl := Hlens parent ls tm Hls Hp.
      rewrite /split_locs Hlk /= !length_app /= length_take_le; last lia.
      rewrite length_drop (split_runs_length _ _ _ _ Hrk). lia.
    + rewrite !lookup_insert_ne //. exact (Hlens q lsq tmq).
Qed.

End store_value_split.
