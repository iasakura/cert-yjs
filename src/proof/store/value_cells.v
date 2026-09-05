(** The [store] VALUE layer, part 1: the CELL BOOKKEEPING the store invariant
    is stated over. Go values but no Iris.

    Definitions
    - [type_state] / [all_cells]: what the invariant tracks per registered
      yType (its DLL cells and its model list), and the cells across the whole
      registry; [store_state], every field of the store at this cell level,
      and [store_invs], the two invariants every store method preserves.
    - the per-client node list: [cell_client] / [cell_clock] / [cell_le] /
      [cell_pr] / [cell_kp] and [client_run], the sorted run of one client's
      cells that shadows [store.items].
    - the pool invariants: location [NoDup], clock-range disjointness
      ([cells_range_disjoint]), [cell_fits], [cell_origin_clk], bundled as
      [pool_invs].
    - the registry coherence side conditions [doc_registry_coh] and
      [inputs_rooted_in_bind]; what [getOrCreateYType] does to the registry,
      [registry_lookup_or_create] ([pool_lookup_or_create] the same at run
      granularity, with the address map); the registry coherence and its
      model agreement at the pool, [pool_registry_coh] /
      [pool_registry_models] / [pool_doc_registry_coh].
    - where a step's cells come from: [cells_within] (inside an old cell) and
      [cells_within_or_from] (inside an old cell or an integrated input).
    - [type_model_of] / [pool_of] / [locs_of]: a type state and the pool at
      their run-granular models and address map; [store_state_runs] /
      [state_runs_of], the store state with the pool as [(sr_locs, sr_pool)]
      (plan-item-run-split stage 2); [locs_wf], the address map covering
      the registered types with one address per run and no address twice
      ([locs_wf_insert_same_len]); [locs_aligned], the pure alignment of
      an address map with a run pool; [types_of_locs_pool] /
      [state_of_runs], the cell-level registry and state a run-granular
      state determines (round-tripping under alignment,
      [pool_of_types_of_locs_pool] / [locs_of_types_of_locs_pool] /
      [state_runs_of_of_runs] / [locs_aligned_of], the identity on a
      parent-coherent registry, [types_of_locs_pool_of]; materialization
      across one registry slot, [types_of_locs_pool_insert], or across
      that slot's addresses and model together,
      [types_of_locs_pool_insert_both], or of a map pair that agrees with
      another away from one slot, [types_of_locs_pool_ext_insert]; the
      per-client index at run granularity: [pool_entries] (the pool's
      (address, run) pairs), [entry_kp] (their (client, clock, address)
      keys), [kp_client_locs] (one client's addresses in clock order off such
      keys, unique under [kp_clkloc]; reshuffled by [kp_client_locs_perm] /
      [_other] / [_snoc_max] / [_insert]) and [client_locs] over the
      entries, meeting [client_run] at [client_run_kp_locs] /
      [client_locs_of] and the materialized registry at [entries_kp_of] /
      [entries_kp_to_cells]; [client_entries], the client's entries in
      clock order ([client_entries_prs] / [client_locs_entries], [client_entries_mem] /
      [_sorted] / [_lookup_slot]; [sorted_client_entries], any clock-sorted
      address-distinct list of one client's entries, with disjoint clock
      ranges, [sorted_client_entries_disjoint], the index's own being one,
      [client_entries_sorted_client]), with the pool's entries at
      their slots, [pool_entries_slot] / [pool_entries_snd] /
      [pool_entries_locs_NoDup], one integrate splice adding its entry
      ([pool_entries_integrate], with [locs_wf_integrate] for the address
      map) and one tombstoning keeping every key ([pool_entries_flip_kp]);
      what a delete step transports ([pool_after_delete_seq_map] /
      [pool_after_delete_arr_pointwise] /
      [pool_registry_models_after_delete]); [entry_clock_Z], an entry's machine-word
      clock under the pool's clock bound); alignment surviving a same-length
      type update, [locs_aligned_insert_same_len], or a slot's addresses
      and model replaced together at equal length,
      [locs_aligned_insert_both], and giving each type a same-length
      address list, [locs_aligned_lens]); [cells_within_or_from] projects
      onto [runs_within_or_from] under the id no-wrap bounds
      ([cells_within_or_from_to_runs]).
    - what one integrate asks and does, at the cell level: [pool_clock_below]
      (the new item is its client's newest), [origins_linked] (the item's
      links are the cells its resolved origins designate), [integrate_splice]
      (the new cell and its run are spliced at matching indices) and
      [run_denotes] (the run is the input's); [integrate_locs], the
      address-list half of one splice.

    Laws
    - the cell vocabulary projects along [cell_run] ([cell_client_run] /
      [cell_clock_run] / [cell_covers_run] / [cell_origin_clk_run];
      [cell_fits_run] and [cells_range_disjoint_runs] under the id no-wrap
      bounds, the latter trading address inequality for index inequality
      under the heap [NoDup]); [origins_linked] is [origins_resolved] at the
      cursor indices plus the [node_loc] readings
      ([origins_linked_resolved]); [all_runs] of a
      projected pool is the projected [all_cells] ([all_runs_pool_of]) and
      [pool_invs] gives [run_pool_invs] under the id no-wrap bounds
      ([run_pool_invs_of]) and [pool_run_clock_below] reads back on the
      cells ([pool_run_clock_below_to_cell]) and [pool_clock_below] at run
      granularity ([pool_clock_below_to_run]);
      [registry_lookup_or_create] carries to [(locs, p)]
      ([registry_lookup_or_create_to_pool]); [pool_of] / [locs_of] under a
      registry insert
      and the address map's flattening ([pool_of_insert] / [locs_of_insert]
      / [locs_of_concat]); [client_run] projects onto [client_runs]
      ([client_run_runs], the clock orders agreeing and same-client clocks
      unique).
    - the pool invariants are preserved by appending a fresh cell ([*_snoc],
      assembled for one integrate as [pool_invs_integrate])
      and by any permutation that keeps locations and runs
      ([locs_run_perm_*], [flip_locs_run_perm] / [pool_invs_flip] /
      [flip_pool_perm] for the tombstone flip). These are the two shapes every
      store operation takes.
    - [all_cells] under a registry insert ([all_cells_insert(_snoc/_empty)],
      [all_cells_lookup]); under the address [NoDup] one location pins its
      type, slot and cell ([all_cells_same_loc_same_slot]); a coherent
      registry's type domain grows with its bindings
      ([registry_coh_dom_mono]).
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
From New.proof Require Import core prelude algebra network_model.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
Local Open Scope Z_scope.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From New.proof.store Require Import model value_span.
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

#[local] Instance pr_le_dec : RelDecision pr_le.
Proof. rewrite /pr_le. solve_decision. Defined.
#[local] Instance pr_le_trans : Transitive pr_le.
Proof. rewrite /pr_le. move=> x y z. lia. Qed.
#[local] Instance pr_le_total : Total pr_le.
Proof. rewrite /pr_le. move=> x y. lia. Qed.

(* ----- the part-6 pool invariants (issue #28): loc NoDup + range disjointness *)

(** Per-client clock-RANGE disjointness of the document cell pool: two distinct
    same-client cells occupy disjoint clock intervals [clock, clock + len).
    It pins the covering cell [getNodeIndex] returns uniquely once runs are
    multi-char. *)
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

(** [pool_clock_below types id]: every cell of [id]'s client in the pool ends
    strictly below [id]'s clock, in machine words: the item about to be
    integrated is its client's newest ([maximalId] at the cell level), which
    is what keeps [AddNode]'s appended run list clock-sorted. *)
Definition pool_clock_below (types : gmap loc type_state) (id : YjsId) : Prop :=
  ∀ c0, c0 ∈ all_cells types -> cell_client c0 = W64 (clientId id) ->
    (uint.Z (cell_clock c0) < uint.Z (W64 (clock id)))%Z ∧
    (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (W64 (clock id)))%Z.

(** [origins_linked cells arr input lft rgt]: [lft] and [rgt] are the cells
    the resolved origins of [input] in [arr] designate: [lft] ends at the
    model index of the left origin and [rgt] starts at that of the right
    origin ([findLeftIdx] / [findRightIdx]), each named by the cell cursor
    whose prefix sum is that index, and [null] at a document boundary. What
    [store.repair] (or the local-edit creator) wrote into the item's [left]
    and [right] links before [Store.Integrate] runs. *)
Definition origins_linked (cells : list item_cell) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (lft rgt : loc) : Prop :=
  ∃ (leftIdx rightIdx : Z) (curL curR : nat),
    findLeftIdx (in_originId input) arr = Some leftIdx ∧
    findRightIdx (in_rightOriginId input) arr = Some rightIdx ∧
    lft = node_loc cells (Z.of_nat curL - 1) ∧
    rgt = node_loc cells (Z.of_nat curR) ∧
    (Z.of_nat (length (run_flatten (take curL cells))) = leftIdx + 1)%Z ∧
    (curL <= length cells)%nat ∧
    (Z.of_nat (length (run_flatten (take curR cells))) = rightIdx)%Z ∧
    (curR <= length cells)%nat.

(** [integrate_splice cells arr item_l run parent cells' arr']: what one
    integrate does to a type: a fresh live cell at [item_l] carrying [run] is
    spliced into [cells] at some cell index, and [run] into [arr] at the
    matching model index (the prefix sum of the cells before it). *)
Definition integrate_splice (cells : list item_cell) (arr : list (YjsItem A))
    (item_l : loc) (run : list (YjsItem A)) (parent : loc)
    (cells' : list item_cell) (arr' : list (YjsItem A)) : Prop :=
  ∃ idx : nat,
    (idx <= length cells)%nat ∧
    (length (run_flatten (take idx cells)) <= length arr)%nat ∧
    cells' = take idx cells ++ MkItemCell item_l run false parent :: drop idx cells ∧
    arr' = take (length (run_flatten (take idx cells))) arr ++ run ++
           drop (length (run_flatten (take idx cells))) arr.

(** [run_denotes input newItem run]: the run a wire item lands as: its head is
    the item the input resolves to (same id and origins) and it has one char
    per byte of the input's content. *)
Definition run_denotes (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (run : list (YjsItem A)) : Prop :=
  item_id (hd inhabitant run) = in_id input ∧
  origin (hd inhabitant run) = origin newItem ∧
  rightOrigin (hd inhabitant run) = rightOrigin newItem ∧
  length run = length (in_content input).

(** [integrate_locs ls idx item_l]: the address-list half of one integrate
    splice: the fresh node's address [item_l] inserted at the cursor [idx]
    ([runs_integrate_splice_at] is the run half, at the same cursor). *)
Definition integrate_locs (ls : list loc) (idx : nat) (item_l : loc) : list loc :=
  take idx ls ++ item_l :: drop idx ls.

(** [inputs_rooted_in_bind inputs bind]: every origin-free tagged input targets
    a root name that is already bound in [bind]. An op with neither a left nor a
    right origin attaches directly under a registered root, so that root must
    exist for the op to integrate. *)
Definition inputs_rooted_in_bind (inputs : list (TId * IntegrateInput (A := A)))
    (bind : gmap P loc) : Prop :=
  ∀ typedInput, typedInput ∈ inputs ->
    in_originId typedInput.2 = None -> in_rightOriginId typedInput.2 = None ->
    ∃ name, typedInput.1 = RootId name ∧ is_Some (bind !! name).

(** [registry_coh bind types]: the root registry [bind] (name -> type loc)
    and the type pool [types] fit together: every bound name has a live type,
    [bind] is injective, and every live type is bound under some name. A
    heap-level fact: every store method preserves it, so [own_store_struct]
    carries it. *)
Definition registry_coh (bind : gmap P loc) (types : gmap loc type_state) : Prop :=
  (∀ nm p, bind !! nm = Some p -> is_Some (types !! p)) /\
  (∀ n1 n2 p, bind !! n1 = Some p -> bind !! n2 = Some p -> n1 = n2) /\
  (∀ p, is_Some (types !! p) -> ∃ nm, bind !! nm = Some p).

(** [registry_models m bind types]: the replayed doc model [m] is what the
    registry holds: it agrees with each bound type's item list at that
    type's root name, and it is populated only at bound root names. The
    model-level half of the store's registry invariant, next to the
    heap-level [registry_coh]. *)
Definition registry_models (m : DocModel) (bind : gmap P loc)
    (types : gmap loc type_state) : Prop :=
  (∀ nm p ts, bind !! nm = Some p -> types !! p = Some ts ->
     doc_model_get m (RootId nm) = ty_arr ts) /\
  (∀ t, doc_model_get m t ≠ [] -> ∃ nm p, t = RootId nm /\ bind !! nm = Some p).

(** The store's whole *registry coherence*: the name->loc bindings [bind], the
    per-type heap state [types], and the replayed doc model [m] fit together,
    [registry_coh] and [registry_models] at once. *)
Definition doc_registry_coh (m : DocModel) (bind : gmap P loc)
    (types : gmap loc type_state) : Prop :=
  registry_coh bind types /\ registry_models m bind types.

(** [pool_registry_coh bind p] / [pool_registry_models m bind p]: the
    registry's coherence and its doc-model agreement, read at the run pool.
    [registry_coh_pool] / [registry_models_pool] transport them along
    [pool_of] as equivalences (the fmap preserves the domain). What C5
    states the repair / applyUpdate specs over. *)
Definition pool_registry_coh (bind : gmap P loc) (p : pool) : Prop :=
  (∀ nm q, bind !! nm = Some q -> is_Some (p !! q)) /\
  (∀ n1 n2 q, bind !! n1 = Some q -> bind !! n2 = Some q -> n1 = n2) /\
  (∀ q, is_Some (p !! q) -> ∃ nm, bind !! nm = Some q).

Definition pool_registry_models (m : DocModel) (bind : gmap P loc) (p : pool) : Prop :=
  (∀ nm q tm, bind !! nm = Some q -> p !! q = Some tm ->
     doc_model_get m (RootId nm) = tm_arr tm) /\
  (∀ t, doc_model_get m t ≠ [] -> ∃ nm q, t = RootId nm /\ bind !! nm = Some q).

(** [pool_doc_registry_coh m bind p]: [doc_registry_coh] at the run pool,
    both clauses at once (what the lock body carries). *)
Definition pool_doc_registry_coh (m : DocModel) (bind : gmap P loc) (p : pool) : Prop :=
  pool_registry_coh bind p /\ pool_registry_models m bind p.

(** [pool_invs types]: the invariants of the document cell pool that the model
    does not determine: every cell's clock range fits in [w64] ([cell_fits]),
    node locations are distinct, same-client cells occupy disjoint clock
    ranges ([cells_range_disjoint]) and every head's same-client origin is
    strictly older ([cell_origin_clk]). Carried by [store_inv] / [own_store]
    and preserved by every store method; the splice ([*_snoc]) and the
    tombstone flip ([pool_invs_flip]) are its two transition laws. *)
(** [cells_within before after]: every cell of [after] sits, as one client's
    clock range, inside a cell of [before]: splits and tombstones narrow or keep
    ranges, never invent chars. The last clause of the three transport records. *)
Definition cells_within (before after : list item_cell) : Prop :=
  ∀ c, c ∈ after -> ∃ c0, c0 ∈ before ∧ cell_client c = cell_client c0 ∧
     (uint.Z (cell_clock c0) <= uint.Z (cell_clock c))%Z ∧
     (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <=
      uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)))%Z.

(** [cells_within_or_from inputs before after]: every cell of [after] sits
    inside a cell of [before] or inside the clock range of one of the
    integrated [inputs] (what applying a batch adds). *)
Definition cells_within_or_from (inputs : list (TId * IntegrateInput (A := A)))
    (before after : list item_cell) : Prop :=
  ∀ c, c ∈ after ->
    (∃ c0, c0 ∈ before ∧ cell_client c = cell_client c0 ∧
       (uint.Z (cell_clock c0) <= uint.Z (cell_clock c))%Z ∧
       (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <=
        uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)))%Z) ∨
    (∃ typedInput : TId * IntegrateInput (A := A), typedInput ∈ inputs ∧
       cell_client c = W64 (clientId (in_id typedInput.2)) ∧
       (uint.Z (W64 (clock (in_id typedInput.2))) <= uint.Z (cell_clock c))%Z ∧
       (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <=
        uint.Z (W64 (clock (in_id typedInput.2))) + Z.of_nat (length (in_content typedInput.2)))%Z).

(** [registry_lookup_or_create types bind nm p types' bind']: what
    [getOrCreateYType nm] does to the registry: hands back the root bound to
    [nm] unchanged, or binds [nm] to a fresh empty type at [p]. *)
Definition registry_lookup_or_create (types : gmap loc type_state) (bind : gmap P loc)
    (nm : P) (p : loc) (types' : gmap loc type_state) (bind' : gmap P loc) : Prop :=
  (bind !! nm = Some p ∧ types' = types ∧ bind' = bind) ∨
  (bind !! nm = None ∧ types !! p = None ∧
   types' = <[p := MkTypeState [] []]> types ∧ bind' = <[nm := p]> bind).

(** [pool_lookup_or_create p ls bind nm q p' ls' bind']:
    [registry_lookup_or_create] at run granularity, over the pool and its
    address map: the root bound to [nm] handed back unchanged, or [nm] bound
    to a fresh empty type at [q] (empty run list, empty address list). *)
Definition pool_lookup_or_create (p : pool) (ls : gmap loc (list loc))
    (bind : gmap P loc) (nm : P) (q : loc)
    (p' : pool) (ls' : gmap loc (list loc)) (bind' : gmap P loc) : Prop :=
  (bind !! nm = Some q ∧ p' = p ∧ ls' = ls ∧ bind' = bind) ∨
  (bind !! nm = None ∧ p !! q = None ∧
   p' = <[q := MkTypeModel [] []]> p ∧ ls' = <[q := []]> ls ∧
   bind' = <[nm := q]> bind).

Definition pool_invs (types : gmap loc type_state) : Prop :=
  (∀ c, c ∈ all_cells types -> cell_fits c) ∧
  NoDup (ic_loc <$> all_cells types) ∧
  cells_range_disjoint (all_cells types) ∧
  (∀ c, c ∈ all_cells types -> cell_origin_clk c).

(** [store_state]: the store's cell-level state, every field of a [store]
    under the write lock: the local client and its next clock, the type pool,
    the root registry, and the buffered wire items and delete spans. The
    model every store-internal method is specified over ([own_store_struct]). *)
Record store_state := MkStoreState {
  ss_client : w64;
  ss_clock : w64;
  ss_types : gmap loc type_state;
  ss_bind : gmap P loc;
  ss_pending : list (TId * IntegrateInput (A := A));
  ss_pending_deletes : list delete_span;
}.

#[export] Instance settable_store_state : Settable store_state :=
  settable! MkStoreState <ss_client; ss_clock; ss_types; ss_bind; ss_pending; ss_pending_deletes>.

(** [store_invs st]: the two invariants every store method preserves: the
    pool's ([pool_invs]) and the registry's coherence with it ([registry_coh]). *)
Definition store_invs (st : store_state) : Prop :=
  pool_invs (ss_types st) ∧ registry_coh (ss_bind st) (ss_types st).

(* ===== lemmas ============================================================= *)

(** The pool-level cell vocabulary projects along [cell_run]
    (docs/plan-item-run-split.md stage 1). The [w64] readings agree with the
    pure [nat] ones outright for client / clock / covers / origin, and under
    the id no-wrap bound for [cell_fits] and range disjointness (where the
    machine word would otherwise wrap; the bound is what the heap layer's
    id round-trip provides, [own_type_pool_id_bounds]). Disjointness also
    trades [ic_loc c1 ≠ ic_loc c2] for [i ≠ j], which needs the heap-layer
    [NoDup] of node addresses. *)
Lemma cell_client_run (c : item_cell) : cell_client c = W64 (run_client (cell_run c)).
Proof. reflexivity. Qed.

Lemma cell_clock_run (c : item_cell) : cell_clock c = W64 (run_clock (cell_run c)).
Proof. reflexivity. Qed.

Lemma cell_origin_clk_run (c : item_cell) :
  cell_origin_clk c ↔ run_origin_clk (cell_run c).
Proof. reflexivity. Qed.

Lemma cell_covers_run (c : item_cell) (d : YjsId) :
  cell_covers c d ↔ run_covers (cell_run c) d.
Proof. reflexivity. Qed.

Lemma cell_fits_run (c : item_cell) :
  (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z ->
  (cell_fits c ↔ run_fits (cell_run c)).
Proof.
  rewrite /cell_fits /run_fits /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
  move=> Hb. split; move=> H; word.
Qed.

(** [origins_linked] is [origins_resolved] at the cursor indices plus the
    [node_loc] reading of the two link addresses; [integrate_splice] projects
    to [runs_integrate_splice], the new node's address and type being all it
    adds. The prefix sums agree by [run_flatten_runs]. *)
Lemma origins_linked_resolved (cells : list item_cell) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (lft rgt : loc) :
  origins_linked cells arr input lft rgt ↔
  ∃ (kL kR : nat), origins_resolved (cell_run <$> cells) arr input kL kR ∧
    lft = node_loc cells (Z.of_nat kL - 1) ∧ rgt = node_loc cells (Z.of_nat kR).
Proof.
  rewrite /origins_linked /origins_resolved. split.
  - intros (leftIdx & rightIdx & curL & curR & HL & HR & -> & -> & HpsL & HbL & HpsR & HbR).
    exists curL, curR. split_and!; [| reflexivity | reflexivity].
    exists leftIdx, rightIdx.
    rewrite -!fmap_take -?fmap_drop -!run_flatten_runs length_fmap.
    split_and!; assumption.
  - intros (kL & kR & (leftIdx & rightIdx & HL & HR & HpsL & HbL & HpsR & HbR) & -> & ->).
    exists leftIdx, rightIdx, kL, kR.
    move: HpsL HpsR HbL HbR. rewrite -!fmap_take -?fmap_drop -!run_flatten_runs length_fmap.
    move=> HpsL HpsR HbL HbR. split_and!; try assumption; reflexivity.
Qed.

Lemma cells_range_disjoint_runs (pool : list item_cell) :
  (∀ c, c ∈ pool -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ pool -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> pool) ->
  (cells_range_disjoint pool ↔ runs_disjoint (cell_run <$> pool)).
Proof.
  move=> Hbnd Hcbnd Hnd.
  have Hclk : ∀ c, c ∈ pool -> uint.Z (cell_clock c) = Z.of_nat (run_clock (cell_run c)).
  { move=> c Hc. have := Hbnd c Hc. rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  split.
  - move=> Hdisj i j r1 r2 Hi Hj Hij Hcl.
    rewrite list_lookup_fmap in Hi. rewrite list_lookup_fmap in Hj.
    destruct (pool !! i) as [c1|] eqn:Hci; last done.
    destruct (pool !! j) as [c2|] eqn:Hcj; last done.
    simpl in Hi, Hj. simplify_eq.
    have Hm1 : c1 ∈ pool := list_elem_of_lookup_2 _ _ _ Hci.
    have Hm2 : c2 ∈ pool := list_elem_of_lookup_2 _ _ _ Hcj.
    have Hlocne : ic_loc c1 ≠ ic_loc c2.
    { move=> Heq.
      have Hl1 : (ic_loc <$> pool) !! i = Some (ic_loc c2) by rewrite list_lookup_fmap Hci /= Heq.
      have Hl2 : (ic_loc <$> pool) !! j = Some (ic_loc c2) by rewrite list_lookup_fmap Hcj.
      exact (Hij (NoDup_lookup _ _ _ _ Hnd Hl1 Hl2)). }
    have Hcc : cell_client c1 = cell_client c2.
    { rewrite !cell_client_run Hcl //. }
    have Hd := Hdisj c1 c2 Hm1 Hm2 Hcc Hlocne.
    move: Hd. rewrite (Hclk c1 Hm1) (Hclk c2 Hm2) /cell_run /=. lia.
  - move=> Hdisj c1 c2 Hm1 Hm2 Hcc Hlocne.
    destruct (list_elem_of_lookup_1 _ _ Hm1) as (i & Hci).
    destruct (list_elem_of_lookup_1 _ _ Hm2) as (j & Hcj).
    have Hij : i ≠ j.
    { move=> Heq. subst j. rewrite Hci in Hcj. simplify_eq. }
    have Hcl : run_client (cell_run c1) = run_client (cell_run c2).
    { have Huz := f_equal uint.Z Hcc. move: Huz.
      rewrite !cell_client_run /=.
      have Hb1 := Hcbnd c1 Hm1. have Hb2 := Hcbnd c2 Hm2.
      move=> Huz. word. }
    have Hd := Hdisj i j (cell_run c1) (cell_run c2)
              ltac:(rewrite list_lookup_fmap Hci //) ltac:(rewrite list_lookup_fmap Hcj //) Hij Hcl.
    rewrite (Hclk c1 Hm1) (Hclk c2 Hm2) /cell_run /=.
    move: Hd. rewrite /cell_run /=. lia.
Qed.

(** [type_model_of] / [pool_of]: a [type_state] and a type-state pool at
    their run-granular models. [all_runs] of a projected pool is the
    projected [all_cells], and the cell-level [pool_invs] gives
    [run_pool_invs] under the id no-wrap bounds (the range-disjointness
    trade of [cells_range_disjoint_runs]). *)
Definition type_model_of (ts : type_state) : type_model :=
  MkTypeModel (cell_run <$> ty_cells ts) (ty_arr ts).

Definition pool_of (types : gmap loc type_state) : pool :=
  type_model_of <$> types.

(** The address map of a cell-level pool: each type's node addresses (the
    heap half [pool_of] forgets). *)
Definition locs_of (types : gmap loc type_state) : gmap loc (list loc) :=
  (λ ts, ic_loc <$> ty_cells ts) <$> types.

(** [store_state_runs]: [store_state] at run granularity
    (plan-item-run-split stage 2): the type pool as [(sr_locs, sr_pool)]
    instead of the cell-level [ss_types]. [state_runs_of] projects;
    [own_store_runs] ([store/heap.v]) is the store at such a state. *)
Record store_state_runs := MkStoreStateRuns {
  sr_client : w64;
  sr_clock : w64;
  sr_locs : gmap loc (list loc);
  sr_pool : pool;
  sr_bind : gmap P loc;
  sr_pending : list (TId * IntegrateInput (A := A));
  sr_pending_deletes : list delete_span;
}.

Definition state_runs_of (st : store_state) : store_state_runs :=
  MkStoreStateRuns (ss_client st) (ss_clock st)
    (locs_of (ss_types st)) (pool_of (ss_types st))
    (ss_bind st) (ss_pending st) (ss_pending_deletes st).

#[export] Instance settable_store_state_runs : Settable store_state_runs :=
  settable! MkStoreStateRuns
    <sr_client; sr_clock; sr_locs; sr_pool; sr_bind; sr_pending; sr_pending_deletes>.

(** [locs_aligned locs p]: the pure alignment of an address map with a run
    pool: same type domain, and per type as many addresses as runs. The pure
    half of [store/heap.v]'s [locs_wf] (which adds the heap [NoDup]); what
    the [types_of_locs_pool] round-trips run on, and the pure conjunct of
    the primitive [own_store_runs]. *)
Definition locs_aligned (locs : gmap loc (list loc)) (p : pool) : Prop :=
  dom locs = dom p ∧
  (∀ parent ls tm, locs !! parent = Some ls -> p !! parent = Some tm ->
     length ls = length (tm_runs tm)).

(** [locs_wf locs p]: the heap-only half of the pool invariants at run
    granularity (plan-item-run-split stage 2): the address map covers
    exactly the registered types, one node address per run, and no node is
    in two types or at two indices. What [pool_invs]'s [NoDup] becomes once
    addresses leave the pure layer. *)
Definition locs_wf (locs : gmap loc (list loc)) (p : pool) : Prop :=
  dom locs = dom p ∧
  NoDup (concat ((map_to_list locs).*2)) ∧
  (∀ parent ls tm, locs !! parent = Some ls -> p !! parent = Some tm ->
     length ls = length (tm_runs tm)).

(** [types_of_locs_pool locs p]: the cell-level registry an address map and a
    run pool determine: each type's cells re-materialized as
    [cells_of_locs_runs] (the run-granular POOL elimination,
    [own_type_pool_runs_to_cells]). *)
Definition types_of_locs_pool (locs : gmap loc (list loc)) (p : pool)
    : gmap loc type_state :=
  map_imap (λ parent tm,
    Some (MkTypeState (cells_of_locs_runs parent (default [] (locs !! parent)) (tm_runs tm))
                      (tm_arr tm))) p.

(** [state_of_runs str]: the cell-level state a run-granular state
    determines: the registry re-materialized as [types_of_locs_pool], every
    other field carried over. The section of [state_runs_of]
    ([state_runs_of_of_runs]), and what the primitive [own_store_runs] holds
    the store at. *)
Definition state_of_runs (str : store_state_runs) : store_state :=
  MkStoreState (sr_client str) (sr_clock str)
    (types_of_locs_pool (sr_locs str) (sr_pool str))
    (sr_bind str) (sr_pending str) (sr_pending_deletes str).


Lemma all_runs_pool_of (types : gmap loc type_state) :
  all_runs (pool_of types) = cell_run <$> all_cells types.
Proof.
  rewrite /all_runs /pool_of /all_cells map_to_list_fmap concat_fmap.
  f_equal. rewrite -!list_fmap_compose.
  apply list_fmap_ext. move=> i [k ts] Hl. reflexivity.
Qed.

Lemma run_pool_invs_of (types : gmap loc type_state) :
  (∀ c, c ∈ all_cells types -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells types -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  pool_invs types ->
  run_pool_invs (pool_of types).
Proof.
  move=> Hckb Hclb [Hfits [Hnd [Hdisj Hoc]]].
  rewrite /run_pool_invs all_runs_pool_of.
  split_and!.
  - intros r Hr. apply list_elem_of_fmap in Hr as (c & -> & Hc).
    apply (cell_fits_run c (Hckb c Hc)). exact (Hfits c Hc).
  - apply (cells_range_disjoint_runs _ Hckb Hclb Hnd). exact Hdisj.
  - intros r Hr. apply list_elem_of_fmap in Hr as (c & -> & Hc).
    apply cell_origin_clk_run. exact (Hoc c Hc).
Qed.

(** The converse: the pool invariants at the cells, from the run-granular
    ones and the address [NoDup] (the [locs_wf] half). The pure leg of
    [own_store_runs_to_state]. *)
Lemma pool_invs_of_runs (types : gmap loc type_state) :
  (∀ c, c ∈ all_cells types -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells types -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  run_pool_invs (pool_of types) ->
  pool_invs types.
Proof.
  move=> Hckb Hclb Hnd. rewrite /run_pool_invs all_runs_pool_of. move=> [Hfits [Hdisj Hoc]].
  split_and!.
  - move=> c Hc. apply (cell_fits_run c (Hckb c Hc)). apply Hfits. exact (list_elem_of_fmap_2 _ _ _ Hc).
  - exact Hnd.
  - apply (cells_range_disjoint_runs _ Hckb Hclb Hnd). exact Hdisj.
  - move=> c Hc. apply cell_origin_clk_run. apply Hoc. exact (list_elem_of_fmap_2 _ _ _ Hc).
Qed.

(** A registry's per-type item sets read through [pool_of]: what the item-set
    authority ([store/heap]'s [Hseq]) carries at the two granularities; and a
    materialized registry entry's document is its model's. *)
Lemma pool_of_seq_map (types : gmap loc type_state) :
  (λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> pool_of types
  = (λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types.
Proof.
  rewrite /pool_of. apply map_eq => q. rewrite !lookup_fmap.
  destruct (types !! q) as [ts|]; reflexivity.
Qed.

Lemma types_of_locs_pool_arr (locs : gmap loc (list loc)) (p : pool) (q : loc) (ts : type_state) :
  types_of_locs_pool locs p !! q = Some ts -> ∃ tm, p !! q = Some tm ∧ ty_arr ts = tm_arr tm.
Proof.
  rewrite /types_of_locs_pool map_lookup_imap. move=> /bind_Some [tm [Htm Hf]].
  injection Hf as <-. exists tm. split; [exact Htm | reflexivity].
Qed.

(** [pool_run_clock_below] read back on the cells: under the pool id bounds
    and nonempty runs, the [nat] clock bound gives [pool_clock_below]'s [w64]
    comparisons. The premise side of [wp_store__Integrate_runs]. *)
Lemma pool_run_clock_below_to_cell (types : gmap loc type_state) (id : YjsId) :
  (∀ c, c ∈ all_cells types -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells types -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells types -> ic_run c ≠ []) ->
  (Z.of_nat (clientId id) < 2^64)%Z ->
  (Z.of_nat (clock id) < 2^64)%Z ->
  pool_run_clock_below (pool_of types) id ->
  pool_clock_below types id.
Proof.
  move=> Hckb Hclb Hne Hidcl Hidck Hrb c0 Hc0 Hclient.
  have Hcl : uint.Z (cell_client c0) = Z.of_nat (run_client (cell_run c0)).
  { have := Hclb c0 Hc0.
    rewrite /cell_client /run_client /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  have Hck : uint.Z (cell_clock c0) = Z.of_nat (run_clock (cell_run c0)).
  { have := Hckb c0 Hc0.
    rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  have Hclid : run_client (cell_run c0) = clientId id.
  { apply Nat2Z.inj. rewrite -Hcl Hclient. word. }
  have Hmem : cell_run c0 ∈ all_runs (pool_of types).
  { rewrite all_runs_pool_of. apply list_elem_of_fmap. by exists c0. }
  have Hsum := Hrb (cell_run c0) Hmem Hclid.
  have Hlenr : length (ic_run c0) = length (run_items (cell_run c0)) by reflexivity.
  have Huck : uint.Z (W64 (clock id)) = Z.of_nat (clock id) by word.
  have Hnn : ic_run c0 ≠ [] := Hne c0 Hc0.
  have Hpos : (1 <= length (run_items (cell_run c0)))%nat.
  { rewrite -Hlenr. destruct (ic_run c0) eqn:Hic; [congruence | simpl; lia]. }
  split.
  - rewrite Hck Huck. lia.
  - rewrite Hck Huck Hlenr. lia.
Qed.

(** [pool_clock_below] read at run granularity (the converse of
    [pool_run_clock_below_to_cell], under the same id bounds). *)
Lemma pool_clock_below_to_run (types : gmap loc type_state) (id : YjsId) :
  (∀ c, c ∈ all_cells types -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (Z.of_nat (clock id) < 2^64)%Z ->
  pool_clock_below types id ->
  pool_run_clock_below (pool_of types) id.
Proof.
  move=> Hckb Hidck Hb r Hr Hcl.
  rewrite all_runs_pool_of in Hr.
  apply list_elem_of_fmap in Hr as (c & -> & Hc).
  have Hck' : (Z.of_nat (clock (item_id (run_head c))) < 2^64)%Z := Hckb c Hc.
  have Hcl' : clientId (item_id (run_head c)) = clientId id := Hcl.
  have Hcc : cell_client c = W64 (clientId id) by rewrite /cell_client Hcl'.
  have [_ Hle] := Hb c Hc Hcc.
  have Hle' : (uint.Z (W64 (clock (item_id (run_head c)))) + Z.of_nat (length (ic_run c))
               <= uint.Z (W64 (clock id)))%Z := Hle.
  change ((clock (item_id (run_head c)) + length (ic_run c) <= clock id)%nat).
  clear Hle Hcl Hb. word.
Qed.

(** [pool_of] / [locs_of] under a registry insert, and the address map's
    flattening: what carries a store step's [<[parent := ...]>] post and the
    freshness of a new node address to the run-granular reading. *)
Lemma pool_of_insert (types : gmap loc type_state) (parent : loc) (ts : type_state) :
  pool_of (<[parent := ts]> types) = <[parent := type_model_of ts]> (pool_of types).
Proof. rewrite /pool_of fmap_insert //. Qed.

Lemma locs_of_insert (types : gmap loc type_state) (parent : loc) (ts : type_state) :
  locs_of (<[parent := ts]> types) = <[parent := ic_loc <$> ty_cells ts]> (locs_of types).
Proof. rewrite /locs_of fmap_insert //. Qed.

(** [registry_lookup_or_create] carried to [(locs, p)]: what projects
    [getOrCreateYType]'s postcondition ([wp_store__getOrCreateYType_runs]).
    A miss inserts the empty type model and the empty address list. *)
Lemma registry_lookup_or_create_to_pool (types types' : gmap loc type_state)
    (bind bind' : gmap P loc) (nm : P) (q : loc) :
  registry_lookup_or_create types bind nm q types' bind' ->
  pool_lookup_or_create (pool_of types) (locs_of types) bind nm q
    (pool_of types') (locs_of types') bind'.
Proof.
  intros [ (Hb & -> & ->) | (Hb & Hfresh & -> & ->) ].
  - left. by split_and!.
  - right. split_and!.
    + exact Hb.
    + rewrite /pool_of lookup_fmap Hfresh //.
    + rewrite pool_of_insert //.
    + rewrite locs_of_insert //.
    + done.
Qed.

Lemma locs_of_concat (types : gmap loc type_state) :
  concat ((map_to_list (locs_of types)).*2) = ic_loc <$> all_cells types.
Proof.
  rewrite /locs_of /all_cells map_to_list_fmap concat_fmap.
  f_equal. rewrite -!list_fmap_compose.
  apply list_fmap_ext. move=> i [k ts] Hl. reflexivity.
Qed.

(** [types_of_locs_pool] round-trips: under matching domains and per-type
    address counts, its [pool_of] is the pool and its [locs_of] is the
    address map. What carries the run-granular pool back to a cell-level
    registry ([own_type_pool_runs_to_cells]). *)
Lemma pool_of_types_of_locs_pool (locs : gmap loc (list loc)) (p : pool) :
  (∀ parent tm, p !! parent = Some tm ->
     ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm)) ->
  pool_of (types_of_locs_pool locs p) = p.
Proof.
  move=> Hlen. apply map_eq => parent.
  rewrite /pool_of /types_of_locs_pool lookup_fmap map_lookup_imap.
  destruct (p !! parent) as [tm|] eqn:Hp; rewrite Hp /=.
  - destruct (Hlen parent tm Hp) as (ls & Hls & Hl).
    rewrite Hls /type_model_of /=.
    rewrite cells_of_locs_runs_run; [| exact Hl].
    destruct tm. done.
  - done.
Qed.

Lemma locs_of_types_of_locs_pool (locs : gmap loc (list loc)) (p : pool) :
  dom locs = dom p ->
  (∀ parent tm, p !! parent = Some tm ->
     ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm)) ->
  locs_of (types_of_locs_pool locs p) = locs.
Proof.
  move=> Hdom Hlen. apply map_eq => parent.
  rewrite /locs_of /types_of_locs_pool lookup_fmap map_lookup_imap.
  destruct (p !! parent) as [tm|] eqn:Hp; rewrite Hp /=.
  - destruct (Hlen parent tm Hp) as (ls & Hls & Hl).
    rewrite Hls /=.
    rewrite cells_of_locs_runs_loc; [| exact Hl].
    done.
  - have Hnd : parent ∉ dom p by apply not_elem_of_dom.
    rewrite -Hdom in Hnd.
    apply not_elem_of_dom in Hnd. rewrite Hnd //.
Qed.

(** The projections are always aligned; [state_runs_of] sections
    [state_of_runs] on aligned states; and on a parent-coherent registry the
    re-materialization is the identity. The three pure legs of the primitive
    [own_store_runs]'s fold/unfold ([own_store_runs_as_state]). *)
Lemma locs_aligned_of (types : gmap loc type_state) :
  locs_aligned (locs_of types) (pool_of types).
Proof.
  split.
  - rewrite /locs_of /pool_of !dom_fmap_L //.
  - move=> parent ls tm.
    rewrite /locs_of /pool_of !lookup_fmap.
    destruct (types !! parent) as [ts|] eqn:Hts; simpl; [| done].
    intros [= <-] [= <-]. rewrite !length_fmap //.
Qed.

Lemma locs_aligned_insert_same_len (locs : gmap loc (list loc)) (p : pool)
    (parent : loc) (tm tm' : type_model) :
  p !! parent = Some tm ->
  length (tm_runs tm') = length (tm_runs tm) ->
  locs_aligned locs p -> locs_aligned locs (<[parent := tm']> p).
Proof.
  move=> Hp Hlen [Hdom Hlens]. split.
  - rewrite dom_insert_L Hdom. symmetry. apply subseteq_union_1_L, singleton_subseteq_l.
    apply elem_of_dom. eauto.
  - move=> q lsq tmq Hq Hpq. destruct (decide (parent = q)) as [<- | Hne].
    + rewrite lookup_insert_eq in Hpq. injection Hpq as <-. rewrite Hlen. exact (Hlens _ _ _ Hq Hp).
    + rewrite lookup_insert_ne in Hpq; last exact Hne. exact (Hlens _ _ _ Hq Hpq).
Qed.

(** Alignment survives replacing one type's address list and model
    together, when the new ones agree on length. *)
Lemma locs_aligned_insert_both (locs : gmap loc (list loc)) (p : pool)
    (parent : loc) (ls' : list loc) (tm' : type_model) :
  length ls' = length (tm_runs tm') ->
  locs_aligned locs p -> locs_aligned (<[parent := ls']> locs) (<[parent := tm']> p).
Proof.
  move=> Hlen [Hdom Hlens]. split.
  - rewrite !dom_insert_L Hdom //.
  - move=> q lsq tmq Hq Hpq. destruct (decide (q = parent)) as [-> | Hne].
    + rewrite lookup_insert_eq in Hq. rewrite lookup_insert_eq in Hpq. simplify_eq/=. exact Hlen.
    + rewrite lookup_insert_ne in Hq; last congruence.
      rewrite lookup_insert_ne in Hpq; last congruence.
      exact (Hlens _ _ _ Hq Hpq).
Qed.

(** An aligned address map has a same-length address list for every type. *)
Lemma locs_aligned_lens (locs : gmap loc (list loc)) (p : pool) :
  locs_aligned locs p ->
  ∀ parent tm, p !! parent = Some tm ->
    ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm).
Proof.
  move=> [Hdom Hlens] parent tm Hp.
  have His : is_Some (locs !! parent).
  { apply elem_of_dom. rewrite Hdom. apply elem_of_dom. by exists tm. }
  destruct His as [ls Hls]. exists ls. split; [done | exact (Hlens parent ls tm Hls Hp)].
Qed.

(** [locs_wf] survives replacing one type's model by one with as many runs
    (a tombstone flip, a per-run update): the address map is untouched. *)
Lemma locs_wf_insert_same_len (locs : gmap loc (list loc)) (p : pool)
    (parent : loc) (tm tm' : type_model) :
  p !! parent = Some tm ->
  length (tm_runs tm') = length (tm_runs tm) ->
  locs_wf locs p -> locs_wf locs (<[parent := tm']> p).
Proof.
  move=> Hp Hlen [Hdom [Hnd Hlens]]. split_and!.
  - rewrite dom_insert_L Hdom. symmetry.
    apply subseteq_union_1_L, singleton_subseteq_l. apply elem_of_dom. by exists tm.
  - exact Hnd.
  - move=> q lsq tmq Hlsq Htmq.
    destruct (decide (q = parent)) as [-> | Hne].
    + rewrite lookup_insert_eq in Htmq. injection Htmq as <-. rewrite Hlen.
      exact (Hlens parent lsq tm Hlsq Hp).
    + rewrite lookup_insert_ne in Htmq; [| congruence]. exact (Hlens q lsq tmq Hlsq Htmq).
Qed.

(** The pool's registry coherence only reads the pool's domain: replacing a
    registered type's model keeps it. *)
Lemma pool_registry_coh_insert_existing (bind : gmap P loc) (p : pool) (parent : loc) (tm tm' : type_model) :
  p !! parent = Some tm ->
  pool_registry_coh bind p -> pool_registry_coh bind (<[parent := tm']> p).
Proof.
  move=> Hp [H1 [H2 H3]]. split_and!; [| exact H2 |].
  - move=> nm q Hq. destruct (decide (q = parent)) as [-> | Hne].
    + rewrite lookup_insert_eq. by eexists.
    + rewrite lookup_insert_ne; [exact (H1 nm q Hq) | congruence].
  - move=> q Hq. destruct (decide (q = parent)) as [-> | Hne].
    + apply H3. by exists tm.
    + rewrite lookup_insert_ne in Hq; [exact (H3 q Hq) | congruence].
Qed.

(** [cells_within_or_from] projects onto [runs_within_or_from] under the
    id no-wrap bounds of the cells and of the inputs. *)
Lemma cells_within_or_from_to_runs (inputs : list (TId * IntegrateInput (A := A)))
    (before after : list item_cell) :
  (∀ c, c ∈ before -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ before -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ after -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ after -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  (∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ inputs ->
     (Z.of_nat (clientId (in_id typedInput.2)) < 2^64)%Z ∧
     (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z) ->
  cells_within_or_from inputs before after ->
  runs_within_or_from inputs (cell_run <$> before) (cell_run <$> after).
Proof.
  move=> Hckb Hclb Hcka Hcla Hinb H r Hr.
  apply list_elem_of_fmap in Hr as (c & -> & Hc).
  have Hzc : uint.Z (cell_clock c) = Z.of_nat (run_clock (cell_run c)).
  { have := Hcka c Hc. rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  have Hzcl : uint.Z (cell_client c) = Z.of_nat (run_client (cell_run c)).
  { have := Hcla c Hc. rewrite /cell_client /run_client /run_head_item /run_head /cell_run /=.
    move=> Hb. word. }
  destruct (H c Hc) as [(c0 & Hc0 & Hcl & Hlo & Hhi) | (ti & Hti & Hcl & Hlo & Hhi)].
  - left. exists (cell_run c0).
    have Hzc0 : uint.Z (cell_clock c0) = Z.of_nat (run_clock (cell_run c0)).
    { have := Hckb c0 Hc0. rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
      move=> Hb. word. }
    have Hzcl0 : uint.Z (cell_client c0) = Z.of_nat (run_client (cell_run c0)).
    { have := Hclb c0 Hc0. rewrite /cell_client /run_client /run_head_item /run_head /cell_run /=.
      move=> Hb. word. }
    split_and!.
    + apply list_elem_of_fmap. eauto.
    + have Hz : uint.Z (cell_client c) = uint.Z (cell_client c0) by rewrite Hcl.
      rewrite Hzcl Hzcl0 in Hz. lia.
    + rewrite Hzc Hzc0 in Hlo. lia.
    + move: Hhi. rewrite Hzc Hzc0 /cell_run /=. lia.
  - right. exists ti.
    have [Hib Hkb] := Hinb ti Hti.
    have Hzk : uint.Z (W64 (clock (in_id ti.2))) = Z.of_nat (clock (in_id ti.2)).
    { have Hlp : (0 <= Z.of_nat (length (in_content ti.2)))%Z by lia. clear -Hkb Hlp. word. }
    split_and!.
    + exact Hti.
    + have Hz : uint.Z (cell_client c) = uint.Z (W64 (clientId (in_id ti.2))) by rewrite Hcl.
      rewrite Hzcl in Hz. move: Hz Hib. word.
    + rewrite Hzc Hzk in Hlo. lia.
    + move: Hhi. rewrite Hzc Hzk /cell_run /=. lia.
Qed.

Lemma state_runs_of_of_runs (str : store_state_runs) :
  locs_aligned (sr_locs str) (sr_pool str) ->
  state_runs_of (state_of_runs str) = str.
Proof.
  move=> [Hdom Hlens].
  have Hprem : ∀ parent tm, sr_pool str !! parent = Some tm ->
      ∃ ls, sr_locs str !! parent = Some ls ∧ length ls = length (tm_runs tm).
  { move=> parent tm Hp.
    have His : is_Some (sr_locs str !! parent).
    { apply elem_of_dom. rewrite Hdom. apply elem_of_dom. by exists tm. }
    destruct His as [ls Hls]. exists ls.
    split; [done | exact (Hlens parent ls tm Hls Hp)]. }
  destruct str. rewrite /state_of_runs /state_runs_of /=.
  f_equal.
  - exact (locs_of_types_of_locs_pool _ _ Hdom Hprem).
  - exact (pool_of_types_of_locs_pool _ _ Hprem).
Qed.

Lemma types_of_locs_pool_of (types : gmap loc type_state) :
  (∀ q ts c, types !! q = Some ts -> c ∈ ty_cells ts -> ic_parent c = q) ->
  types_of_locs_pool (locs_of types) (pool_of types) = types.
Proof.
  move=> Hpar. apply map_eq => parent.
  rewrite /types_of_locs_pool map_lookup_imap /pool_of /locs_of !lookup_fmap.
  destruct (types !! parent) as [ts|] eqn:Hts; simpl; [| done].
  rewrite /type_model_of /=.
  rewrite cells_of_locs_runs_projections.
  - destruct ts. done.
  - move=> c Hc. exact (Hpar parent ts c Hts Hc).
Qed.

(** Materialization of an address map and a pool that agree with
    [(locs0, p0)] away from one type: an insert into [(locs0, p0)]'s
    registry. *)
Lemma types_of_locs_pool_ext_insert (locs locs0 : gmap loc (list loc)) (p p0 : pool)
    (parent : loc) (ls : list loc) (tm : type_model) :
  locs !! parent = Some ls -> p !! parent = Some tm ->
  (∀ q, q ≠ parent -> locs !! q = locs0 !! q) ->
  (∀ q, q ≠ parent -> p !! q = p0 !! q) ->
  types_of_locs_pool locs p
  = <[parent := MkTypeState (cells_of_locs_runs parent ls (tm_runs tm)) (tm_arr tm)]> (types_of_locs_pool locs0 p0).
Proof.
  move=> Hls Hp Hl Hq. apply map_eq => x.
  destruct (decide (x = parent)) as [-> | Hne].
  - rewrite lookup_insert_eq /types_of_locs_pool map_lookup_imap Hp /= Hls //.
  - rewrite lookup_insert_ne; last congruence.
    rewrite /types_of_locs_pool !map_lookup_imap (Hq x Hne) (Hl x Hne) //.
Qed.

(** Materialization across one registry slot. *)
Lemma types_of_locs_pool_insert (locs : gmap loc (list loc)) (p : pool)
    (parent : loc) (ls : list loc) (tm' : type_model) :
  locs !! parent = Some ls ->
  types_of_locs_pool locs (<[parent := tm']> p)
  = <[parent := MkTypeState (cells_of_locs_runs parent ls (tm_runs tm')) (tm_arr tm')]>
      (types_of_locs_pool locs p).
Proof.
  move=> Hls. rewrite /types_of_locs_pool map_imap_insert Hls //.
Qed.

(** Materialization across one registry slot when both the address list
    and the model of that slot change. *)
Lemma types_of_locs_pool_insert_both (locs : gmap loc (list loc)) (p : pool)
    (parent : loc) (ls' : list loc) (tm' : type_model) :
  types_of_locs_pool (<[parent := ls']> locs) (<[parent := tm']> p)
  = <[parent := MkTypeState (cells_of_locs_runs parent ls' (tm_runs tm')) (tm_arr tm')]>
      (types_of_locs_pool locs p).
Proof.
  apply map_eq => q. destruct (decide (q = parent)) as [-> | Hne].
  - rewrite lookup_insert_eq /types_of_locs_pool map_lookup_imap !lookup_insert_eq //.
  - rewrite lookup_insert_ne; last congruence.
    rewrite /types_of_locs_pool !map_lookup_imap.
    rewrite lookup_insert_ne; last congruence.
    rewrite lookup_insert_ne; last congruence.
    done.
Qed.

(** [pool_entries locs p]: the store's nodes as [(address, run)] pairs: every
    run of every registered type zipped with its address, in the registry's
    order ([all_runs p] with the addresses put back). The per-client item
    index ([own_item_map]) is built from it at run granularity. *)
Definition pool_entries (locs : gmap loc (list loc)) (p : pool) : list (loc * ItemRun) :=
  concat ((λ kv, zip (default [] (locs !! kv.1)) (tm_runs kv.2)) <$> map_to_list p).

(** An entry's client and clock in machine words, its (clock, address) key
    and the clock order the item index sorts by; [entry_kp] bundles the
    (client, clock, address) key, the [cell_kp] of the cell the entry
    materializes to. *)
Definition entry_client (e : loc * ItemRun) : w64 := W64 (run_client e.2).
Definition entry_clock (e : loc * ItemRun) : w64 := W64 (run_clock e.2).
Definition entry_pr (e : loc * ItemRun) : Z * loc := (uint.Z (entry_clock e), e.1).
Definition entry_le (a b : loc * ItemRun) : Prop := (uint.Z (entry_clock a) <= uint.Z (entry_clock b))%Z.

#[local] Instance entry_le_dec : RelDecision entry_le.
Proof. rewrite /entry_le. solve_decision. Defined.
#[local] Instance entry_le_trans : Transitive entry_le.
Proof. rewrite /entry_le. move=> x y z. lia. Qed.
#[local] Instance entry_le_total : Total entry_le.
Proof. rewrite /entry_le. move=> x y. lia. Qed.

Definition entry_kp (e : loc * ItemRun) : w64 * (Z * loc) := (entry_client e, entry_pr e).

(** [kp_clkloc kps]: one client's clock names one address, over a
    (client, clock, address) list: the uniqueness the item index relies on
    ([own_item_map]'s [Hclkloc] clause). *)
Definition kp_clkloc (kps : list (w64 * (Z * loc))) : Prop :=
  ∀ a b, a ∈ kps -> b ∈ kps -> a.1 = b.1 -> a.2.1 = b.2.1 -> a.2.2 = b.2.2.

(** [kp_client_locs client kps]: client [client]'s addresses in clock order
    off a (client, clock, address) list: the item index's backing slice for
    that client. [client_run]'s address sequence is this over
    [cell_kp <$> all_cells types] ([client_run_kp_locs]); the run-granular
    [client_locs] is this over the pool's entries. *)
Definition kp_client_locs (client : w64) (kps : list (w64 * (Z * loc))) : list loc :=
  snd <$> merge_sort pr_le ((filter (λ kp, kp.1 = client) kps).*2).

(** [client_locs locs p client]: the client's clock-sorted node-address
    slice at [(locs, pool)]: [own_item_map]'s backing-slice model, read at
    run granularity. Meets [client_run]'s address sequence at
    [client_locs_of]. *)
Definition client_locs (locs : gmap loc (list loc)) (p : pool) (client : w64) : list loc :=
  kp_client_locs client (entry_kp <$> pool_entries locs p).

(** [client_entries locs p client]: the client's entries in clock order, the
    index's addresses with their runs ([client_locs_entries]); what the
    index walk ([getNodeIndex]) probes. *)
Definition client_entries (locs : gmap loc (list loc)) (p : pool) (client : w64) : list (loc * ItemRun) :=
  merge_sort entry_le (filter (λ e, entry_client e = client) (pool_entries locs p)).

(** [sorted_client_entries locs p client E]: [E] lists entries of client
    [client] from the pool [(locs, p)], clock-sorted and without a repeated
    address: the index's entries for [client] ([client_entries]), or those
    with one run rewritten during a split. What the index walk
    ([wp_getNodeIndex_runs]) searches. *)
Definition sorted_client_entries (locs : gmap loc (list loc)) (p : pool) (client : w64)
    (E : list (loc * ItemRun)) : Prop :=
  StronglySorted entry_le E ∧ NoDup E.*1 ∧
  (∀ e, e ∈ E -> e ∈ pool_entries locs p ∧ entry_client e = client).

(** [client_run] projects onto [client_runs]: the [merge_sort cell_le] run
    list, mapped through [cell_run], is the [merge_sort run_le] of the
    projected pool. Needs the id no-wrap bounds (so the [w64] and [nat]
    clock orders agree), nonempty runs, range disjointness and the address
    [NoDup] (so same-client clocks are unique and sortedness pins the list). *)
Lemma client_run_runs (types : gmap loc type_state) (client : w64) :
  (∀ c, c ∈ all_cells types -> (Z.of_nat (run_clock (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells types -> (Z.of_nat (run_client (cell_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells types -> ic_run c ≠ []) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  cell_run <$> client_run types client = client_runs (pool_of types) (uint.nat client).
Proof.
  move=> Hckb Hclb Hne Hnd Hdisj.
  rewrite /client_runs all_runs_pool_of list_filter_fmap /client_run.
  set (P1 := λ c : item_cell, cell_client c = client).
  set (P2 := λ c : item_cell, run_client (cell_run c) = uint.nat client).
  have Hpq : ∀ c, c ∈ all_cells types -> (P1 c ↔ P2 c).
  { move=> c Hc. rewrite /P1 /P2 cell_client_run.
    have Hb := Hclb c Hc. split; move=> H; word. }
  have -> : filter P2 (all_cells types) = filter P1 (all_cells types).
  { apply list_filter_iff_elem_of. move=> c Hc. symmetry. by apply Hpq. }
  set (F := filter P1 (all_cells types)).
  have HFsub : ∀ c, c ∈ F -> c ∈ all_cells types.
  { move=> c Hc. apply list_elem_of_filter in Hc. tauto. }
  apply (StronglySorted_unique_strong run_le).
  - (* same clock, same client, disjoint ranges, nonempty runs -> same cell *)
    move=> r1 r2 Hr1 Hr2 H12 H21.
    apply list_elem_of_fmap in Hr1 as (c1 & -> & Hc1).
    rewrite merge_sort_Permutation in Hc1.
    rewrite merge_sort_Permutation in Hr2.
    apply list_elem_of_fmap in Hr2 as (c2 & -> & Hc2).
    have Hm1 : c1 ∈ all_cells types := HFsub c1 Hc1.
    have Hm2 : c2 ∈ all_cells types := HFsub c2 Hc2.
    have Hcl : cell_client c1 = cell_client c2.
    { apply list_elem_of_filter in Hc1. apply list_elem_of_filter in Hc2.
      rewrite /P1 in Hc1 Hc2. destruct Hc1 as [-> _]. destruct Hc2 as [-> _]. done. }
    have Hck : run_clock (cell_run c1) = run_clock (cell_run c2).
    { rewrite /run_le in H12 H21. lia. }
    have Hloc : ic_loc c1 = ic_loc c2.
    { destruct (decide (ic_loc c1 = ic_loc c2)) as [| Hnee]; [done |].
      have Hd := Hdisj c1 c2 Hm1 Hm2 Hcl Hnee.
      have Hlen1 : (1 <= length (ic_run c1))%nat
        by (destruct (ic_run c1) eqn:E; [exfalso; exact (Hne c1 Hm1 E) | simpl; lia]).
      have Hlen2 : (1 <= length (ic_run c2))%nat
        by (destruct (ic_run c2) eqn:E; [exfalso; exact (Hne c2 Hm2 E) | simpl; lia]).
      have Hz1 : uint.Z (cell_clock c1) = Z.of_nat (run_clock (cell_run c1)).
      { have := Hckb c1 Hm1. rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
        move=> Hb. word. }
      have Hz2 : uint.Z (cell_clock c2) = Z.of_nat (run_clock (cell_run c2)).
      { have := Hckb c2 Hm2. rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
        move=> Hb. word. }
      move: Hd. rewrite Hz1 Hz2 Hck /cell_run /=. lia. }
    f_equal.
    destruct (list_elem_of_lookup_1 _ _ Hm1) as (i1 & Hi1).
    destruct (list_elem_of_lookup_1 _ _ Hm2) as (i2 & Hi2).
    have Hll1 : (ic_loc <$> all_cells types) !! i1 = Some (ic_loc c2)
      by rewrite list_lookup_fmap Hi1 /= Hloc.
    have Hll2 : (ic_loc <$> all_cells types) !! i2 = Some (ic_loc c2)
      by rewrite list_lookup_fmap Hi2.
    have Heqi : i1 = i2 := NoDup_lookup _ _ _ _ Hnd Hll1 Hll2.
    rewrite Heqi Hi2 in Hi1. by simplify_eq.
  - apply (StronglySorted_fmap_elem_of cell_le run_le).
    + move=> x y Hx Hy Hxy.
      rewrite merge_sort_Permutation in Hx. rewrite merge_sort_Permutation in Hy.
      have Hmx : x ∈ all_cells types := HFsub x Hx.
      have Hmy : y ∈ all_cells types := HFsub y Hy.
      move: Hxy. rewrite /cell_le /run_le.
      have Hzx : uint.Z (cell_clock x) = Z.of_nat (run_clock (cell_run x)).
      { have := Hckb x Hmx. rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
        move=> Hb. word. }
      have Hzy : uint.Z (cell_clock y) = Z.of_nat (run_clock (cell_run y)).
      { have := Hckb y Hmy. rewrite /cell_clock /run_clock /run_head_item /run_head /cell_run /=.
        move=> Hb. word. }
      rewrite Hzx Hzy. lia.
    + apply (StronglySorted_merge_sort cell_le).
  - apply (StronglySorted_merge_sort run_le).
  - rewrite !merge_sort_Permutation //.
Qed.


(** The spliced cell list is the old one plus the new cell, as a multiset. *)
Lemma integrate_splice_perm (cells : list item_cell) (arr : list (YjsItem A))
    (item_l : loc) (run : list (YjsItem A)) (parent : loc)
    (cells' : list item_cell) (arr' : list (YjsItem A)) :
  integrate_splice cells arr item_l run parent cells' arr' ->
  cells' ≡ₚ cells ++ [MkItemCell item_l run false parent].
Proof.
  move=> [idx [Hidx [_ [-> _]]]].
  have -> : cells ++ [MkItemCell item_l run false parent]
          = take idx cells ++ (drop idx cells ++ [MkItemCell item_l run false parent])
    by rewrite app_assoc take_drop.
  apply Permutation_app_head. apply Permutation_cons_append.
Qed.

(** The new cell sits at its splice index. *)
Lemma integrate_splice_lookup (cells : list item_cell)
    (item_l : loc) (run : list (YjsItem A)) (parent : loc)
    (cells' : list item_cell) (idx : nat) :
  (idx <= length cells)%nat ->
  cells' = take idx cells ++ MkItemCell item_l run false parent :: drop idx cells ->
  cells' !! idx = Some (MkItemCell item_l run false parent).
Proof.
  move=> Hidx ->. rewrite lookup_app_r; last (rewrite length_take; lia).
  rewrite length_take_le; last exact Hidx. rewrite Nat.sub_diag //.
Qed.

(** A one-char input lands as exactly the item it resolves to: the run has
    one char, whose id is the new item's, and ids are unique in the valid
    result ([id_unique]). *)
Lemma integrate_unit_run (arr arr' : list (YjsItem A)) (input : IntegrateInput (A := A))
    (newItem : YjsItem A) (run : list (YjsItem A)) :
  YjsArrInvariant arr ->
  integrate_ready arr input newItem ->
  integrate input arr = Some arr' ->
  YjsArrInvariant arr' ->
  run_denotes input newItem run ->
  length (in_content input) = 1%nat ->
  (∀ x, x ∈ run -> x ∈ arr') ->
  run = [newItem].
Proof.
  move=> Hinv [Htoitem [Hvalid Hmax]] Hintegrate Hinv' [Hid [_ [_ Hlen]]] Hlen1 Hsub.
  rewrite Hlen1 in Hlen.
  destruct run as [| x [| y tl]]; simpl in Hlen; [done | | done].
  have Hxin : x ∈ arr' := Hsub x (list_elem_of_here x []).
  have HnewIn : newItem ∈ arr'.
  { destruct (YjsArrInvariant_integrate input arr arr' newItem Hinv Htoitem Hvalid Hmax Hintegrate)
      as [i [Hile' [Harr'eq _]]].
    rewrite Harr'eq. apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile')). left. reflexivity. }
  have Hidnew : item_id newItem = in_id input := commutativity.toItem_id input arr newItem Htoitem.
  f_equal.
  apply (id_unique (ArrSet arr') (yai_item_set_inv _ Hinv') x newItem);
    [simpl in Hid; rewrite Hid Hidnew // | exact Hxin | exact HnewIn].
Qed.

(** Replacing a registered type's state keeps the registry coherent: the
    pool's domain is unchanged. *)
Lemma registry_coh_insert (bind : gmap P loc) (types : gmap loc type_state)
    (p : loc) (ts ts' : type_state) :
  types !! p = Some ts ->
  registry_coh bind types ->
  registry_coh bind (<[p := ts']> types).
Proof.
  move=> Hp [Hbt [Hinj Htb]]. split_and!.
  - move=> nm q Hq. destruct (decide (q = p)) as [-> | Hne].
    + rewrite lookup_insert_eq. by eexists.
    + rewrite lookup_insert_ne //. exact (Hbt nm q Hq).
  - exact Hinj.
  - move=> q [ts0 Hq]. destruct (decide (q = p)) as [-> | Hne].
    + exact (Htb p (ex_intro _ ts Hp)).
    + rewrite lookup_insert_ne in Hq; last done. exact (Htb q (ex_intro _ ts0 Hq)).
Qed.

(** Pool membership, decomposed to the owning type. *)
Lemma all_cells_elem_of (types : gmap loc type_state) (c : item_cell) :
  c ∈ all_cells types <-> ∃ p ts, types !! p = Some ts /\ c ∈ ty_cells ts.
Proof.
  rewrite /all_cells list_elem_of_concat.
  split.
  - move=> [l [Hcl Hl]].
    apply list_elem_of_fmap in Hl. destruct Hl as (ts & -> & Hts).
    apply list_elem_of_fmap in Hts. destruct Hts as ([p ts'] & -> & Hpts).
    simpl in *. exists p, ts'. split; [| exact Hcl].
    by apply elem_of_map_to_list.
  - move=> [p [ts [Hp Hcts]]].
    exists (ty_cells ts). split; [exact Hcts |].
    apply list_elem_of_fmap. exists ts. split; [done |].
    apply list_elem_of_fmap. exists (p, ts). split; [done |].
    by apply elem_of_map_to_list.
Qed.

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

(** Under the address [NoDup], a location determines its slot: two cells at
    the same address sit in the same type at the same index (what turns the
    loc-identified clauses of the step records into index facts). *)
Lemma all_cells_same_loc_same_slot (types : gmap loc type_state)
    (q1 q2 : loc) (ts1 ts2 : type_state) (k1 k2 : nat) (c1 c2 : item_cell) :
  NoDup (ic_loc <$> all_cells types) ->
  types !! q1 = Some ts1 -> ty_cells ts1 !! k1 = Some c1 ->
  types !! q2 = Some ts2 -> ty_cells ts2 !! k2 = Some c2 ->
  ic_loc c1 = ic_loc c2 ->
  q1 = q2 ∧ k1 = k2 ∧ c1 = c2.
Proof.
  move=> Hnd Hq1 Hk1 Hq2 Hk2 Hloc.
  have Hqq : q1 = q2.
  { destruct (decide (q1 = q2)) as [| Hne]; [done | exfalso].
    have Hperm := all_cells_lookup types q1 ts1 Hq1.
    have Hnd2 : NoDup (ic_loc <$> (ty_cells ts1 ++ all_cells (delete q1 types))).
    { by rewrite -Hperm. }
    rewrite fmap_app in Hnd2. apply NoDup_app in Hnd2.
    destruct Hnd2 as (_ & Hdisj & _).
    apply (Hdisj (ic_loc c1)).
    - apply list_elem_of_fmap_2. exact (list_elem_of_lookup_2 _ _ _ Hk1).
    - rewrite Hloc. apply list_elem_of_fmap_2.
      apply all_cells_elem_of. exists q2, ts2.
      rewrite lookup_delete_ne; last congruence.
      split; [exact Hq2 | exact (list_elem_of_lookup_2 _ _ _ Hk2)]. }
  subst q2. have Hts : ts2 = ts1 by congruence. subst ts2.
  have Hperm := all_cells_lookup types q1 ts1 Hq1.
  have Hnd2 : NoDup (ic_loc <$> (ty_cells ts1 ++ all_cells (delete q1 types))).
  { by rewrite -Hperm. }
  rewrite fmap_app in Hnd2. apply NoDup_app in Hnd2.
  destruct Hnd2 as (Hnd1 & _ & _).
  have Hl1 : (ic_loc <$> ty_cells ts1) !! k1 = Some (ic_loc c2)
    by rewrite list_lookup_fmap Hk1 /= Hloc.
  have Hl2 : (ic_loc <$> ty_cells ts1) !! k2 = Some (ic_loc c2)
    by rewrite list_lookup_fmap Hk2.
  have Hkk : k1 = k2 := NoDup_lookup _ _ _ _ Hnd1 Hl1 Hl2.
  subst k2. have Hc : c2 = c1 by congruence. subst c2. done.
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

(** The pool invariants only look at the cells as a multiset: they transport
    along any permutation of [all_cells]. *)
Lemma pool_invs_perm (types types' : gmap loc type_state) :
  all_cells types' ≡ₚ all_cells types ->
  pool_invs types -> pool_invs types'.
Proof.
  move=> Hperm [Hfits [Hnodup [Hdisj Horigin]]]. split_and!.
  - move=> c Hc. rewrite Hperm in Hc. exact (Hfits c Hc).
  - rewrite Hperm //.
  - move=> c1 c2 Hc1 Hc2. rewrite Hperm in Hc1 Hc2. exact (Hdisj c1 c2 Hc1 Hc2).
  - move=> c Hc. rewrite Hperm in Hc. exact (Horigin c Hc).
Qed.

(** Registering a fresh EMPTY type adds no cell. *)
Lemma pool_invs_insert_empty (types : gmap loc type_state) (p : loc) :
  types !! p = None ->
  pool_invs types -> pool_invs (<[p := MkTypeState [] []]> types).
Proof. move=> Hp. apply pool_invs_perm. exact (all_cells_insert_empty types p [] Hp). Qed.

(** Registering a fresh name at a fresh type keeps the registry coherent. *)
Lemma registry_coh_bind_fresh (bind : gmap P loc) (types : gmap loc type_state)
    (nm : P) (p : loc) (ts : type_state) :
  bind !! nm = None ->
  types !! p = None ->
  registry_coh bind types ->
  registry_coh (<[nm := p]> bind) (<[p := ts]> types).
Proof.
  move=> Hnm Hp [Hbt [Hinj Htb]].
  have Hpnotbound : ∀ name, bind !! name = Some p -> False.
  { move=> name Hb. destruct (Hbt name p Hb) as [ts0 Hts0]. rewrite Hp in Hts0. done. }
  split_and!.
  - move=> name q. destruct (decide (name = nm)) as [-> | Hne].
    + rewrite lookup_insert_eq. move=> [= <-]. rewrite lookup_insert_eq. by eexists.
    + rewrite lookup_insert_ne //. move=> Hb.
      destruct (decide (q = p)) as [-> | Hnep]; first by (exfalso; exact (Hpnotbound name Hb)).
      rewrite lookup_insert_ne //. exact (Hbt name q Hb).
  - move=> n1 n2 q H1 H2.
    destruct (decide (n1 = nm)) as [-> | Hn1]; destruct (decide (n2 = nm)) as [-> | Hn2].
    + done.
    + exfalso. rewrite lookup_insert_eq in H1. rewrite lookup_insert_ne // in H2.
      injection H1 as <-. exact (Hpnotbound n2 H2).
    + exfalso. rewrite lookup_insert_ne // in H1. rewrite lookup_insert_eq in H2.
      injection H2 as <-. exact (Hpnotbound n1 H1).
    + rewrite lookup_insert_ne // in H1. rewrite lookup_insert_ne // in H2.
      exact (Hinj n1 n2 q H1 H2).
  - move=> q. destruct (decide (q = p)) as [-> | Hnep].
    + move=> _. exists nm. by rewrite lookup_insert_eq.
    + rewrite lookup_insert_ne //. move=> Hs.
      destruct (Htb q Hs) as [name Hb]. exists name.
      rewrite lookup_insert_ne //. move=> ?; subst name. by rewrite Hnm in Hb.
Qed.

(** A step that keeps the pool's domain keeps the registry coherent. *)
(** A coherent registry's type domain grows with its bindings. *)
Lemma registry_coh_dom_mono (bind bind' : gmap P loc) (types types' : gmap loc type_state) :
  registry_coh bind types -> registry_coh bind' types' -> bind ⊆ bind' ->
  dom types ⊆ dom types'.
Proof.
  move=> [_ [_ Htb]] [Hbt' _] Hsub p. rewrite !elem_of_dom. move=> Hp.
  destruct (Htb p Hp) as [nm Hnm]. exact (Hbt' nm p (lookup_weaken _ _ _ _ Hnm Hsub)).
Qed.

Lemma registry_coh_dom_eq (bind : gmap P loc) (types types' : gmap loc type_state) :
  (∀ p, is_Some (types !! p) -> is_Some (types' !! p)) ->
  (∀ p, is_Some (types' !! p) -> is_Some (types !! p)) ->
  registry_coh bind types -> registry_coh bind types'.
Proof.
  move=> Hfwd Hbwd [Hbt [Hinj Htb]]. split_and!.
  - move=> nm q Hq. exact (Hfwd q (Hbt nm q Hq)).
  - exact Hinj.
  - move=> q Hq. exact (Htb q (Hbwd q Hq)).
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

(** The pool invariants survive one integrate: a fresh node holding a run
    that fits, starting above every same-client cell, whose head's same-client
    origin is older, spliced into one type. *)
Lemma pool_invs_integrate (types : gmap loc type_state) (parent : loc)
    (cells arr cells' arr' : list _) (c : item_cell) :
  pool_invs types ->
  types !! parent = Some (MkTypeState cells arr) ->
  cells' ≡ₚ cells ++ [c] ->
  ic_loc c ∉ ic_loc <$> all_cells types ->
  cell_fits c ->
  pool_clock_below types (item_id (run_head c)) ->
  cell_origin_clk c ->
  pool_invs (<[parent := MkTypeState cells' arr']> types).
Proof.
  move=> [Hfits [Hnodup [Hdisj Horig]]] Hp Hperm Hfresh Hfc Hbelow Hoc.
  have Hac := all_cells_insert_snoc types parent cells arr cells' arr' c Hp Hperm.
  split_and!.
  - exact (fits_snoc _ _ c Hac Hfc Hfits).
  - exact (nodup_locs_snoc _ _ c Hac Hfresh Hnodup).
  - apply (rangedisj_snoc _ _ c Hac); [| exact Hdisj].
    move=> c0 Hc0 Hcc. exact (proj2 (Hbelow c0 Hc0 Hcc)).
  - exact (originclk_snoc _ _ c Hac Hoc Horig).
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

(** [kp_client_locs] only sees the (client, clock, address) multiset: under
    [kp_clkloc] a permutation sorts to the same addresses, a key of another
    client leaves the slice alone, a client absent from the keys has the
    empty slice, a key at the client's newest clock lands
    at the tail (the [addNode] step), and a key strictly between the sorted
    clocks lands at that position (the split step). *)
Lemma kp_client_locs_perm (client : w64) (kps1 kps2 : list (w64 * (Z * loc))) :
  kp_clkloc kps1 -> kps1 ≡ₚ kps2 ->
  kp_client_locs client kps1 = kp_client_locs client kps2.
Proof.
  move=> Hkd Hperm. rewrite /kp_client_locs. f_equal.
  apply (StronglySorted_unique_strong pr_le).
  - move=> p1 p2 Hp1 Hp2 H12 H21.
    rewrite merge_sort_Permutation in Hp1. rewrite merge_sort_Permutation in Hp2.
    apply list_elem_of_fmap in Hp1 as (a & -> & Ha).
    apply list_elem_of_fmap in Hp2 as (b & -> & Hb).
    apply list_elem_of_filter in Ha as [Hac Ha].
    apply list_elem_of_filter in Hb as [Hbc Hb].
    rewrite -Hperm in Hb.
    rewrite /pr_le in H12 H21.
    have Hkeq : a.2.1 = b.2.1 by lia.
    have Hloc := Hkd a b Ha Hb ltac:(congruence) Hkeq.
    destruct a as [ac [aclk al]], b as [bc [bclk bl]]; simpl in *. by subst.
  - apply (StronglySorted_merge_sort pr_le).
  - apply (StronglySorted_merge_sort pr_le).
  - rewrite !merge_sort_Permutation. apply Permutation_map. by rewrite Hperm.
Qed.

Lemma kp_client_locs_other (client : w64) (kps : list (w64 * (Z * loc))) (kp : w64 * (Z * loc)) :
  kp.1 ≠ client -> kp_client_locs client (kps ++ [kp]) = kp_client_locs client kps.
Proof.
  move=> Hne. rewrite /kp_client_locs filter_app filter_cons_False // filter_nil app_nil_r //.
Qed.

Lemma kp_client_locs_absent (client : w64) (kps : list (w64 * (Z * loc))) :
  client ∉ kps.*1 -> kp_client_locs client kps = [].
Proof.
  move=> Hnin.
  have Hfilt : filter (λ kp : w64 * (Z * loc), kp.1 = client) kps = [].
  { move: Hnin. elim: kps => [| a l IH] Hnin; [reflexivity |].
    rewrite filter_cons. case_decide as Hc.
    - exfalso. apply Hnin. rewrite fmap_cons Hc. apply list_elem_of_here.
    - apply IH. move=> Hin. apply Hnin. rewrite fmap_cons. apply elem_of_cons. by right. }
  rewrite /kp_client_locs Hfilt //.
Qed.

Lemma kp_client_locs_snoc_max (client : w64) (kps : list (w64 * (Z * loc))) (kp : w64 * (Z * loc)) :
  kp_clkloc kps -> kp.1 = client ->
  (∀ a, a ∈ kps -> a.1 = client -> (a.2.1 < kp.2.1)%Z) ->
  kp_client_locs client (kps ++ [kp]) = kp_client_locs client kps ++ [kp.2.2].
Proof.
  move=> Hkd Hkc Hmax. rewrite /kp_client_locs.
  rewrite filter_app filter_cons_True // filter_nil fmap_app /=.
  set prs := (filter (λ kp0, kp0.1 = client) kps).*2.
  have Hprs : ∀ a, a ∈ prs -> ∃ b, b ∈ kps ∧ b.1 = client ∧ a = b.2.
  { move=> a Ha. apply list_elem_of_fmap in Ha as (b & -> & Hb).
    apply list_elem_of_filter in Hb as [Hbc Hb]. by exists b. }
  have Hmaxp : ∀ a, a ∈ prs -> (a.1 < kp.2.1)%Z.
  { move=> a Ha. destruct (Hprs a Ha) as (b & Hb & Hbc & ->). exact (Hmax b Hb Hbc). }
  have Hkdp : ∀ a b, a ∈ prs -> b ∈ prs -> a.1 = b.1 -> a = b.
  { move=> a b Ha Hb Hab.
    destruct (Hprs a Ha) as (a' & Ha' & Hac & ->).
    destruct (Hprs b Hb) as (b' & Hb' & Hbc & ->).
    have Hloc := Hkd a' b' Ha' Hb' ltac:(congruence) Hab.
    destruct a' as [ac [aclk al]], b' as [bc [bclk bl]]; simpl in *. by subst. }
  change [kp.2.2] with (snd <$> [kp.2]). rewrite -fmap_app. f_equal.
  apply (StronglySorted_unique_strong pr_le).
  - move=> p1 p2 Hp1 Hp2 H12 H21.
    rewrite merge_sort_Permutation in Hp1.
    rewrite /pr_le in H12 H21.
    have Hkeq : p1.1 = p2.1 by lia.
    apply elem_of_app in Hp1 as [Hp1 | Hp1]; apply elem_of_app in Hp2 as [Hp2 | Hp2].
    + rewrite merge_sort_Permutation in Hp2. exact (Hkdp p1 p2 Hp1 Hp2 Hkeq).
    + apply list_elem_of_singleton in Hp2 as ->. exfalso. have := Hmaxp p1 Hp1. lia.
    + apply list_elem_of_singleton in Hp1 as ->. rewrite merge_sort_Permutation in Hp2.
      exfalso. have := Hmaxp p2 Hp2. lia.
    + apply list_elem_of_singleton in Hp1 as ->. apply list_elem_of_singleton in Hp2 as ->. reflexivity.
  - apply (StronglySorted_merge_sort pr_le).
  - apply StronglySorted_app_2.
    + move=> a z Ha Hz. apply list_elem_of_singleton in Hz as ->.
      rewrite merge_sort_Permutation in Ha. rewrite /pr_le. have := Hmaxp a Ha. lia.
    + apply (StronglySorted_merge_sort pr_le).
    + repeat constructor.
  - rewrite merge_sort_Permutation. apply Permutation_app; [| reflexivity]. symmetry. apply merge_sort_Permutation.
Qed.

Lemma kp_client_locs_insert (client : w64) (kps : list (w64 * (Z * loc))) (kp : w64 * (Z * loc)) (i : nat) :
  kp_clkloc kps -> kp.1 = client ->
  (∀ a, a ∈ take i (merge_sort pr_le ((filter (λ kp0, kp0.1 = client) kps).*2)) -> (a.1 < kp.2.1)%Z) ->
  (∀ a, a ∈ drop i (merge_sort pr_le ((filter (λ kp0, kp0.1 = client) kps).*2)) -> (kp.2.1 < a.1)%Z) ->
  kp_client_locs client (kps ++ [kp])
  = take i (kp_client_locs client kps) ++ kp.2.2 :: drop i (kp_client_locs client kps).
Proof.
  move=> Hkd Hkc Hbef Haft. rewrite /kp_client_locs.
  rewrite filter_app filter_cons_True // filter_nil fmap_app /=.
  set prs := (filter (λ kp0, kp0.1 = client) kps).*2.
  set S := merge_sort pr_le prs.
  have Hprs : ∀ a, a ∈ prs -> ∃ b, b ∈ kps ∧ b.1 = client ∧ a = b.2.
  { move=> a Ha. apply list_elem_of_fmap in Ha as (b & -> & Hb).
    apply list_elem_of_filter in Hb as [Hbc Hb]. by exists b. }
  have Hkdp : ∀ a b, a ∈ prs -> b ∈ prs -> a.1 = b.1 -> a = b.
  { move=> a b Ha Hb Hab.
    destruct (Hprs a Ha) as (a' & Ha' & Hac & ->).
    destruct (Hprs b Hb) as (b' & Hb' & Hbc & ->).
    have Hloc := Hkd a' b' Ha' Hb' ltac:(congruence) Hab.
    destruct a' as [ac [aclk al]], b' as [bc [bclk bl]]; simpl in *. by subst. }
  have HSperm : S ≡ₚ prs := merge_sort_Permutation pr_le prs.
  have HinS_take : ∀ z, z ∈ take i S -> z ∈ S.
  { move=> z Hz. rewrite -(take_drop i S). apply elem_of_app. by left. }
  have HinS_drop : ∀ z, z ∈ drop i S -> z ∈ S.
  { move=> z Hz. rewrite -(take_drop i S). apply elem_of_app. by right. }
  have HSS : StronglySorted pr_le S by apply (StronglySorted_merge_sort pr_le).
  have HSSapp : StronglySorted pr_le (take i S ++ drop i S).
  { rewrite (take_drop i S). exact HSS. }
  rewrite -fmap_take -fmap_drop.
  change (kp.2.2 :: (snd <$> drop i S)) with (snd <$> (kp.2 :: drop i S)).
  rewrite -fmap_app. f_equal.
  apply (StronglySorted_unique_strong pr_le).
  - move=> p1 p2 Hp1 Hp2 H12 H21.
    rewrite /pr_le in H12 H21.
    have Hkeq : p1.1 = p2.1 by lia.
    rewrite merge_sort_Permutation in Hp1.
    have Hp2c : (p2 ∈ S) ∨ p2 = kp.2.
    { apply elem_of_app in Hp2 as [Hp2 | Hp2]; [left; exact (HinS_take p2 Hp2) |].
      apply elem_of_cons in Hp2 as [-> | Hp2]; [by right | left; exact (HinS_drop p2 Hp2)]. }
    apply elem_of_app in Hp1 as [Hp1 | Hp1]; last apply list_elem_of_singleton in Hp1 as ->.
    + destruct Hp2c as [Hp2S | ->].
      * apply Hkdp; [exact Hp1 | by rewrite -HSperm | exact Hkeq].
      * exfalso. rewrite -HSperm -(take_drop i S) in Hp1. apply elem_of_app in Hp1 as [Ht | Hd].
        -- have := Hbef p1 Ht. lia.
        -- have := Haft p1 Hd. lia.
    + destruct Hp2c as [Hp2S | ->]; [| reflexivity].
      exfalso. rewrite -(take_drop i S) in Hp2S. apply elem_of_app in Hp2S as [Ht | Hd].
      * have := Hbef p2 Ht. lia.
      * have := Haft p2 Hd. lia.
  - apply (StronglySorted_merge_sort pr_le).
  - apply StronglySorted_app_2.
    + move=> a c Ha Hc. apply elem_of_cons in Hc as [-> | Hc].
      * rewrite /pr_le. have := Hbef a Ha. lia.
      * rewrite /pr_le. have := Hbef a Ha. have := Haft c Hc. lia.
    + exact (StronglySorted_app_1_l _ _ _ HSSapp).
    + change (kp.2 :: drop i S) with ([kp.2] ++ drop i S).
      apply StronglySorted_app_2.
      * move=> a c Ha Hc. apply list_elem_of_singleton in Ha as ->. rewrite /pr_le. have := Haft c Hc. lia.
      * repeat constructor.
      * exact (StronglySorted_app_1_r _ _ _ HSSapp).
  - rewrite merge_sort_Permutation. rewrite -HSperm -{1}(take_drop i S).
    change (kp.2 :: drop i S) with ([kp.2] ++ drop i S).
    rewrite -app_assoc. apply Permutation_app; [reflexivity |]. apply Permutation_app_comm.
Qed.

(** [kp_clkloc] over a registry's keys is [own_item_map]'s [Hclkloc]
    clause, and [client_run]'s address sequence is [kp_client_locs] over
    those keys. *)
Lemma kp_clkloc_cells (types : gmap loc type_state) :
  kp_clkloc (cell_kp <$> all_cells types) <->
  (∀ c1 c2, c1 ∈ all_cells types → c2 ∈ all_cells types →
     cell_client c1 = cell_client c2 → (cell_pr c1).1 = (cell_pr c2).1 → ic_loc c1 = ic_loc c2).
Proof.
  split.
  - move=> Hkd c1 c2 Hc1 Hc2 Hcc Hpr.
    exact (Hkd (cell_kp c1) (cell_kp c2) (list_elem_of_fmap_2 _ _ _ Hc1) (list_elem_of_fmap_2 _ _ _ Hc2) Hcc Hpr).
  - move=> Hkd a b Ha Hb Hab Hpr.
    apply list_elem_of_fmap in Ha as (c1 & -> & Hc1). apply list_elem_of_fmap in Hb as (c2 & -> & Hc2).
    exact (Hkd c1 c2 Hc1 Hc2 Hab Hpr).
Qed.

Lemma client_run_kp_locs (types : gmap loc type_state) (client : w64) :
  kp_clkloc (cell_kp <$> all_cells types) ->
  ic_loc <$> client_run types client = kp_client_locs client (cell_kp <$> all_cells types).
Proof.
  move=> Hkd. rewrite /client_run /kp_client_locs ic_loc_fmap_pr -cell_pr_filter_kp. f_equal.
  apply (StronglySorted_unique_strong pr_le).
  - move=> p1 p2 Hp1 Hp2 H12 H21.
    rewrite (merge_sort_Permutation cell_le) in Hp1.
    rewrite (merge_sort_Permutation pr_le) in Hp2.
    apply list_elem_of_fmap in Hp1 as (x1 & -> & Hx1).
    apply list_elem_of_fmap in Hp2 as (x2 & -> & Hx2).
    apply list_elem_of_filter in Hx1 as [Hc1 Hx1]. apply list_elem_of_filter in Hx2 as [Hc2 Hx2].
    rewrite /pr_le in H12 H21.
    have Hkeq : (cell_pr x1).1 = (cell_pr x2).1 by lia.
    have Hloc := proj1 (kp_clkloc_cells types) Hkd x1 x2 Hx1 Hx2 ltac:(congruence) Hkeq.
    rewrite /cell_pr. f_equal; assumption.
  - apply SS_cell_pr_merge.
  - apply (StronglySorted_merge_sort pr_le).
  - rewrite (merge_sort_Permutation pr_le). apply Permutation_map. apply merge_sort_Permutation.
Qed.

(** The entries of a cell registry's own addresses and runs are its cells'
    addresses and runs, so their keys are the cells' [cell_kp]; and a
    run-granular state's entries are those of the registry it materializes
    to. *)
Lemma entry_kp_cell (c : item_cell) : entry_kp (ic_loc c, cell_run c) = cell_kp c.
Proof. reflexivity. Qed.

Lemma pool_entries_of (types : gmap loc type_state) :
  pool_entries (locs_of types) (pool_of types) = (λ c, (ic_loc c, cell_run c)) <$> all_cells types.
Proof.
  rewrite /pool_entries /all_cells /pool_of map_to_list_fmap fmap_concat -!list_fmap_compose.
  f_equal. apply list_fmap_ext => i kv Hkv.
  have Hlk : types !! kv.1 = Some kv.2.
  { apply elem_of_map_to_list. destruct kv. exact (list_elem_of_lookup_2 _ _ _ Hkv). }
  rewrite /= /locs_of lookup_fmap Hlk /= zip_with_fmap_l zip_with_fmap_r zip_with_diag //.
Qed.

Lemma entries_kp_of (types : gmap loc type_state) :
  entry_kp <$> pool_entries (locs_of types) (pool_of types) = cell_kp <$> all_cells types.
Proof. rewrite pool_entries_of -list_fmap_compose. apply list_fmap_ext => i c _. reflexivity. Qed.

Lemma entries_kp_to_cells (locs : gmap loc (list loc)) (p : pool) :
  dom locs = dom p ->
  (∀ parent tm, p !! parent = Some tm ->
     ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm)) ->
  entry_kp <$> pool_entries locs p = cell_kp <$> all_cells (types_of_locs_pool locs p).
Proof.
  move=> Hdom Hlens. rewrite -entries_kp_of.
  rewrite (locs_of_types_of_locs_pool locs p Hdom Hlens) (pool_of_types_of_locs_pool locs p Hlens) //.
Qed.

(** The run-granular index over a cell registry's own addresses and runs is
    [client_run]'s address sequence. *)
Lemma client_locs_of (types : gmap loc type_state) (client : w64) :
  kp_clkloc (cell_kp <$> all_cells types) ->
  client_locs (locs_of types) (pool_of types) client = ic_loc <$> client_run types client.
Proof. move=> Hkd. rewrite /client_locs entries_kp_of (client_run_kp_locs types client Hkd) //. Qed.

(** The client's entries: a permutation of the pool's entries with that
    client tag, clock-sorted; their addresses are the index's slice
    ([client_locs_entries], under the key uniqueness); each sits at a slot of
    the pool ([pool_entries_slot] / [client_entries_lookup_slot]); the pool's
    entries carry the pool's runs ([pool_entries_snd]) and, under the
    address [NoDup], distinct entries of one client have disjoint clock
    ranges ([client_entries_disjoint]). *)
Lemma entry_kp_split (e : loc * ItemRun) : entry_kp e = (entry_client e, entry_pr e).
Proof. reflexivity. Qed.

(** The left half of a split keeps the run's head, so its keys are the
    split run's. *)
Lemma entry_kp_split_left (l : loc) (r : ItemRun) (o : nat) :
  (0 < o)%nat -> entry_kp (l, split_run_left r o) = entry_kp (l, r).
Proof.
  move=> Ho. destruct o as [|o']; [lia |]. destruct r as [items d].
  rewrite /entry_kp /entry_client /entry_pr /entry_clock /run_client /run_clock /run_head_item
          /split_run_left /=.
  destruct items; reflexivity.
Qed.

(** An entry's machine-word clock is its run's clock, under the pool's clock
    bound. *)
Lemma entry_clock_Z (l : loc) (r : ItemRun) :
  (Z.of_nat (run_clock r) < 2^64)%Z -> uint.Z (entry_clock (l, r)) = Z.of_nat (run_clock r).
Proof. move=> Hb. rewrite /entry_clock /=. word. Qed.

Lemma client_entries_mem (locs : gmap loc (list loc)) (p : pool) (client : w64) (e : loc * ItemRun) :
  e ∈ client_entries locs p client <-> (e ∈ pool_entries locs p ∧ entry_client e = client).
Proof. rewrite /client_entries (merge_sort_Permutation entry_le _) list_elem_of_filter. tauto. Qed.

Lemma client_entries_sorted (locs : gmap loc (list loc)) (p : pool) (client : w64) :
  StronglySorted entry_le (client_entries locs p client).
Proof. apply StronglySorted_merge_sort; apply _. Qed.

Lemma entry_pr_filter_kp (client : w64) (l : list (loc * ItemRun)) :
  entry_pr <$> filter (λ e, entry_client e = client) l
  = (filter (λ kp : w64 * (Z * loc), kp.1 = client) (entry_kp <$> l)).*2.
Proof.
  induction l as [|e l IH]; [reflexivity|].
  rewrite fmap_cons filter_cons filter_cons entry_kp_split /=.
  case_decide as Hc.
  - rewrite fmap_cons IH /=. reflexivity.
  - exact IH.
Qed.

Lemma SS_entry_pr_merge (l : list (loc * ItemRun)) :
  StronglySorted pr_le (entry_pr <$> merge_sort entry_le l).
Proof.
  apply (StronglySorted_fmap entry_pr entry_le pr_le).
  - move=> x y Hxy. rewrite /pr_le /entry_pr /entry_le in Hxy |- *. exact Hxy.
  - apply (StronglySorted_merge_sort entry_le).
Qed.

Lemma client_entries_prs (locs : gmap loc (list loc)) (p : pool) (client : w64) :
  kp_clkloc (entry_kp <$> pool_entries locs p) ->
  merge_sort pr_le ((filter (λ kp : w64 * (Z * loc), kp.1 = client) (entry_kp <$> pool_entries locs p)).*2)
  = entry_pr <$> client_entries locs p client.
Proof.
  move=> Hkd. rewrite /client_entries -entry_pr_filter_kp.
  apply (StronglySorted_unique_strong pr_le).
  - move=> p1 p2 Hp1 Hp2 H12 H21.
    rewrite (merge_sort_Permutation pr_le) in Hp1.
    rewrite (merge_sort_Permutation entry_le) in Hp2.
    apply list_elem_of_fmap in Hp1 as (x1 & -> & Hx1).
    apply list_elem_of_fmap in Hp2 as (x2 & -> & Hx2).
    apply list_elem_of_filter in Hx1 as [Hc1 Hx1]. apply list_elem_of_filter in Hx2 as [Hc2 Hx2].
    rewrite /pr_le in H12 H21.
    have Hkeq : (entry_pr x1).1 = (entry_pr x2).1 by lia.
    have Hcc : (entry_kp x1).1 = (entry_kp x2).1.
    { rewrite !entry_kp_split /=. congruence. }
    have Hloc := Hkd (entry_kp x1) (entry_kp x2) (list_elem_of_fmap_2 _ _ _ Hx1) (list_elem_of_fmap_2 _ _ _ Hx2) Hcc Hkeq.
    rewrite /entry_pr. f_equal; [exact Hkeq | exact Hloc].
  - apply (StronglySorted_merge_sort pr_le).
  - apply SS_entry_pr_merge.
  - rewrite (merge_sort_Permutation pr_le). apply Permutation_map. symmetry. apply merge_sort_Permutation.
Qed.

Lemma client_locs_entries (locs : gmap loc (list loc)) (p : pool) (client : w64) :
  kp_clkloc (entry_kp <$> pool_entries locs p) ->
  client_locs locs p client = (client_entries locs p client).*1.
Proof.
  move=> Hkd. rewrite /client_locs /kp_client_locs (client_entries_prs locs p client Hkd).
  rewrite -list_fmap_compose. apply list_fmap_ext. move=> i e _. reflexivity.
Qed.

Lemma pool_entries_slot (locs : gmap loc (list loc)) (p : pool) (l : loc) (r : ItemRun) :
  (l, r) ∈ pool_entries locs p <->
  ∃ parent ls tm k, locs !! parent = Some ls ∧ p !! parent = Some tm ∧ ls !! k = Some l ∧ tm_runs tm !! k = Some r.
Proof.
  rewrite /pool_entries list_elem_of_concat. split.
  - move=> [zl [Hin Hzl]].
    apply list_elem_of_fmap in Hzl as (kv & -> & Hkv).
    destruct kv as [parent tm]. apply elem_of_map_to_list in Hkv. simpl in Hin.
    destruct (locs !! parent) as [ls|] eqn:Hls; simpl in Hin; last by rewrite elem_of_nil in Hin.
    apply list_elem_of_lookup in Hin as [k Hk].
    apply lookup_zip_with_Some in Hk as (x & y & Heq & Hx & Hy).
    injection Heq as <- <-.
    by exists parent, ls, tm, k.
  - intros (parent & ls & tm & k & Hls & Hp & Hl & Hr).
    exists (zip ls (tm_runs tm)). split.
    + apply list_elem_of_lookup. exists k. apply lookup_zip_with_Some. by exists l, r.
    + apply list_elem_of_fmap. exists (parent, tm). split; [by rewrite /= Hls | by apply elem_of_map_to_list].
Qed.

Lemma pool_entries_snd (locs : gmap loc (list loc)) (p : pool) :
  dom locs = dom p ->
  (∀ parent ls tm, locs !! parent = Some ls -> p !! parent = Some tm -> length ls = length (tm_runs tm)) ->
  (pool_entries locs p).*2 = all_runs p.
Proof.
  move=> Hdom Hlens. rewrite /pool_entries /all_runs fmap_concat -!list_fmap_compose.
  f_equal. apply list_fmap_ext. move=> i [parent tm] Hi. simpl.
  have Hp : p !! parent = Some tm by (apply elem_of_map_to_list; exact (list_elem_of_lookup_2 _ _ _ Hi)).
  have His : is_Some (locs !! parent).
  { apply elem_of_dom. rewrite Hdom. apply elem_of_dom. by exists tm. }
  destruct His as [ls Hls]. rewrite Hls /=. apply snd_zip. rewrite (Hlens parent ls tm Hls Hp). lia.
Qed.

Lemma pool_entries_locs_NoDup (locs : gmap loc (list loc)) (p : pool) :
  dom locs = dom p ->
  (∀ parent tm, p !! parent = Some tm -> ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm)) ->
  NoDup (concat ((map_to_list locs).*2)) ->
  NoDup (pool_entries locs p).*1.
Proof.
  move=> Hdom Hlens Hnd.
  have Hkp := entries_kp_to_cells locs p Hdom Hlens.
  have Hfst : (pool_entries locs p).*1 = ic_loc <$> all_cells (types_of_locs_pool locs p).
  { have H : (λ kp : w64 * (Z * loc), kp.2.2) <$> (entry_kp <$> pool_entries locs p)
           = (λ kp : w64 * (Z * loc), kp.2.2) <$> (cell_kp <$> all_cells (types_of_locs_pool locs p))
      by rewrite Hkp.
    rewrite -!list_fmap_compose in H. exact H. }
  rewrite Hfst -locs_of_concat (locs_of_types_of_locs_pool locs p Hdom Hlens). exact Hnd.
Qed.

(** One integrate splice adds exactly the new entry to the pool's entries:
    the fresh node's address at the cursor of the address list, its run at
    the same cursor of the run list. *)
Lemma pool_entries_integrate (locs : gmap loc (list loc)) (p : pool) (parent : loc)
    (ls : list loc) (tm : type_model) (idx : nat) (item_l : loc) (r : ItemRun)
    (arr' : list (YjsItem A)) :
  locs !! parent = Some ls -> p !! parent = Some tm ->
  length ls = length (tm_runs tm) ->
  pool_entries (<[parent := integrate_locs ls idx item_l]> locs)
               (<[parent := MkTypeModel (take idx (tm_runs tm) ++ r :: drop idx (tm_runs tm)) arr']> p)
    ≡ₚ (item_l, r) :: pool_entries locs p.
Proof.
  move=> Hls Hp Hlen.
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
  set (Ap := zip (take idx ls) (take idx (tm_runs tm))).
  set (Bp := zip (drop idx ls) (drop idx (tm_runs tm))).
  have HlenA : length (take idx ls) = length (take idx (tm_runs tm)) by rewrite !length_take Hlen.
  have Hother : ∀ q, q ≠ parent -> <[parent := integrate_locs ls idx item_l]> locs !! q = locs !! q.
  { move=> q Hne. rewrite lookup_insert_ne //. }
  have Hold : pool_entries locs p ≡ₚ Ap ++ Bp ++ others.
  { rewrite -{1}(insert_id p parent tm Hp) (Hpe locs tm (λ q _, eq_refl)) /F /= Hls /=.
    rewrite -{1}(take_drop idx ls) -{1}(take_drop idx (tm_runs tm)).
    rewrite zip_with_app; last exact HlenA.
    rewrite -/Ap -/Bp -app_assoc //. }
  have Hnew : pool_entries (<[parent := integrate_locs ls idx item_l]> locs)
                (<[parent := MkTypeModel (take idx (tm_runs tm) ++ r :: drop idx (tm_runs tm)) arr']> p)
              ≡ₚ Ap ++ (item_l, r) :: Bp ++ others.
  { rewrite (Hpe _ _ Hother) /F /= lookup_insert_eq /= /integrate_locs.
    rewrite zip_with_app; last exact HlenA.
    simpl. rewrite -/Ap -/Bp -app_assoc //. }
  rewrite Hnew Hold. symmetry. apply Permutation_middle.
Qed.

(** The address map stays well formed across an integrate splice landing at
    a fresh address. *)
Lemma locs_wf_integrate (locs : gmap loc (list loc)) (p : pool) (parent : loc)
    (ls : list loc) (tm : type_model) (idx : nat) (item_l : loc) (r : ItemRun)
    (arr' : list (YjsItem A)) :
  locs !! parent = Some ls -> p !! parent = Some tm ->
  item_l ∉ concat ((map_to_list locs).*2) ->
  locs_wf locs p ->
  locs_wf (<[parent := integrate_locs ls idx item_l]> locs)
          (<[parent := MkTypeModel (take idx (tm_runs tm) ++ r :: drop idx (tm_runs tm)) arr']> p).
Proof.
  move=> Hls Hp Hfresh [Hdom [Hnd Hlens]].
  have Hperm0 : concat ((map_to_list locs).*2) ≡ₚ ls ++ concat ((map_to_list (delete parent locs)).*2).
  { rewrite -{1}(insert_id locs parent ls Hls).
    rewrite (concat_perm _ _ (Permutation_map snd (map_to_list_insert_existing locs parent ls ls Hls))) //. }
  have Hperm : concat ((map_to_list (<[parent := integrate_locs ls idx item_l]> locs)).*2)
             ≡ₚ integrate_locs ls idx item_l ++ concat ((map_to_list (delete parent locs)).*2).
  { rewrite (concat_perm _ _ (Permutation_map snd (map_to_list_insert_existing locs parent ls _ Hls))) //. }
  have Hil : integrate_locs ls idx item_l ≡ₚ item_l :: ls.
  { rewrite /integrate_locs -{3}(take_drop idx ls). symmetry. apply Permutation_middle. }
  split_and!.
  - rewrite !dom_insert_L Hdom //.
  - rewrite Hperm Hil. rewrite Hperm0 in Hnd Hfresh.
    apply NoDup_cons. split; [exact Hfresh | exact Hnd].
  - move=> q lsq tmq. destruct (decide (q = parent)) as [-> | Hne].
    + rewrite !lookup_insert_eq. move=> [<-] [<-]. simpl.
      have Hlsl := Hlens parent ls tm Hls Hp.
      rewrite /integrate_locs !length_app /= !length_take !length_drop. lia.
    + rewrite !lookup_insert_ne //. exact (Hlens q lsq tmq).
Qed.

(** A tombstoning leaves the item index alone: a flip changes no entry's
    (client, clock, address) key. *)
Lemma pool_entries_flip_kp (locs : gmap loc (list loc)) (p : pool) (parent : loc)
    (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun) :
  locs !! parent = Some ls -> p !! parent = Some tm ->
  ls !! k = Some lc -> tm_runs tm !! k = Some r ->
  entry_kp <$> pool_entries locs (<[parent := MkTypeModel (<[k := flip_run r]> (tm_runs tm)) (tm_arr tm)]> p)
  ≡ₚ entry_kp <$> pool_entries locs p.
Proof.
  move=> Hls Hp Hlk Hrk.
  set (F := λ (kv : loc * type_model), zip (default [] (locs !! kv.1)) (tm_runs kv.2)).
  set (others := concat (F <$> map_to_list (delete parent p))).
  have Hpe : ∀ (tm' : type_model),
      pool_entries locs (<[parent := tm']> p) ≡ₚ F (parent, tm') ++ others.
  { move=> tm'. rewrite /pool_entries.
    have Hm : F <$> map_to_list (<[parent := tm']> p)
            ≡ₚ F <$> ((parent, tm') :: map_to_list (delete parent p)).
    { apply Permutation_map. exact (map_to_list_insert_existing p parent tm tm' Hp). }
    rewrite (concat_perm _ _ Hm) fmap_cons concat_cons //. }
  have Hkp : entry_kp (lc, flip_run r) = entry_kp (lc, r).
  { rewrite /entry_kp /entry_client /entry_pr /entry_clock /run_client /run_clock /run_head_item /flip_run //. }
  have Hzip : zip ls (<[k := flip_run r]> (tm_runs tm)) = <[k := (lc, flip_run r)]> (zip ls (tm_runs tm)).
  { have H := insert_zip_with pair ls (tm_runs tm) k lc (flip_run r).
    rewrite (list_insert_id ls k lc Hlk) in H. rewrite -H //. }
  rewrite (Hpe _) -(insert_id p parent tm Hp) (Hpe tm) /F /= Hls /= Hzip !fmap_app.
  rewrite list_fmap_insert Hkp list_insert_id; first done.
  rewrite list_lookup_fmap lookup_zip_with Hlk Hrk //.
Qed.

(** What a delete step ([pool_after_delete]) transports: the per-type
    item-set map is unchanged, a pointwise fact about the documents
    survives, and so does the registry's model reading. *)
Lemma pool_after_delete_seq_map (p p' : pool) :
  pool_after_delete p p' ->
  ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p')
  = ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p).
Proof.
  intros (Harr & Hdom & _ & _ & _).
  apply map_eq => q. rewrite !lookup_fmap.
  destruct (p' !! q) as [tm'|] eqn:Htm'.
  - destruct (Harr q tm' Htm') as (tm & Htm & Heq). rewrite Htm' Htm /= Heq //.
  - destruct (p !! q) as [tm|] eqn:Htm; last (rewrite Htm' Htm //).
    exfalso. destruct (Hdom q (mk_is_Some _ _ Htm)) as [tm0 Htm0]. rewrite Htm0 in Htm'. done.
Qed.

Lemma pool_after_delete_arr_pointwise (p p' : pool) (Q : YjsItem A -> Prop) :
  pool_after_delete p p' ->
  (∀ parent tm x, p !! parent = Some tm -> x ∈ tm_arr tm -> Q x) ->
  (∀ parent tm x, p' !! parent = Some tm -> x ∈ tm_arr tm -> Q x).
Proof.
  intros (Harr & _) H parent tm' x Htm' Hx.
  destruct (Harr parent tm' Htm') as (tm & Htm & Heq). rewrite Heq in Hx. exact (H parent tm x Htm Hx).
Qed.

Lemma pool_registry_models_after_delete (m : DocModel) (bind : gmap P loc) (p p' : pool) :
  pool_after_delete p p' -> pool_registry_models m bind p -> pool_registry_models m bind p'.
Proof.
  intros (Harr & _) [Hmtypes Hmdom]. split; [| exact Hmdom].
  move=> nm q tm' Hb Htm'. destruct (Harr q tm' Htm') as (tm & Htm & Heq).
  rewrite Heq. exact (Hmtypes nm q tm Hb Htm).
Qed.

Lemma client_entries_NoDup_locs (locs : gmap loc (list loc)) (p : pool) (client : w64) :
  NoDup (pool_entries locs p).*1 -> NoDup (client_entries locs p client).*1.
Proof.
  move=> Hnd. rewrite /client_entries.
  have Hperm : (merge_sort entry_le (filter (λ e, entry_client e = client) (pool_entries locs p))).*1
             ≡ₚ (filter (λ e, entry_client e = client) (pool_entries locs p)).*1.
  { apply Permutation_map. apply merge_sort_Permutation. }
  rewrite Hperm. clear Hperm.
  induction (pool_entries locs p) as [|e l IH]; first done.
  rewrite fmap_cons NoDup_cons in Hnd. destruct Hnd as [Hnotin Hnd].
  rewrite filter_cons. case_decide as Hc.
  - rewrite fmap_cons NoDup_cons. split; [| exact (IH Hnd)].
    move=> Hin. apply Hnotin. apply list_elem_of_fmap in Hin as (e' & Heq & He').
    apply list_elem_of_fmap. exists e'. split; [exact Heq |].
    exact (proj2 (proj1 (list_elem_of_filter _ _ _) He')).
  - exact (IH Hnd).
Qed.

Lemma client_entries_lookup_slot (locs : gmap loc (list loc)) (p : pool) (client : w64)
    (i : nat) (l : loc) (r : ItemRun) :
  client_entries locs p client !! i = Some (l, r) ->
  entry_client (l, r) = client ∧
  ∃ parent ls tm k, locs !! parent = Some ls ∧ p !! parent = Some tm ∧ ls !! k = Some l ∧ tm_runs tm !! k = Some r.
Proof.
  move=> Hi. have Hmem := list_elem_of_lookup_2 _ _ _ Hi.
  apply client_entries_mem in Hmem as [Hpe Hc]. split; [exact Hc | by apply pool_entries_slot].
Qed.

Lemma sorted_client_entries_disjoint (locs : gmap loc (list loc)) (p : pool) (client : w64)
    (E : list (loc * ItemRun)) :
  dom locs = dom p ->
  (∀ parent tm, p !! parent = Some tm -> ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm)) ->
  NoDup (pool_entries locs p).*1 ->
  (∀ r, r ∈ all_runs p -> (Z.of_nat (run_client r) < 2^64)%Z) ->
  runs_disjoint (all_runs p) ->
  sorted_client_entries locs p client E ->
  ∀ (i j : nat) (l1 l2 : loc) (r1 r2 : ItemRun),
    E !! i = Some (l1, r1) -> E !! j = Some (l2, r2) -> i ≠ j ->
    (run_clock r1 + length (run_items r1) <= run_clock r2)%nat ∨
    (run_clock r2 + length (run_items r2) <= run_clock r1)%nat.
Proof.
  move=> Hdom Hlens Hnd Hclb Hdisj [_ [Hndc Hmem]] i j l1 l2 r1 r2 Hi Hj Hij.
  have Hlens' : ∀ parent ls tm, locs !! parent = Some ls -> p !! parent = Some tm ->
      length ls = length (tm_runs tm).
  { move=> parent ls tm Hls Hp. destruct (Hlens parent tm Hp) as (ls' & Hls' & Hlen).
    rewrite Hls in Hls'. injection Hls' as <-. exact Hlen. }
  have Hsnd := pool_entries_snd locs p Hdom Hlens'.
  have Hl12 : l1 ≠ l2.
  { move=> Heq. apply Hij. apply (NoDup_lookup _ i j l1 Hndc);
      rewrite list_lookup_fmap; [rewrite Hi // | rewrite Hj /= Heq //]. }
  have [Hm1 Hc1] := Hmem _ (list_elem_of_lookup_2 _ _ _ Hi).
  have [Hm2 Hc2] := Hmem _ (list_elem_of_lookup_2 _ _ _ Hj).
  apply list_elem_of_lookup in Hm1 as [n1 Hn1]. apply list_elem_of_lookup in Hm2 as [n2 Hn2].
  have Hn12 : n1 ≠ n2.
  { move=> Heq. subst n2. rewrite Hn1 in Hn2. injection Hn2 as Heq _. exact (Hl12 Heq). }
  have Hr1 : all_runs p !! n1 = Some r1 by rewrite -Hsnd list_lookup_fmap Hn1 //.
  have Hr2 : all_runs p !! n2 = Some r2 by rewrite -Hsnd list_lookup_fmap Hn2 //.
  have Hcl : run_client r1 = run_client r2.
  { have Hb1 := Hclb r1 (list_elem_of_lookup_2 _ _ _ Hr1).
    have Hb2 := Hclb r2 (list_elem_of_lookup_2 _ _ _ Hr2).
    rewrite /entry_client /= in Hc1 Hc2.
    have Hz : uint.Z (W64 (run_client r1)) = uint.Z (W64 (run_client r2)) by rewrite Hc1 Hc2.
    apply Nat2Z.inj. word. }
  exact (Hdisj n1 n2 r1 r2 Hr1 Hr2 Hn12 Hcl).
Qed.

(** The index's own entries are such a list. *)
Lemma client_entries_sorted_client (locs : gmap loc (list loc)) (p : pool) (client : w64) :
  NoDup (pool_entries locs p).*1 ->
  sorted_client_entries locs p client (client_entries locs p client).
Proof.
  move=> Hnd. split_and!; [exact (client_entries_sorted locs p client) | exact (client_entries_NoDup_locs locs p client Hnd) |].
  move=> e He. by apply client_entries_mem.
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

Lemma registry_coh_pool (bind : gmap P loc) (types : gmap loc type_state) :
  registry_coh bind types <-> pool_registry_coh bind (pool_of types).
Proof.
  rewrite /registry_coh /pool_registry_coh /pool_of.
  split; move=> [H1 [H2 H3]]; split_and!; try exact H2.
  - move=> nm q Hq. rewrite lookup_fmap fmap_is_Some. exact (H1 nm q Hq).
  - move=> q. rewrite lookup_fmap fmap_is_Some. exact (H3 q).
  - move=> nm q Hq. have := H1 nm q Hq. rewrite lookup_fmap fmap_is_Some //.
  - move=> q Hq. apply (H3 q). rewrite lookup_fmap fmap_is_Some //.
Qed.

Lemma registry_models_pool (m : DocModel) (bind : gmap P loc) (types : gmap loc type_state) :
  registry_models m bind types <-> pool_registry_models m bind (pool_of types).
Proof.
  rewrite /registry_models /pool_registry_models /pool_of.
  split; move=> [H1 H2]; split; try exact H2.
  - move=> nm q tm Hq. rewrite lookup_fmap.
    destruct (types !! q) as [ts|] eqn:Hts; last by [].
    move=> /= [<-]. exact (H1 nm q ts Hq Hts).
  - move=> nm q ts Hq Hts. have := H1 nm q (type_model_of ts) Hq.
    rewrite lookup_fmap Hts /=. move=> H. exact (H eq_refl).
Qed.

End store_value_cells.
