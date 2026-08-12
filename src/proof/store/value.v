(** The [store], VALUE layer: the cell bookkeeping the invariant is stated
    over. Go values but no Iris.

    Definitions
    - [type_state] / [all_cells]: what the invariant tracks per registered
      yType (its DLL cells and its model list), and the cells across the whole
      registry.
    - the per-client node list: [cell_client] / [cell_clock] / [cell_le] /
      [cell_pr] / [cell_kp] and [client_run], the sorted run of one client's
      cells that shadows [store.items].
    - the pool invariants: location [NoDup], clock-range disjointness
      ([cells_range_disjoint]), [cell_fits], [cell_origin_clk], bundled as
      [pool_invs] / [split_step_facts] / [repair_types_facts] /
      [delete_types_facts].
    - [live_refine]: every live cell of the new pool is covered, chars and
      all, by a live cell of the old one, and [ds_tombstoned]: no live cell
      holds an id of the delete set. The pair is what gives the ghost delete
      set its meaning (plan-delete-set.md section 3). Integration breaks
      [live_refine] (it adds a live cell with no ancestor), so it reports the
      weaker [integrate_live_refine] (the escape is "this char is the wire
      item's own"), which the apply loop turns into [apply_live_refine] (the
      escape is "the model did not have this id") with the replay's client
      bound. [dead_chars_kept] is the dual, carrying a delete loop's record of
      what it has already tombstoned across the next iteration's surgeries.
    - the split surgery [split_cell_left] / [split_cell_right] / [split_cells].
    - the id-span abstraction [span_ids] / [span_wf] (a span denotes its whole
      clock interval, since an id addresses any char of a run), and
      [cell_has_id] / [findById_res], the by-id search.
    - [cell_covers]: the model id [d] addresses a char of cell [c]'s run.

    Laws
    - splitting a node is invisible to the model: [split_cells_flatten] and
      [split_cells_num_visible].
    - the pool invariants are preserved by appending a fresh cell ([*_snoc])
      and by any permutation that keeps locations and runs
      ([locs_run_perm_*]). These are the two shapes every store operation
      takes.
    - [all_cells] under a registry insert ([all_cells_insert(_snoc/_empty)],
      [all_cells_lookup]).
    - [client_run] is stable under the same steps ([merge_sort_loc_*],
      [client_run_loc_tail] / [_insert] / [_other], [cellctr_locs_run_perm]),
      and [cell_kp] determines client, clock, location and [cell_pr].
    - [span_ids] is exactly the clock-interval test ([span_ids_elem] at the
      heap level, [span_ids_elem_nat] at the model level), is the singleton on
      a length-1 span, splits at any interior point ([span_ids_split]), and
      matches a run's char ids ([span_ids_char_ids]).
    - a well-formed run denotes exactly its cell's coordinate window
      ([run_wf_char_id_bound] and its converse [run_wf_char_id_mem]), which
      gives store-global id uniqueness out of the pool invariants alone
      ([cells_char_id_unique], via [pool_loc_inj]) and hence the obligation a
      delete must discharge to mint a certificate ([ds_tombstoned_char_ids]).
    - [live_refine] is reflexive, transitive, and holds of a tombstone flip
      ([live_refine_flip], over the cell-level [flip_pool_perm]) and of a
      cell-preserving permutation; [ds_tombstoned] travels along it
      ([ds_tombstoned_refine]) and along an integrate splice whose fresh run
      misses the set ([ds_tombstoned_snoc]).

    The Iris layer over all of this is [store/heap.v]. *)
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

Section store_value.

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

(* ===== the split surgery on abstract cells (issue #28 M2) ================
   Splitting a run node is pure cell surgery: the left half keeps the node
   location and the first [o] model items, the right half is a fresh node
   carrying the rest, and BOTH halves inherit the deleted bit and parent (the
   yjs splitItem semantics; y-octo drops the right half's flags, a reported
   divergence). The flatten and the visible count are unchanged, which is why
   every public predicate is invariant under splits. *)

Definition split_cell_left (c : item_cell) (o : nat) : item_cell :=
  MkItemCell (ic_loc c) (take o (ic_run c)) (ic_deleted c) (ic_parent c).

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

(** [cell_covers c d]: the model id [d] addresses a char of cell [c]'s run
    (issue #28 U7c): same client as the run head, and clock inside the run's
    range [head clock, head clock + run length). The per-char [run_wf] id law
    ([run_wf_char_id]) makes this exactly "[d] is the id of some [ic_run c]
    char". Replaces the all-singleton head-only [item_id (run_head c) = d]. *)
Definition cell_covers (c : item_cell) (d : YjsId) : Prop :=
  clientId (item_id (run_head c)) = clientId d ∧
  (clock (item_id (run_head c)) <= clock d)%nat ∧
  (clock d < clock (item_id (run_head c)) + length (ic_run c))%nat.

(* ===== wire-level drain (issue #40 x issue #28 U7c) =======================
   The Go [applyUpdate] loop drains WIRE items (whole [updateItem] structs),
   integrating each ready one as ONE run cell -- a whole [expand_input] chunk of
   [integrate_all]. [wire_pass] / [wire_drain] mirror the per-char [pending_pass]
   / [pending_drain] ([network_model]) but step by [integrate_all] over a
   wire item's ops, so the drain loop refines them 1:1. The bridge to the
   per-char model (for the certificate [ValidReplay]) is
   [WireReplay_to_PendingReplay] in [store/applyUpdate]: it turns a [WireReplay]
   into a [PendingReplay] of the [expand_inputs], re-deriving each chunk's
   freshness from head-freshness via [delivered_clock_bound]. Reuses
   [pending_keep] / [doc_model_has] / [input_ready] (a wire item's readiness is its
   head op's, since [typedInput.2]'s origins are the head's). *)

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

Definition split_cell_right (c : item_cell) (o : nat) (r_loc : loc) : item_cell :=
  MkItemCell r_loc (drop o (ic_run c)) (ic_deleted c) (ic_parent c).

Definition split_cells (cells : list item_cell) (k o : nat) (r_loc : loc) : list item_cell :=
  match cells !! k with
  | Some c => take k cells ++ [split_cell_left c o; split_cell_right c o r_loc] ++ drop (S k) cells
  | None => cells
  end.

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

(* ----- id-span-slice abstraction to a gset ------------------------------ *)

(** The char ids one [idSpan] covers: the [len] consecutive clocks from the
    head id, at the span's client. An id addresses ANY char of a scanned run
    (yjs getItem semantics, issue #28), so the scan's id sets are CHAR-id sets
    and a span denotes its whole clock interval. *)
Definition span_ids (v : yjs.idSpan.t) : gset YjsId :=
  list_to_set
    ((λ o, MkYjsId (uint.nat v.(yjs.idSpan.id').(yjs.id.clientId'))
                   (uint.nat v.(yjs.idSpan.id').(yjs.id.clock') + o)%nat)
       <$> seq 0 (uint.nat v.(yjs.idSpan.len'))).

(** The ids a WIRE delete batch denotes: a span is its whole clock interval,
    and the batch is their union. This is the PURE model of the [deleteSpan]
    slice, and it is the right one because deletes are STATE, not operations:
    a batch means exactly the set of ids it tombstones, with no order and no
    multiplicity, which is why two batches with the same union are the same
    request. A public spec speaks about this set and never about the heap
    records behind it. *)
Definition delete_span_ids (sp : yjs.deleteSpan.t) : gset YjsId :=
  span_ids (yjs.idSpan.mk (yjs.id.mk sp.(yjs.deleteSpan.client')
                                     sp.(yjs.deleteSpan.clock'))
                          sp.(yjs.deleteSpan.length')).

Definition delete_batch_ids (spans : list yjs.deleteSpan.t) : gset YjsId :=
  ⋃ (delete_span_ids <$> spans).

(** A span's clock interval does not wrap: [containsId]'s Go range test
    computes [clock + len] in [w64], so this is what makes the test decide
    [span_ids] membership. Sourced from the store's run-fits pool invariant. *)
Definition span_wf (v : yjs.idSpan.t) : Prop :=
  (uint.Z v.(yjs.idSpan.id').(yjs.id.clock') + uint.Z v.(yjs.idSpan.len') < 2^64)%Z.

(* ----- findById: locate a node by id in the DLL ------------------------- *)

(** The cell predicate [findById] decides: a cell whose model id is [toYjsId idv].
    [findById] returns the first matching node's location, or [null]. *)
Definition cell_has_id (idv : yjs.id.t) (c : item_cell) : Prop :=
  item_id (run_head c) = toYjsId idv.

#[local] Instance cell_has_id_dec idv c : Decision (cell_has_id idv c).
Proof. rewrite /cell_has_id. apply _. Defined.

(** Result location of [findById] over a cell list: first match, else [null]. *)
Definition findById_res (cells : list item_cell) (idv : yjs.id.t) : loc :=
  match list_find (cell_has_id idv) cells with
  | Some (_, c) => ic_loc c
  | None => null
  end.

(* ----- invariant-carrying split wrappers (issue #28 stage D2b) ------------
   The D1b heap specs packaged with the D1c/D2a pool bookkeeping: pool
   invariants out for pool invariants in, plus the transport facts [repair]
   needs to sequence two splits (document/domain preservation, coverage
   transport with provenance, stability away from the split location, run
   list growth) and the boundary cell itself. *)

Definition pool_invs (types : gmap loc type_state) : Prop :=
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ∧
  NoDup (ic_loc <$> all_cells types) ∧
  cells_range_disjoint (all_cells types) ∧
  (∀ c, c ∈ all_cells types -> cell_origin_clk c).

(* ----- the live-cell refinement and the tombstone-set invariant --------- *)

(** [live_refine types types']: every LIVE (untombstoned) cell of the new pool
    has a LIVE cell of the old pool holding all of its chars. Three of the
    four surgeries the store performs satisfy it: a split's halves inherit the
    node's [ic_deleted] bit and share out its run, a tombstone flip only turns
    bits ON, and registering a type adds no cells. Integration does NOT (it
    adds a live cell with no ancestor); that step re-establishes
    [ds_tombstoned] from the new id's freshness instead ([ds_tombstoned_snoc]).

    Stated over chars, not coordinates, because the tombstone set is a set of
    [YjsId]s: the coordinate clause of the records below is about where a cell
    sits in its client's clock space, which is the wrong currency here. *)
Definition live_refine (types types' : gmap loc type_state) : Prop :=
  ∀ c', c' ∈ all_cells types' -> ic_deleted c' = false ->
    ∃ c, c ∈ all_cells types ∧ ic_deleted c = false ∧
         (∀ y, y ∈ ic_run c' -> y ∈ ic_run c).

(** [apply_live_refine m pool pool']: the growth-tolerant form of
    [live_refine], which the remote apply path needs because integration adds
    a LIVE cell with no ancestor. Every char of every live cell of the new
    pool either sat in a live cell of the old one, or is an id the model [m]
    did not have at all, i.e. a char this apply just integrated. Both
    disjuncts keep the char out of the delete set: the first by the invariant
    itself, the second by the domain bound (the set only holds ids of [m]).

    Composable across steps against a FIXED [m], the model the apply started
    from: the second disjunct only gets easier as the model grows, so a char
    fresh to a later model is fresh to [m] too. *)
Definition apply_live_refine (m : DocModel) (pool pool' : list item_cell) : Prop :=
  ∀ c', c' ∈ pool' -> ic_deleted c' = false -> ∀ y, y ∈ ic_run c' ->
    (∃ c, c ∈ pool ∧ ic_deleted c = false ∧ y ∈ ic_run c)
    ∨ doc_model_has m (item_id y) = false.

(** A well-formed run's chars all carry the head's client and a clock at or
    above the head's: [run_wf] makes the run one client's consecutive clocks
    starting at the head ([run_wf_lookup_clock]). This is what turns a cell's
    coordinates into a statement about its chars' ids. *)
Lemma run_wf_char_id_bound (c : item_cell) (y : YjsItem A) :
  run_wf (ic_run c) -> y ∈ ic_run c ->
  clientId (item_id y) = clientId (item_id (run_head c)) ∧
  (clock (item_id (run_head c)) <= clock (item_id y) <
     clock (item_id (run_head c)) + length (ic_run c))%nat.
Proof.
  move=> Hwf Hy.
  have Hne : ic_run c ≠ [] by (move: Hwf => [Hne _]; exact Hne).
  have Hhd : ic_run c !! 0%nat = Some (run_head c).
  { rewrite /run_head. by destruct (ic_run c). }
  apply list_elem_of_lookup_1 in Hy as [o Ho].
  have Holt : (o < length (ic_run c))%nat := lookup_lt_Some _ _ _ Ho.
  rewrite (run_wf_lookup_clock (ic_run c) o (run_head c) y Hwf Hhd Ho) /=.
  split; [reflexivity | lia].
Qed.

(** The converse: every id in a run's client/clock window IS one of its chars.
    Together with [run_wf_char_id_bound] this says a run denotes exactly its
    coordinate window, which is what lets a delete loop turn "this node is
    tombstoned" into "these span ids are tombstoned". *)
Lemma run_wf_char_id_mem (c : item_cell) (i : YjsId) :
  run_wf (ic_run c) ->
  clientId i = clientId (item_id (run_head c)) ->
  (clock (item_id (run_head c)) <= clock i <
     clock (item_id (run_head c)) + length (ic_run c))%nat ->
  i ∈ char_ids (ic_run c).
Proof.
  move=> Hwf Hcl [Hlo Hhi].
  have Hhd : ic_run c !! 0%nat = Some (run_head c).
  { rewrite /run_head. move: Hwf => [Hne _]. by destruct (ic_run c). }
  set (o := (clock i - clock (item_id (run_head c)))%nat).
  have [y Hy] : is_Some (ic_run c !! o).
  { apply lookup_lt_is_Some. rewrite /o. lia. }
  have Hid := run_wf_lookup_clock (ic_run c) o (run_head c) y Hwf Hhd Hy.
  rewrite /char_ids elem_of_list_to_set list_elem_of_fmap.
  exists y. split; last exact (list_elem_of_lookup_2 _ _ _ Hy).
  rewrite Hid. destruct i as [ci ki]. simpl in *. rewrite /o. f_equal; lia.
Qed.

(** Locations identify pooled cells ([NoDup] of the pool's locations is one of
    the pool invariants), which is what lets a cell-level disjointness
    hypothesis be applied to two cells known to differ. *)
Lemma pool_loc_inj (pool : list item_cell) (c1 c2 : item_cell) :
  NoDup (ic_loc <$> pool) -> c1 ∈ pool -> c2 ∈ pool ->
  ic_loc c1 = ic_loc c2 -> c1 = c2.
Proof.
  move=> Hnd Hc1 Hc2 Heq.
  apply list_elem_of_lookup_1 in Hc1 as [i Hi].
  apply list_elem_of_lookup_1 in Hc2 as [j Hj].
  have Hij : i = j.
  { apply (NoDup_lookup (ic_loc <$> pool) i j (ic_loc c1) Hnd).
    - rewrite list_lookup_fmap Hi //.
    - rewrite list_lookup_fmap Hj /= Heq //. }
  subst j. rewrite Hi in Hj. by injection Hj.
Qed.

(** Store-global id uniqueness, out of the pool invariants alone: two cells at
    different locations never share a char id. Same client puts their clock
    ranges apart ([cells_range_disjoint]) and a run's chars sit exactly inside
    its own cell's range, with [cell_fits] keeping the [w64] coordinates
    honest; different clients differ in the id's client field outright.

    This is the fact docs/plan-delete-set.md expected to need real plumbing
    ("store-global id uniqueness"): the pool invariants already carry it. *)
Lemma cells_char_id_unique (pool : list item_cell) (c1 c2 : item_cell)
    (y1 y2 : YjsItem A) :
  cells_range_disjoint pool ->
  (∀ c, c ∈ pool -> run_wf (ic_run c)) ->
  (∀ c, c ∈ pool -> (Z.of_nat (clock (item_id (run_head c))) < 2^64)%Z) ->
  c1 ∈ pool -> c2 ∈ pool -> ic_loc c1 ≠ ic_loc c2 ->
  y1 ∈ ic_run c1 -> y2 ∈ ic_run c2 -> item_id y1 ≠ item_id y2.
Proof.
  move=> Hdisj Hwf Hclkb Hc1 Hc2 Hloc Hy1 Hy2 Hideq.
  have [Hcl1 Hrg1] := run_wf_char_id_bound c1 y1 (Hwf c1 Hc1) Hy1.
  have [Hcl2 Hrg2] := run_wf_char_id_bound c2 y2 (Hwf c2 Hc2) Hy2.
  have Hclheads : clientId (item_id (run_head c1)) = clientId (item_id (run_head c2)).
  { rewrite -Hcl1 -Hcl2 Hideq //. }
  have Hccells : cell_client c1 = cell_client c2
    by rewrite /cell_client Hclheads.
  have Hb1 := Hclkb c1 Hc1. have Hb2 := Hclkb c2 Hc2.
  have Hz1 : uint.Z (cell_clock c1) = Z.of_nat (clock (item_id (run_head c1)))
    by (rewrite /cell_clock; word).
  have Hz2 : uint.Z (cell_clock c2) = Z.of_nat (clock (item_id (run_head c2)))
    by (rewrite /cell_clock; word).
  have Hclk : clock (item_id y1) = clock (item_id y2) by rewrite Hideq.
  destruct (Hdisj c1 c2 Hc1 Hc2 Hccells Hloc) as [Hle | Hle]; lia.
Qed.

(** [integrate_live_refine input pool pool']: what one integrate step gives,
    stated without a model so the step itself stays model-agnostic (like the
    coordinate provenance clause next to it). A char of a live cell of the new
    pool either sat in a live cell of the old one, or is one of the integrated
    wire item's own chars, recognised by its client and a clock at or above
    the item's. The caller turns the second disjunct into "the model did not
    have this id" with the replay's client bound, which is the form
    [apply_live_refine] wants. *)
Definition integrate_live_refine (input : IntegrateInput (A := A))
    (pool pool' : list item_cell) : Prop :=
  ∀ c', c' ∈ pool' -> ic_deleted c' = false -> ∀ y, y ∈ ic_run c' ->
    (∃ c, c ∈ pool ∧ ic_deleted c = false ∧ y ∈ ic_run c)
    ∨ (clientId (item_id y) = clientId (in_id input) ∧
       (clock (in_id input) <= clock (item_id y))%nat).

(** [dead_chars_kept types types']: the dual of [live_refine]. Every char of
    a TOMBSTONED cell is still held by a tombstoned cell of the new pool. A
    split's halves inherit the bit and partition the run, and a flip only
    turns bits on, so both keep it. This is what lets a delete loop carry
    "everything covered so far is tombstoned" across the surgeries the next
    iteration performs. *)
Definition dead_chars_kept (types types' : gmap loc type_state) : Prop :=
  ∀ c, c ∈ all_cells types -> ic_deleted c = true -> ∀ y, y ∈ ic_run c ->
    ∃ c', c' ∈ all_cells types' ∧ ic_deleted c' = true ∧ y ∈ ic_run c'.

(** [ds_tombstoned ds pool]: no LIVE cell of the pool holds a char whose id is
    in [ds]. This is the direction of #37's [deleted_match] that gives the
    delete set its MEANING: without it an [is_ds_lb] certificate is a receipt
    any implementation could mint, including one whose [Delete] does nothing.
    With it, the certificate says the ids are gone from every live node, hence
    from the visible document a reader observes (issue #125).

    The converse (every tombstoned char is recorded in [ds]) is deliberately
    NOT carried: nothing consumes it, and it would force every delete to grow
    the ghost set eagerly, which is exactly the bookkeeping y-octo's
    [delete_item_inner] does and ours does not. *)
Definition ds_tombstoned (ds : gset YjsId) (pool : list item_cell) : Prop :=
  ∀ c, c ∈ pool -> ic_deleted c = false -> ∀ y, y ∈ ic_run c -> item_id y ∉ ds.

Definition split_step_facts (types types' : gmap loc type_state) (w : item_cell) : Prop :=
  (∀ p ts', types' !! p = Some ts' ->
     ∃ ts, types !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
           run_flatten (ty_cells ts') = run_flatten (ty_cells ts)) ∧
  (∀ p, is_Some (types !! p) -> is_Some (types' !! p)) ∧
  (∀ kc, (length (client_run types' kc) <= S (length (client_run types kc)))%nat) ∧
  (∀ c, c ∈ all_cells types -> ic_loc c ≠ ic_loc w -> c ∈ all_cells types') ∧
  (∀ (ccl : w64) (clkZ : Z) (c : item_cell), c ∈ all_cells types ->
     cell_client c = ccl -> (uint.Z (cell_clock c) <= clkZ)%Z ->
     (clkZ < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z ->
     ∃ c', c' ∈ all_cells types' ∧ cell_client c' = ccl ∧
           (uint.Z (cell_clock c') <= clkZ)%Z ∧
           (clkZ < uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')))%Z ∧
           ic_parent c' = ic_parent c ∧
           (c' = c ∨ (c = w ∧ (1 < length (ic_run w))%nat ∧
                      (ic_loc c' = ic_loc w ∨
                       ic_loc c' ∉ (ic_loc <$> all_cells types))))) ∧
  (∀ p ts ts', types !! p = Some ts -> types' !! p = Some ts' ->
     Forall cell_unit (ty_cells ts) -> ts' = ts) ∧
  (∀ c', c' ∈ all_cells types' -> ∃ c, c ∈ all_cells types ∧
     cell_client c' = cell_client c ∧
     (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
     (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')) <=
      uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z) ∧
  live_refine types types' ∧
  dead_chars_kept types types'.

(** What [repair] guarantees about the type map: per-type model documents and
    the domain survive, and each client's run list grows by at most the two
    possible splits. *)
Definition repair_types_facts (types types2 : gmap loc type_state) : Prop :=
  (∀ p ts', types2 !! p = Some ts' ->
     ∃ ts, types !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
           run_flatten (ty_cells ts') = run_flatten (ty_cells ts)) ∧
  (∀ p, is_Some (types !! p) -> is_Some (types2 !! p)) ∧
  (∀ kc, (length (client_run types2 kc) <= 2 + length (client_run types kc))%nat) ∧
  (∀ p ts ts', types !! p = Some ts -> types2 !! p = Some ts' ->
     Forall cell_unit (ty_cells ts) -> ts' = ts) ∧
  (∀ c', c' ∈ all_cells types2 -> ∃ c, c ∈ all_cells types ∧
     cell_client c' = cell_client c ∧
     (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
     (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')) <=
      uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z) ∧
  live_refine types types2.

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

Lemma dead_chars_kept_flip (types : gmap loc type_state) (p : loc)
    (ts : type_state) (k : nat) (c : item_cell) :
  types !! p = Some ts -> ty_cells ts !! k = Some c ->
  dead_chars_kept types
    (<[p := MkTypeState (<[k := flip_cell c]> (ty_cells ts)) (ty_arr ts)]> types).
Proof.
  move=> Hp Hck.
  destruct (flip_pool_perm types p ts k c Hp Hck) as (rest & Hold & Hnew).
  move=> c0 Hc0 Hdel y Hy. rewrite Hold in Hc0.
  apply elem_of_cons in Hc0 as [-> | Hc0].
  - exists (flip_cell c). split_and!;
      [rewrite Hnew; apply list_elem_of_here | done | exact Hy].
  - exists c0. split_and!;
      [rewrite Hnew; apply elem_of_cons; by right | exact Hdel | exact Hy].
Qed.

Lemma live_refine_flip (types : gmap loc type_state) (p : loc)
    (ts : type_state) (k : nat) (c : item_cell) :
  types !! p = Some ts -> ty_cells ts !! k = Some c ->
  live_refine types
    (<[p := MkTypeState (<[k := flip_cell c]> (ty_cells ts)) (ty_arr ts)]> types).
Proof.
  move=> Hp Hck.
  destruct (flip_pool_perm types p ts k c Hp Hck) as (rest & Hold & Hnew).
  move=> c' Hc' Hlive. rewrite Hnew in Hc'.
  apply elem_of_cons in Hc' as [-> | Hc'].
  { by rewrite /flip_cell /= in Hlive. }
  exists c'. split_and!; [rewrite Hold; by apply elem_of_cons; right | exact Hlive | done].
Qed.

(** What the wire delete path guarantees about the type map (issue #133): the
    per-type MODEL documents are untouched (both surgeries it performs, a
    split and a tombstone, are model no-ops), no type disappears, and the live
    cells only shrink. Unlike [repair_types_facts] this carries no run-length
    bound, because the delete loop splits an unbounded number of times; that
    is also what makes it transitive, so the loop can compose one record per
    step. *)
Definition delete_types_facts (types types' : gmap loc type_state) : Prop :=
  (∀ p ts', types' !! p = Some ts' ->
     ∃ ts, types !! p = Some ts ∧ ty_arr ts' = ty_arr ts) ∧
  (∀ p, is_Some (types !! p) -> is_Some (types' !! p)) ∧
  live_refine types types' ∧
  dead_chars_kept types types' ∧
  (∀ c', c' ∈ all_cells types' -> ∃ c, c ∈ all_cells types ∧
     cell_client c' = cell_client c ∧
     (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
     (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c'))
      <= uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z).

Lemma live_refine_refl (types : gmap loc type_state) : live_refine types types.
Proof. move=> c' Hc' Hlive. exists c'. split_and!; [exact Hc' | exact Hlive | done]. Qed.

Lemma live_refine_trans (t1 t2 t3 : gmap loc type_state) :
  live_refine t1 t2 -> live_refine t2 t3 -> live_refine t1 t3.
Proof.
  move=> H12 H23 c3 Hc3 Hlive3.
  destruct (H23 c3 Hc3 Hlive3) as (c2 & Hc2 & Hlive2 & Hrun2).
  destruct (H12 c2 Hc2 Hlive2) as (c1 & Hc1 & Hlive1 & Hrun1).
  exists c1. split_and!; [exact Hc1 | exact Hlive1 |].
  move=> y Hy. exact (Hrun1 y (Hrun2 y Hy)).
Qed.

(** Registering a fresh empty type moves no cells. *)
Lemma live_refine_perm (types types' : gmap loc type_state) :
  all_cells types' ≡ₚ all_cells types -> live_refine types types'.
Proof.
  move=> Hperm c' Hc' Hlive. exists c'.
  split_and!; [by rewrite -Hperm | exact Hlive | done].
Qed.

(** The tombstone-set invariant travels forward along any of the three
    surgeries, since each of them only ever shrinks the live chars. *)
Lemma ds_tombstoned_refine (ds : gset YjsId) (types types' : gmap loc type_state) :
  live_refine types types' ->
  ds_tombstoned ds (all_cells types) -> ds_tombstoned ds (all_cells types').
Proof.
  move=> Hlr Hds c' Hc' Hlive y Hy.
  destruct (Hlr c' Hc' Hlive) as (c & Hc & Hlivec & Hrun).
  exact (Hds c Hc Hlivec y (Hrun y Hy)).
Qed.

Lemma ds_tombstoned_perm (ds : gset YjsId) (pool pool' : list item_cell) :
  pool' ≡ₚ pool -> ds_tombstoned ds pool -> ds_tombstoned ds pool'.
Proof. move=> Hperm Hds c Hc. apply Hds. by rewrite -Hperm. Qed.

(** Integration is the one step with no live ancestor for its new cell: the
    fresh run's ids must be outside the set, which is where the domain bound
    [ds_dom] plus the id's freshness comes in (see [store/heap.v]). *)
Lemma ds_tombstoned_snoc (ds : gset YjsId) (pool pool' : list item_cell)
    (c : item_cell) :
  pool' ≡ₚ pool ++ [c] ->
  ds_tombstoned ds pool ->
  (∀ y, y ∈ ic_run c -> item_id y ∉ ds) ->
  ds_tombstoned ds pool'.
Proof.
  move=> Hperm Hds Hfresh c0 Hc0. rewrite Hperm in Hc0.
  apply elem_of_app in Hc0 as [Hc0 | Hc0].
  - exact (Hds c0 Hc0).
  - apply list_elem_of_singleton in Hc0 as ->. move=> _. exact Hfresh.
Qed.

(** Growing the set: the new ids must miss every live cell. This is the
    obligation a delete discharges to mint its [is_ds_lb] certificate. *)
Lemma ds_tombstoned_union (ds S : gset YjsId) (pool : list item_cell) :
  ds_tombstoned ds pool -> ds_tombstoned S pool -> ds_tombstoned (ds ∪ S) pool.
Proof.
  move=> Hds HS c Hc Hlive y Hy.
  apply not_elem_of_union. split; [exact (Hds c Hc Hlive y Hy) | exact (HS c Hc Hlive y Hy)].
Qed.

(** A tombstoned cell's chars are gone from every LIVE cell of the pool: they
    are gone from every OTHER cell by id uniqueness, and the cell itself is
    not live. This is the obligation [own_ds_grow] puts on a delete before it
    hands out an [is_ds_lb] certificate. *)
Lemma ds_tombstoned_char_ids (pool : list item_cell) (c : item_cell) :
  cells_range_disjoint pool ->
  (∀ c0, c0 ∈ pool -> run_wf (ic_run c0)) ->
  (∀ c0, c0 ∈ pool -> (Z.of_nat (clock (item_id (run_head c0))) < 2^64)%Z) ->
  NoDup (ic_loc <$> pool) ->
  c ∈ pool -> ic_deleted c = true ->
  ds_tombstoned (char_ids (ic_run c)) pool.
Proof.
  move=> Hdisj Hwf Hclkb Hnd Hc Hdel c0 Hc0 Hlive y Hy Hin.
  rewrite /char_ids elem_of_list_to_set list_elem_of_fmap in Hin.
  destruct Hin as (z & Hidz & Hz).
  have Hne : ic_loc c0 ≠ ic_loc c.
  { move=> Hloc. have Heqc := pool_loc_inj pool c0 c Hnd Hc0 Hc Hloc.
    subst c0. by rewrite Hdel in Hlive. }
  exact (cells_char_id_unique pool c0 c y z Hdisj Hwf Hclkb Hc0 Hc Hne Hy Hz
           Hidz).
Qed.

Lemma ds_tombstoned_mono (ds ds' : gset YjsId) (pool : list item_cell) :
  ds' ⊆ ds -> ds_tombstoned ds pool -> ds_tombstoned ds' pool.
Proof. move=> Hsub Hds c Hc Hlive y Hy Hin. exact (Hds c Hc Hlive y Hy (Hsub _ Hin)). Qed.

Lemma apply_live_refine_refl (m : DocModel) (pool : list item_cell) :
  apply_live_refine m pool pool.
Proof. move=> c' Hc' Hlive y Hy. left. by exists c'. Qed.

Lemma apply_live_refine_of_live_refine (m : DocModel) (types types' : gmap loc type_state) :
  live_refine types types' ->
  apply_live_refine m (all_cells types) (all_cells types').
Proof.
  move=> Hlr c' Hc' Hlive y Hy. left.
  destruct (Hlr c' Hc' Hlive) as (c & Hc & Hlivec & Hrun).
  exists c. split_and!; [exact Hc | exact Hlivec | exact (Hrun y Hy)].
Qed.

(** Composition: the middle step is stated against the LATER model, and its
    freshness disjunct transfers to [m] because the model only grew. *)
Lemma apply_live_refine_trans (m m1 : DocModel) (pool pool1 pool2 : list item_cell) :
  (∀ i, doc_model_has m i = true -> doc_model_has m1 i = true) ->
  apply_live_refine m pool pool1 ->
  apply_live_refine m1 pool1 pool2 ->
  apply_live_refine m pool pool2.
Proof.
  move=> Hmono H01 H12 c2 Hc2 Hlive2 y Hy.
  destruct (H12 c2 Hc2 Hlive2 y Hy) as [(c1 & Hc1 & Hlive1 & Hy1) | Hfresh1].
  - exact (H01 c1 Hc1 Hlive1 y Hy1).
  - right. destruct (doc_model_has m (item_id y)) eqn:Hh; last done.
    by rewrite (Hmono _ Hh) in Hfresh1.
Qed.

(** The integrate splice: the pool grows by one live cell whose chars the
    model does not have yet. *)
Lemma apply_live_refine_snoc (m : DocModel) (pool pool' : list item_cell)
    (c : item_cell) :
  pool' ≡ₚ pool ++ [c] ->
  (∀ y, y ∈ ic_run c -> doc_model_has m (item_id y) = false) ->
  apply_live_refine m pool pool'.
Proof.
  move=> Hperm Hfresh c' Hc' Hlive y Hy. rewrite Hperm in Hc'.
  apply elem_of_app in Hc' as [Hc' | Hc'].
  - left. by exists c'.
  - apply list_elem_of_singleton in Hc' as ->. right. exact (Hfresh y Hy).
Qed.

Lemma integrate_live_refine_of_live_refine (input : IntegrateInput (A := A))
    (types types' : gmap loc type_state) :
  live_refine types types' ->
  integrate_live_refine input (all_cells types) (all_cells types').
Proof.
  move=> Hlr c' Hc' Hlive y Hy. left.
  destruct (Hlr c' Hc' Hlive) as (c & Hc & Hlivec & Hrun).
  exists c. split_and!; [exact Hc | exact Hlivec | exact (Hrun y Hy)].
Qed.

Lemma integrate_live_refine_trans (input : IntegrateInput (A := A))
    (pool pool1 pool2 : list item_cell) :
  integrate_live_refine input pool pool1 ->
  integrate_live_refine input pool1 pool2 ->
  integrate_live_refine input pool pool2.
Proof.
  move=> H01 H12 c2 Hc2 Hlive2 y Hy.
  destruct (H12 c2 Hc2 Hlive2 y Hy) as [(c1 & Hc1 & Hlive1 & Hy1) | Hnew]; last by right.
  exact (H01 c1 Hc1 Hlive1 y Hy1).
Qed.

(** The splice itself: the pool grows by one cell all of whose chars carry the
    integrated item's client and a clock at or above its own. That is read off
    the cell's coordinates ([cell_client] / [cell_clock]) plus the run's own
    well-formedness, which is why the caller passes [run_wf]. *)
Lemma integrate_live_refine_snoc (input : IntegrateInput (A := A))
    (pool pool' : list item_cell) (c : item_cell) :
  pool' ≡ₚ pool ++ [c] ->
  (∀ y, y ∈ ic_run c -> clientId (item_id y) = clientId (in_id input) ∧
     (clock (in_id input) <= clock (item_id y))%nat) ->
  integrate_live_refine input pool pool'.
Proof.
  move=> Hperm Hnew c' Hc' Hlive y Hy. rewrite Hperm in Hc'.
  apply elem_of_app in Hc' as [Hc' | Hc'].
  - left. by exists c'.
  - apply list_elem_of_singleton in Hc' as ->. right. exact (Hnew y Hy).
Qed.

(** The bridge the apply loop uses: an integrate step's second disjunct (the
    char carries the wire item's client and a clock at or above its own) is
    exactly freshness against the model, because the replay's [VR_cons] bound
    puts every same-client item of the model strictly below the item's clock. *)
Lemma apply_live_refine_of_integrate (input : IntegrateInput (A := A))
    (mc : DocModel) (pool pool' : list item_cell) :
  (∀ (t' : TId) x, x ∈ doc_model_get mc t' ->
     clientId (item_id x) = clientId (in_id input) ->
     (clock (item_id x) < clock (in_id input))%nat) ->
  integrate_live_refine input pool pool' ->
  apply_live_refine mc pool pool'.
Proof.
  move=> Hbound Hilr c' Hc' Hlive y Hy.
  destruct (Hilr c' Hc' Hlive y Hy) as [Hold | [Hcl Hlo]]; first by left.
  right. destruct (doc_model_has mc (item_id y)) eqn:Hh; last done.
  exfalso. apply docm_has_spec in Hh as (t' & x & Hx & Hid).
  have Hcx : clientId (item_id x) = clientId (in_id input) by rewrite Hid.
  have := Hbound t' x Hx Hcx. rewrite Hid. lia.
Qed.

Lemma dead_chars_kept_refl (types : gmap loc type_state) : dead_chars_kept types types.
Proof. move=> c Hc Hdel y Hy. exists c. split_and!; done. Qed.

Lemma dead_chars_kept_trans (t1 t2 t3 : gmap loc type_state) :
  dead_chars_kept t1 t2 -> dead_chars_kept t2 t3 -> dead_chars_kept t1 t3.
Proof.
  move=> H12 H23 c1 Hc1 Hdel1 y Hy.
  destruct (H12 c1 Hc1 Hdel1 y Hy) as (c2 & Hc2 & Hdel2 & Hy2).
  exact (H23 c2 Hc2 Hdel2 y Hy2).
Qed.

Lemma dead_chars_kept_perm (types types' : gmap loc type_state) :
  all_cells types' ≡ₚ all_cells types -> dead_chars_kept types types'.
Proof.
  move=> Hperm c Hc Hdel y Hy. exists c. split_and!; [by rewrite Hperm | exact Hdel | exact Hy].
Qed.

Lemma delete_types_facts_refl (types : gmap loc type_state) :
  delete_types_facts types types.
Proof.
  split_and!; [move=> p ts' Hp; by exists ts' | done | exact (live_refine_refl types)
              | exact (dead_chars_kept_refl types) |].
  move=> c' Hc'. exists c'. split_and!; [exact Hc' | done | lia | lia].
Qed.

Lemma delete_types_facts_trans (t1 t2 t3 : gmap loc type_state) :
  delete_types_facts t1 t2 -> delete_types_facts t2 t3 -> delete_types_facts t1 t3.
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

(** A split step is a delete step: [split_step_facts]'s model and coordinate
    clauses. *)
Lemma delete_types_facts_of_split (types types' : gmap loc type_state) (w : item_cell) :
  split_step_facts types types' w -> delete_types_facts types types'.
Proof.
  move=> [Harr [Hdom [_ [_ [_ [_ [Hco [Hlr Hdk]]]]]]]].
  split_and!; [| exact Hdom | exact Hlr | exact Hdk | exact Hco].
  move=> p ts' Hp'. destruct (Harr p ts' Hp') as (ts & Hp & Heq & _).
  exists ts. split; [exact Hp | exact Heq].
Qed.

(** A tombstone step is a delete step: one type is replaced by one whose
    cells changed but whose model list did not, and (in the only use,
    [flip_cell] at one index) whose cells keep their coordinates. *)
Lemma delete_types_facts_of_flip (types : gmap loc type_state) (p : loc)
    (ts : type_state) (k : nat) (c : item_cell) :
  types !! p = Some ts -> ty_cells ts !! k = Some c ->
  delete_types_facts types
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

(** Membership in [span_ids] is exactly the (mathematical) range test. *)
Lemma span_ids_elem (v : yjs.idSpan.t) (idv : yjs.id.t) :
  toYjsId idv ∈ span_ids v ↔
    (v.(yjs.idSpan.id').(yjs.id.clientId') = idv.(yjs.id.clientId') ∧
     (uint.Z v.(yjs.idSpan.id').(yjs.id.clock') ≤ uint.Z idv.(yjs.id.clock'))%Z ∧
     (uint.Z idv.(yjs.id.clock') <
        uint.Z v.(yjs.idSpan.id').(yjs.id.clock') + uint.Z v.(yjs.idSpan.len'))%Z).
Proof.
  have HZn : ∀ w : w64, Z.of_nat (uint.nat w) = uint.Z w by move=> w; word.
  rewrite /span_ids elem_of_list_to_set list_elem_of_fmap /toYjsId.
  split.
  - move=> [o [Hid Ho]]. apply elem_of_seq in Ho.
    injection Hid => Hclk Hcid.
    split_and!.
    + word.
    + have := f_equal Z.of_nat Hclk. rewrite Nat2Z.inj_add !HZn. lia.
    + have := f_equal Z.of_nat Hclk. rewrite Nat2Z.inj_add !HZn.
      have : (Z.of_nat o < uint.Z v.(yjs.idSpan.len'))%Z by rewrite -(HZn v.(yjs.idSpan.len')); lia.
      lia.
  - move=> [Hcid [Hle Hlt]].
    exists (uint.nat idv.(yjs.id.clock') - uint.nat v.(yjs.idSpan.id').(yjs.id.clock'))%nat.
    have Hlen : (uint.nat idv.(yjs.id.clock') - uint.nat v.(yjs.idSpan.id').(yjs.id.clock')
                 < uint.nat v.(yjs.idSpan.len'))%nat.
    { have H1 := HZn idv.(yjs.id.clock'). have H2 := HZn v.(yjs.idSpan.id').(yjs.id.clock').
      have H3 := HZn v.(yjs.idSpan.len'). lia. }
    have Hge : (uint.nat v.(yjs.idSpan.id').(yjs.id.clock') <= uint.nat idv.(yjs.id.clock'))%nat.
    { have H1 := HZn idv.(yjs.id.clock'). have H2 := HZn v.(yjs.idSpan.id').(yjs.id.clock'). lia. }
    split.
    + f_equal; [by rewrite Hcid | lia].
    + apply elem_of_seq. lia.
Qed.

(** The [nat]-level form of the same test, for callers that hold a model id
    rather than a heap one. *)
Lemma span_ids_elem_nat (v : yjs.idSpan.t) (i : YjsId) :
  i ∈ span_ids v ↔
    (clientId i = uint.nat v.(yjs.idSpan.id').(yjs.id.clientId') ∧
     (uint.nat v.(yjs.idSpan.id').(yjs.id.clock') <= clock i)%nat ∧
     (clock i < uint.nat v.(yjs.idSpan.id').(yjs.id.clock')
                + uint.nat v.(yjs.idSpan.len'))%nat).
Proof.
  rewrite /span_ids elem_of_list_to_set list_elem_of_fmap. split.
  - move=> [o [-> Ho]]. apply elem_of_seq in Ho. simpl. split_and!; [done | lia | lia].
  - move=> [Hcid [Hle Hlt]].
    exists (clock i - uint.nat v.(yjs.idSpan.id').(yjs.id.clock'))%nat. split.
    + destruct i as [ci ki]. simpl in *. f_equal; [done | lia].
    + apply elem_of_seq. lia.
Qed.

(** A span splits at any interior point, which is how a delete loop grows its
    "covered so far" record one node at a time. The no-wrap premise is the
    same [w64] honesty the store's [cell_fits] provides. *)
Lemma span_ids_split (cl clk l1 l2 : w64) :
  (uint.Z clk + uint.Z l1 + uint.Z l2 < 2^64)%Z ->
  span_ids (yjs.idSpan.mk (yjs.id.mk cl clk) (word.add l1 l2))
  = span_ids (yjs.idSpan.mk (yjs.id.mk cl clk) l1)
    ∪ span_ids (yjs.idSpan.mk (yjs.id.mk cl (word.add clk l1)) l2).
Proof.
  move=> Hnw. apply set_eq => i.
  rewrite elem_of_union !span_ids_elem_nat /=.
  have Hs : uint.Z (word.add l1 l2) = uint.Z l1 + uint.Z l2 by word.
  have Hc : uint.Z (word.add clk l1) = uint.Z clk + uint.Z l1 by word.
  have Hn : ∀ w : w64, Z.of_nat (uint.nat w) = uint.Z w by move=> w; word.
  split.
  - move=> [Hcid [Hle Hlt]].
    destruct (decide (clock i < uint.nat clk + uint.nat l1)%nat) as [Hin | Hin].
    + left. split_and!; [exact Hcid | exact Hle | exact Hin].
    + right. split_and!; [exact Hcid | | ].
      * have := Hn clk. have := Hn l1. lia.
      * have := Hn clk. have := Hn l1. have := Hn l2. have := Hn (word.add l1 l2).
        have := Hn (word.add clk l1). lia.
  - move=> [[Hcid [Hle Hlt]] | [Hcid [Hle Hlt]]].
    + split_and!; [exact Hcid | exact Hle |].
      have := Hn clk. have := Hn l1. have := Hn l2. have := Hn (word.add l1 l2). lia.
    + split_and!; [exact Hcid | |].
      * have := Hn clk. have := Hn l1. have := Hn (word.add clk l1). lia.
      * have := Hn clk. have := Hn l1. have := Hn l2. have := Hn (word.add l1 l2).
        have := Hn (word.add clk l1). lia.
Qed.

(** A length-1 span denotes exactly its head id (the pre-#28 singleton case). *)
Lemma span_ids_singleton (v : yjs.idSpan.t) :
  v.(yjs.idSpan.len') = W64 1 ->
  span_ids v = {[ toYjsId v.(yjs.idSpan.id') ]}.
Proof.
  move=> Hlen. rewrite /span_ids Hlen.
  have -> : uint.nat (W64 1) = 1%nat by word.
  rewrite /= Nat.add_0_r /toYjsId.
  by rewrite (right_id_L ∅ (∪)).
Qed.

(** Appending one span adds its char ids in accumulator order. *)
Lemma span_union_snoc (vs : list yjs.idSpan.t) (v : yjs.idSpan.t) :
  ⋃ (span_ids <$> (vs ++ [v])) = span_ids v ∪ ⋃ (span_ids <$> vs).
Proof.
  rewrite fmap_app union_list_app_L /= (right_id_L ∅ (∪)).
  apply union_comm_L.
Qed.

(* ----- span <-> run-char bridge (issue #28 M4, stage C1a) ---------------- *)

(** A scanned node's span denotes exactly its run's char ids: the run's chars
    sit at the head's client with consecutive clocks from the head
    ([run_step]), which is what [span_ids] enumerates. Pure nat arithmetic on
    both sides, so no no-wrap premise is needed here (the [w64] no-wrap only
    matters for [containsId]'s range test). *)
Lemma span_ids_char_ids (idv : yjs.id.t) (len : w64)
    (h : YjsItem A) (tail : list (YjsItem A)) :
  item_id h = toYjsId idv ->
  run_step (h :: tail) ->
  length (h :: tail) = uint.nat len ->
  span_ids (yjs.idSpan.mk idv len) = char_ids (h :: tail).
Proof.
  move=> Hid Hstep Hlen.
  have Heta : forall i : YjsId, i = MkYjsId (clientId i) (clock i) by move=> [] //.
  apply set_eq => x.
  rewrite /span_ids /char_ids !elem_of_list_to_set !list_elem_of_fmap.
  split.
  - move=> [o [-> Ho]]. apply elem_of_seq in Ho. simpl in Ho.
    destruct o as [|k].
    + exists h. split; [| apply elem_of_cons; by left].
      rewrite Hid /toYjsId /= Nat.add_0_r //.
    + have Hk : (k < length tail)%nat by (simpl in Hlen; lia).
      destruct (lookup_lt_is_Some_2 tail k Hk) as [y Hy].
      exists y. split; [| apply elem_of_cons; right; by eapply list_elem_of_lookup_2].
      destruct (run_step_tail_ids h tail Hstep k y Hy) as [Hcl Hck].
      rewrite (Heta (item_id y)) Hcl Hck Hid /toYjsId /=.
      f_equal. lia.
  - move=> [y [-> Hy]]. apply elem_of_cons in Hy as [-> | Hy].
    + exists 0%nat. split.
      * rewrite Hid /toYjsId /= Nat.add_0_r //.
      * apply elem_of_seq. simpl. simpl in Hlen. lia.
    + apply list_elem_of_lookup_1 in Hy as [k Hk].
      have Hklt : (k < length tail)%nat by (eapply lookup_lt_Some; exact Hk).
      exists (S k). split.
      * destruct (run_step_tail_ids h tail Hstep k y Hk) as [Hcl Hck].
        rewrite (Heta (item_id y)) Hcl Hck Hid /toYjsId /=.
        f_equal. lia.
      * apply elem_of_seq. simpl. simpl in Hlen. lia.
Qed.

End store_value.
