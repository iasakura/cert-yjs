# Plan: split `item_cell` into a pure `ItemRun` and a location list

Status: proposal (2026-08-22), written after the spec refactor
(`docs/plan-spec-refactor.md`, PRs #143 to #151). Stage 1 in progress
(2026-08-27): `ItemRun`, its vocabulary and split surgery, `cell_run` and
the projection laws for flatten / visible / flip / split / covers / fits /
origin / disjointness are in (`item/model.v` section `item_run`,
`item/value.v`, `store/value_cells.v`, `store/value_split.v`); part 2 adds
`runs_start_at` / `runs_end_at`, `origins_resolved` (cursor indices only)
and `runs_integrate_splice`, with `origins_linked` an iff to the resolved
form plus the `node_loc` readings, and `integrate_splice` projecting onto
`runs_integrate_splice`. What remains of stage 1 is the sorted
`client_runs` theory, which needs `all_runs` over the run-granular pool and
so lands with stage 2.

## 1. The problem

`item_cell` (`src/proof/item/value.v`) is

```coq
Record item_cell := MkItemCell {
  ic_loc : loc;                 (* runtime: the node's address *)
  ic_run : list (YjsItem A);    (* model: the run of chars the node holds *)
  ic_deleted : bool;            (* model: the tombstone bit *)
  ic_parent : loc;              (* runtime: the address of the node's yType *)
}.
```

It mixes two kinds of data. Reasoning about runs (their flatten, their
clock ranges, what a split or a tombstone does to them) is pure and never
needs an address; reasoning about which heap node holds which run is a
heap fact. Because the one record carries both, every pure definition over
cells sees locations, and every spec about a node's run drags the
location along:

- `cells_range_disjoint` identifies distinct cells by `ic_loc c1 ≠ ic_loc c2`,
  so a statement about clock ranges depends on addresses;
- `pool_invs` holds `NoDup (ic_loc <$> all_cells types)`, a heap fact, next
  to three pure facts;
- `node_loc cells k`, `ic_loc <$> client_run types client`, `fresh_loc`,
  `cell_pr` (the clock-then-location sort key), `split_cells cells k o r_loc`
  (the split takes the new node's address as a pure argument) all thread
  addresses through the value layer;
- `ic_parent` duplicates information the pool already has (a cell is in
  exactly one type's list) and has to be kept coherent
  (`own_ytype_cells`'s `Hcpar`, `cell_ends_at types parent l d`, the
  `ic_parent` clauses of `repair_parent` / `origins_split`);
The pool's key (the yType's address in `gmap loc type_state`) is a
different matter: it is only a name for the type, no pure lemma computes
with it (`all_cells` reads the values, `registry_coh` relates keys to root
names), so it stays.

Footprint today: `item_cell` / `ic_*` appear in 21 files; the heavy ones are
`splitNode.v` (250 field uses), `value_cells.v` (90), `Integrate.v` (75),
`repair.v` (80), `text/Delete.v` (73), `item/heap.v` (85).

## 2. The target

### 2.1 Pure layer (no `loc` anywhere)

```coq
(* item/model.v *)
Record ItemRun := MkItemRun {
  run_items : list (YjsItem A);   (* nonempty, consecutive clocks: run_wf *)
  run_deleted : bool;
}.

(* ytype/model.v: a type's model is its list of runs and its item list *)
Record type_model := MkTypeModel {
  tm_runs : list ItemRun;
  tm_arr : list (YjsItem A);      (* = runs_flatten tm_runs, the document *)
}.

(* store/model.v: the pool, keyed by the yType's address as today; the key
   names the type and is never computed with *)
Definition pool := gmap loc type_model.
```

Everything that is pure today is restated over `ItemRun` and indices:

| today (over `item_cell`) | target (over `ItemRun`) | note |
|---|---|---|
| `run_head`, `run_flatten`, `num_visible`, `cell_unit`, `cells_model`, `cells_repr` | same names over `list ItemRun` | drop `ic_loc` / `ic_parent` |
| `cell_covers c d`, `cell_covers_clock`, `cell_fits`, `cell_origin_clk`, `cell_client` / `cell_clock` / `cell_le` | same over `ItemRun` | unchanged bodies |
| `cells_range_disjoint pool` (distinct cells by `ic_loc ≠`) | `runs_disjoint runs`: `∀ i j, i ≠ j → runs !! i = Some r → runs !! j = Some r' → same client → ranges disjoint` | index-based, which is what `wp_getNodeIndex_raw` already assumes |
| `pool_invs types` = fits ∧ `NoDup locs` ∧ disjoint ∧ origin_clk | `pool_invs p` = fits ∧ `runs_disjoint (all_runs p)` ∧ origin_clk | `NoDup` of locations moves to the heap layer |
| `all_cells types : list item_cell` | `all_runs p : list ItemRun` | |
| `client_run types client` (sorted by `cell_pr` = (clock, loc)) | `client_runs p client : list ItemRun` sorted by clock | with `runs_disjoint` the clocks are distinct per client, so the location tie-break is unnecessary |
| `split_cells cells k o r_loc`, `split_cell_left / right` | `split_runs runs k o` | the new node's address is a heap matter |
| `flip_cell`, `set_deleted` | `flip_run` | |
| `node_loc cells k` | gone from the pure layer; see `ls !! k` below | |
| `cell_starts_at types parent l d`, `cell_ends_at` | `run_starts_at p parent k d`, `run_ends_at p parent k d`: the `k`-th run of the type at `parent` | the node is indexed, not addressed |
| `fresh_loc l types` | heap layer only | |
| `pool_cell_covers types c d` | `pool_run_covers p parent k d` | |
| `origins_linked cells arr input lft rgt` | `origins_resolved runs arr input kL kR` (cursor indices only) | the locs `lft` / `rgt` come from `ls !! kL`, `ls !! kR` in the spec |
| `integrate_splice cells arr item_l run parent cells' arr'` | `integrate_splice runs arr run runs' arr'` | the address of the new node is a heap fact |
| `repair_parent bind opn ocL ocR p_t`, `origins_split`, `origins_covered` | over the type's address and run indices (`ic_parent c` becomes "the type whose list holds the run") | |
| `split_types_update_rel`, `repair_types_update_rel`, `delete_types_update_rel`, `cells_within`, `live_refine`, `dead_chars_kept`, `ids_tombstoned`, `delete_set_tombstoned` | same over `pool` / `list ItemRun` | bodies lose the `ic_loc ≠ ic_loc w` clauses, which become "index ≠ k" |

### 2.2 Heap layer: the location list

One predicate relates a type's heap nodes to its runs, in the form the
user proposed:

```coq
(* item/heap.v: the DLL, as a list of node addresses paired with the runs they hold *)
Fixpoint own_dll (dq : dfrac) (l last prev next : loc)
    (ls : list loc) (runs : list ItemRun) : iProp Σ :=
  match ls, runs with
  | [], [] => ⌜l = next ∧ last = prev⌝
  | lc :: ls', r :: runs' =>
      ⌜l = lc ∧ lc ≠ null⌝ ∗
      own_item_node lc dq (input_of_run r) (run_deleted r) prev ∗   (* F2a of the spec refactor *)
      own_dll dq (next of lc) last lc next ls' runs'
  | _, _ => False
  end.

(* ytype/heap.v *)
Definition own_ytype (parent : loc) (dq : dfrac) (ls : list loc) (tm : type_model) : iProp Σ := …

(* store/heap.v: the pool's heap side; [locs] holds each type's node addresses *)
Definition own_type_pool (dq : dfrac) (locs : gmap loc (list loc)) (p : pool) : iProp Σ :=
  [∗ map] parent ↦ tm ∈ p, ∃ ls, ⌜locs !! parent = Some ls⌝ ∗ own_ytype parent dq ls tm.
```

`own_item_node l dq input deleted prev` is the item-node predicate of the
spec refactor's F2a (the struct value and the `yjs.id.t` origin cells are
existential inside it; `is_origin_id` is stated over `option YjsId`). This
is where step 3 of `docs/plan-spec-refactor.md` lands: both changes rewrite
the same per-node payload of `own_dll`, so they are done together.

The heap-only facts: `NoDup (concat (map_to_list locs).*2)` (one node is in
one type at one index) and `length ls = length (tm_runs tm)` per type,
bundled as `locs_wf locs p`, living in `own_type_pool`, not in `pool_invs`.

### 2.3 Specs

A helper that returns a node names it through the location list:

```coq
Lemma wp_store__GetNode (s : loc) (idv : yjs.id.t) (st : store_state) :
  {{{ own_store_struct s st }}}
    s @! (go.PointerType yjs.store) @! "GetNode" #idv
  {{{ (l : loc) (ok : bool), RET (#l, #ok);
      own_store_struct s st ∗
      ⌜if ok then ∃ parent k, pool_run_covers (ss_pool st) parent k (toYjsId idv) ∧
                              ss_locs st !! parent ≫= (.!! k) = Some l
       else ∀ parent k, ¬ pool_run_covers (ss_pool st) parent k (toYjsId idv)⌝ }}}.
```

(`store_state` carries `ss_locs : gmap loc (list loc)` and `ss_pool : pool`
in place of today's `ss_types`; the whole-store shape of the specs is
unchanged.)

The pure part (`pool_run_covers`, `pool_invs`, `split_runs`, …) never
mentions `locs`; the heap part relates indices to addresses only through
`locs`. `wp_store__splitNode` returns `rloc` with `locs' = insert_at parent (k+1) rloc locs`
and `p' = split at (parent, k, o)`; `wp_Store__Integrate` takes the two cursor
indices and the item's address, and returns `locs'` / `p'`.

The public layer (`is_Text`, `own_store`, `own_ytype` at its model,
`is_Doc`) is unchanged: it already hides cells.

## 3. Migration, in compiling stages

1. **Pure theory first, as a projection.** Add `ItemRun`, `cell_run : item_cell → ItemRun`,
   and the loc-free definitions (`runs_flatten`, `runs_disjoint`, `split_runs`,
   `flip_run`, `run_starts_at`, …) next to the existing ones, with projection
   lemmas (`run_flatten cells = runs_flatten (cell_run <$> cells)`,
   `cells_range_disjoint (all_cells types) ↔ runs_disjoint (all_runs types)` given
   `NoDup` of locations, `split_cells cells k o r = …` projects to `split_runs`).
   Nothing else changes; the new theory is checked in isolation.
   Files: `item/model.v`, `item/value.v`, `store/value_cells.v`, `store/value_split.v`.
2. **The location map.** Replace `types : gmap loc type_state` by
   `p : pool` (same keys, loc-free values) plus `locs`; `own_type_pool`,
   `own_item_map` (`ic_loc <$> client_run` becomes the client's sublist of `locs`),
   `own_store_items` take `(locs, p)` and `store_state` carries them as
   `ss_locs` / `ss_pool`. Specs of the internal helpers are restated in the
   2.3 shape; proofs keep their cell
   lists through `cell_run` / `ic_loc` projections until stage 3.
   Files: `store/heap.v`, every `store/*.v` WP file, `text/Insert.v`,
   `text/Delete.v`, `doc/GetOrCreateText.v`.
   If the Go decomposition of the store cores is ever done
   (`parent.integrate(item)` as a `yType` method, a named `itemIndex` type
   with `addNode`, likewise split and delete), this is the stage for it: the
   index model is restructured here anyway and each core's spec becomes the
   whole predicate of its smaller receiver. Decided 2026-08-25: not required;
   the `#[local]` stepping-stone discipline (CLAUDE.md "Spec shape") covers
   the cores. Update 2026-08-26: `addNode` and `deleteNode` became
   footprint-visible free functions without waiting for this stage; only
   the `parent.integrate(item)` split remains optional here.
3. **The node payload.** `own_dll` over `(ls, runs)` with `own_item_node`;
   `is_origin_id` over `option YjsId`; the three `item` method specs over
   `own_item_node` (spec refactor step 3). The borrow lemmas
   (`own_dll_acc`, `own_dll_lookup_acc`, `own_dll_update_gen`, `own_dll_split`)
   hand out `own_item_node` instead of `itemVal` plus ten equations.
   Files: `item/heap.v`, `item/*.v`, `ytype/heap.v`, `ytype/findPos.v`,
   and every proof that opens a borrow (`Integrate.v`, `splitNode.v`,
   `deleteRange.v`, `repair.v`, `text/Insert.v`, `text/Delete.v`).
4. **Delete `item_cell`.** Remove the projections and the old definitions.
   Fold `ty_arr` away at the same time: `tm_arr = runs_flatten tm_runs`
   always holds (`cells_repr`), so `type_model` becomes the run list and the
   document list is derived. Every spec that says `ty_arr` says
   `runs_flatten` instead, and `integrate_splice` loses its second splice
   (`arr' = take … ++ run ++ drop …`) and both length bounds: it is
   `runs' = insert_at idx run runs`, the location of the new run living in
   the heap layer.
5. **Run-granular model (issue #105).** The remaining awkwardness of the
   Integrate spec is rocq-yjs's one-char `YjsItem`: a wire item explodes into
   `length (in_content input)` items, `toItem` resolves only the head, and
   `run_denotes input newItem run` (head id and origins, length) plus the
   premise `integrate_all (ops_of_input input (explode …)) arr = Some arr'`
   restate the rest. With a run-level item (`id`, `origin`, `rightOrigin`,
   `content : list A`) and a run-level `integrate_run`, the premise is one
   `toItem input runs = Some newRun`, the post is
   `runs' = integrate_run newRun runs` (no `∃ idx`, no `run_denotes`), and
   the store post is `own_store_struct s (st <| ss_types := <[parent :=
   store_integrate …]> … |>)`. Upstream work in rocq-yjs: define the run
   model, prove `runs_flatten (integrate_run r runs) = integrate_all
   (explode r) (runs_flatten runs)` so the per-char convergence theorems
   transfer. Done after stage 4, when there is one run list to refine.
   Representation candidate (2026-08-28): a run-level item is
   `YjsItem (list A)` paired with the tombstone bit (the bit is not a model
   notion, as `text_snapshot`'s `list (YjsItem A * bool)` already shows).
   On `run_wf` runs this is an isomorphism with stage 1's `ItemRun` (a run
   is its head's origin / rightOrigin / id plus its contents), it makes
   well-formedness structural, and because rocq-yjs's order theory never
   reads the content, instantiating the generic `integrate` /
   `YjsArrInvariant` / convergence theorems at `list A` gives the
   run-granular algorithm and its theorems outright; the flatten bridge
   (`run_wf_of_chain`'s chain construction) is the one new proof. Not used
   in stages 1 to 4 on purpose: there `cell_run` stays a restriction and
   the projections definitional, keeping the explode bridge out of them.

Stages 1 and 2 are where the user-visible improvement is (loc-free pure
lemmas, specs over `(p, locs)`); stage 3 is the part shared with the spec
refactor's step 3 and is the most expensive (it touches every DLL borrow);
stage 5 is the only one that changes rocq-yjs.

## 4. Cost

Rough size, from the footprint above: stage 1 ~600 lines of new pure theory
(mostly restatements with projection proofs); stage 2 rewrites every store
spec statement and the pool plumbing of ~12 WP files (the proofs mostly
survive through the projections); stage 3 touches ~40 borrow sites and the
three item method proofs. Comparable to the whole spec refactor (steps 1 to
7, PRs #143 to #151), and best done after those PRs are merged so it does
not stack on eight unmerged branches.

## 5. Open questions for the owner

- The pool keeps the yType address as its key (decided 2026-08-22). The
  key is only an index for the pure theory; it is the address because the
  heap side (`own_type_pool`'s big-sep, `item.parent` in Go) identifies a
  type by its pointer, so sharing the identifier saves a second map. Keying
  by root name would remove the last `loc` from the pure pool at the cost of
  a registry indirection, for no proof benefit.
- `own_item_map`'s per-client slices store node addresses in clock order,
  so its model is naturally a list of addresses; with `locs` keyed by type
  and `client_runs` by client, the slice's model is `client_locs locs p client`
  (a derived list), which is fine but means the item map's model is
  computed, not stored.
- `ty_arr` is folded away in stage 4 (decided 2026-08-23): the double
  bookkeeping of cells and their flattened document is what makes
  `integrate_splice` state the same splice twice.
