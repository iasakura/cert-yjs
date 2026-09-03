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
`runs_integrate_splice`. The sorted `client_runs` theory
landed with stage 2 part 1 (`client_runs` over `pool`, `client_run_runs`),
closing stage 1's pure side. Stage 2 part 2 (merged, PR #160):
`store_state_runs` / `own_store_runs` (the cell-level state existential)
and the derived `_runs` specs for `GetNode` and `splitNode`, each the
cell-level spec plus pure projection transport. Part 3 (2026-08-29): the
run-level split step record `pool_after_split` (with `pool_run_starts_at`
/ `pool_run_ends_at`, `runs_live_refine` / `runs_dead_kept`,
`runs_within`), its transport `split_types_update_rel_to_pool`, the slot
translations (`cell_starts_ends_at_to_run` and kin, over
`all_cells_same_loc_same_slot`) and the derived
`wp_store__splitAtAndGetLeft_runs` / `Right_runs`. The position clauses
(which half of the split sits at which slot) deliberately stay out of
`pool_after_split`: they are address-map facts, so the specs state them on
`sr_locs`. Part 4 (2026-08-29): `Integrate` at run granularity:
`pool_run_clock_below` with its cell read-back
`pool_run_clock_below_to_cell`, `loc_at` (`node_loc` over a bare address
list), `runs_integrate_splice_at` (the cursor-explicit core of
`runs_integrate_splice`), `integrate_locs` and
`integrate_splice_runs_locs` (the run and the address-list halves of one
splice at one shared cursor), and the derived `wp_store__Integrate_runs`.
Part 5 (2026-08-29): the registry family: `pool_after_repair`
(`repair_types_update_rel` loc-free, the `pool_after_split` clauses minus
the split-spot ones) with its transport `repair_types_update_rel_to_pool`;
`pool_lookup_or_create` + `registry_lookup_or_create_to_pool`; the repair
contract at run granularity (`pool_origins_covered` /
`pool_repair_parent` / `pool_origins_split` over origin slots `(q, k)`,
with `origin_slot_names` naming the cells and the covered / parent / split
translations); and the derived `wp_store__getOrCreateYType_runs` /
`wp_store__repair_runs`. `pool_origins_split` deliberately drops
`origins_split`'s left-address identity (`lft = ic_loc c0`); add it on
`sr_locs` if the `applyUpdate` conversion needs it. `hasNode` converts
with `applyUpdate` (its premise `registry_models` is DocModel-level).
Part 6 (2026-08-29): the delete path: `pool_after_delete`
(`delete_types_update_rel` loc-free) with its transport
`delete_types_update_rel_to_pool`; `ids_tombstoned_runs` (item/model.v,
the loc-free `ids_tombstoned`) with `ids_tombstoned_runs_of`
(value_live.v); and the derived `wp_store__deleteRange_runs` /
`wp_store__applyDeleteSpans_runs`. The `applyUpdate` / `hasNode` conversion is DEFERRED to stage 3:
their public spec is `own_store`-level (ghost certificates, and
`registry_models` sits inside `own_store`'s invariant), so their run form
belongs with the run-granular `own_store`; the pure pieces are mechanical
(`registry_models`: `ty_arr` to `tm_arr`; `apply_live_refine` /
`cells_within_or_from` mirror `runs_live_refine` plus a fresh disjunct).
That closes the stage-2 derived-spec program. Stage 3a (2026-08-29,
started): `own_item_node` (item/heap.v, the F2a node predicate of
docs/plan-spec-refactor.md step 3: struct and origin cells existential,
pinned to the wire item, flag byte pinned so Countable is free), the
three item method specs over it (`wp_item__Len_node` /
`wp_item__Deleted_node` / `wp_item__Indexable_node`) and
`own_linked_item_as_node` (store/heap.v): the payload `own_dll` moves
onto in the borrow rewrite. Stage 3b groundwork (2026-08-29):
`items_string` (with `_app` / `_explode`) moved from ytype/value.v down
to item/model.v, `input_of_run` (the wire item a run denotes), and the
node-level borrow forms `own_dll_lookup_acc_node` /
`own_dll_update_gen_node` (item/heap.v): each hands the k-th node out
WHOLE as `own_item_node` at `input_of_run (cell_run c)` instead of
`itemVal` plus ten equations; the update wand takes the node back at any
tombstone bit. The content pin travels through `items_string_explode`,
and the restore direction needs no new facts because the run is
unchanged through a borrow. `own_dll_acc_node` and the exposed spelled-length pin
`length (items_string (ic_run c)) = length (ic_run c)` landed with the
groundwork. REASSESSED 2026-08-30: converting the existing borrow SITES
(text/Delete.v's flip loop was the candidate) is a net loss while
`own_dll` is cell-level: goose field reads and the tombstone store need
the raw struct, so a site opens the node anyway and each of the four
wand returns pays a ~5-line node re-pack against the old one-line
eq_refl wand. The node borrows pay off when `own_dll` itself is
primitive over the address list and the runs. So the next step is the
stage-3 core: `own_dll_runs dq parent l last prev next ls runs` (per
section 2.2, payload one `own_item_node` at `input_of_run r` per node,
plus the per-run PER-CHAR pin `content <$> run_items r =
explode (items_string (run_items r))`, which the wire view alone cannot
recover and today's explode pin carries), with the fold/unfold bridge to
the cell-level `own_dll` (under per-cell parent coherence) that lets
files convert one at a time, and its structural laws (app, then acc /
insert_middle / split forms as conversions need them). Landed 2026-08-30
(PR #167); on top of it, `own_ytype_runs` is REDEFINED primitively over
`own_dll_runs` (a heap `yType` heading the run-granular DLL, `len` =
`runs_visible`, the document list = `runs_flatten`), with
`own_ytype_runs_intro` reproven through `own_dll_as_runs`, the new
elimination `own_ytype_runs_as_cells` re-materializing cells as
`cells_of_locs_runs` (the zip of the addresses with the runs,
item/value.v, laws `_run` / `_loc` / `_parent`), `own_dll_runs_length`
aligning the spine's two lists, and the `own_item_node` /
`own_dll_runs` Timeless instances beside the other heap instances
(store/heap.v). The pool elimination landed on top:
`types_of_locs_pool` (value_cells.v, the cell registry an address map
and a run pool determine, round-tripping under matching domains and
counts) and `own_type_pool_runs_to_cells` (store/heap.v, via the generic
`big_sepM_map_imap_total`, algebra.v), the converse of
`own_type_pool_runs_of`. On top of that, `own_store_runs` is
REDEFINED primitively (2026-08-30): `own_store_struct` at
`state_of_runs` (the registry re-materialized as `types_of_locs_pool`)
plus `locs_aligned`; `own_store_runs_as_state` folds and unfolds the old
"some cell-level state projecting to `str`" reading, and the nine
derived `_runs` proofs consume it through one rewrite at entry and exit.
`(sr_locs, sr_pool)` is now THE store state of the run-granular layer;
what remains cell-level lives inside `own_store_struct`'s field
predicates and goes at stage 4. SYNTHESIS (2026-08-30): stage 3's spec
surface is COMPLETE with this. The public layer (`own_store`'s
`(c, h, m, pend)` model, `is_Text`, `is_Doc`) is already cell-free, as
section 2.3 says, so `applyUpdate` / `hasNode` need no spec conversion
at all (the stage-2 deferral resolves to "nothing to do"); every
cell-keyed conjunct inside `own_store` (`own_store_struct`, the seq
auth over `ty_arr`, `registry_models`, the counter bound,
`own_delete_set`'s pool argument) is existential and dies with stage
4's internal rewrite. Stage 4's order: first the `own_dll_runs`
structural toolkit (app, insert_middle, split, the borrow laws at run
granularity, mirroring the cell ones), then rewrite the store WP files
one at a time onto `(ls, runs)` (deleting their `own_dll` use), then
the field predicates (`own_item_map` at a per-client address theory,
`own_delete_set` over runs), and last delete `item_cell` and fold
`ty_arr`. The toolkit landed 2026-08-30 (#167 commits 5 to 8: `_app`,
`_insert_middle`, `_split` with its per-char premises discharged by
`run_per_char_split_left` / `_right`, and the `_lookup_acc` / `_update`
borrows). Scoping of the first file rewrite (splitNode.v, ~2300 lines):
its ~20 `split_pool_*` transports map as follows. Already run-level:
`runs_within` (subrange), `runs_live_refine` / `runs_dead_kept`,
`split_runs_flatten` / `split_runs_visible`, `run_wf_take` / `_drop`
(the halves' well-formedness). MISSING pure lemmas, to write first:
`split_runs_fits` / `split_runs_disjoint` / `split_runs_origin_clk`
(run_pool_invs survives one split; the cell proofs `split_pool_fits` /
`_rangedisj` / `_originclk` are the templates, minus the address
reasoning), and the heap freshness law `own_dll_runs_fresh` (a fully
owned node's address is outside a segment's `ls`, replacing
`split_pool_locdup`). `split_cell_cover`'s role is played by
`pool_after_split`'s coverage clause. All of these landed (#167 commit
10, as `run_pool_invs_split` and kin).

DECISION 2026-08-30 (owner): the per-client item index at run
granularity goes the MATERIALIZATION route: the index stays
`client_run` over `types_of_locs_pool locs p` (no new sort theory now);
`client_run` itself is re-implemented at run granularity only at the
item_cell deletion step, behind one bridge. Consequently the stage-4
step order corrects to: the direct body rewrites would be 80 percent
textual copies while the index and the goose stepping stay cell-shaped
under materialization, so the CELL SPECS AND BODIES STAY until the
final coordinated cutover; the remaining pre-cutover work is to
re-thread the DLL-TOUCHING proof internals onto the run primitives
through the bridges (`own_dll_as_runs`, the `_node` borrows), file by
file, smallest first (`ytype/findPos.v`, `ytype/Text.v`,
`text/Delete.v`'s flip loop, then the store cores), so that at the
cutover the `own_dll`/`item_cell` deletion is a definition swap plus
mechanical cleanup instead of a proof rewrite. DONE 2026-08-30 (#167
commits 13 to 24): every WP-file window now goes through the node
toolkit (`own_dll_acc_node` / `_lookup_acc_node` / `_update_gen_node` /
`_lookup_acc_2_node`, `own_dll_cons_node_unfold` / `_fold`,
`own_dll_insert_middle_node` / `own_dll_split_node`,
`own_item_node_not_null`; `run_per_char_intro` discharges fold premises
from explode couplings). Converted: `findPos`, `ytype/Text`,
`text/Delete`, `text/Insert`, `store/deleteRange`, `own_type_pool_acc`,
all of `store/Integrate` (scan, pairwise, splices, cursor reads), and
`store/splitNode` end-to-end. The only cons-layout proofs left are
layer-internal (`own_dll_fractional` and the toolkit's own proofs),
re-proved over the runs bridge at the cutover.

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

## 6. Cutover execution order (added 2026-08-30, after the re-threading)

With the re-threading done, the coordinated cutover proceeds bottom-up in
six compiling stages. Scaffolding (compat wrappers) is allowed DURING the
cutover and dies in C6; nothing of it survives.

- **C1, item layer** (LANDED 2026-08-30, full build green; the original wording had a flaw:
  a parentless wrapper cannot synthesize the run spine's parent).
  `own_dll` GAINS the parent parameter and is defined as
  `⌜∀ c ∈ cells, ic_parent c = parent⌝ ∗ own_dll_runs dq parent …
  (ic_loc <$> cells) (cell_run <$> cells)`. The old cons Fixpoint and
  all its laws survive renamed `own_dll_cells_layout(_*)` (scaffolding,
  deleted at C6); `own_dll_unfold_layout` is the isomorphism, and a
  wrapper-level suite re-exports every consumer-facing law with the
  parent IMPLICIT, so the ~40 borrow call sites compile unchanged; only
  sites that STATE `own_dll` spell the parent, and the splice calls
  discharge the new parent-coherence premises. `item/value.v` keeps
  `item_cell` and the projections for now (they feed the wrapper).
REVISION 2026-08-30, after C1 landed: C2 to C4 collapse into C6. The
run-side definitions they would make primitive already exist with
bridges (`own_ytype_runs`, `own_type_pool_runs`, `own_store_runs`,
`store_state_runs` with `state_runs_of`), and flipping which side is
the Definition buys nothing before C5: consumers keep the cell spelling
either way, and a function-valued `ss_types` compat is not transparent
enough (the `types_of_locs_pool` round-trips are propositional, so
every proof that constructs a state and reads `ss_types` back by iota
would need rewriting). The remaining work before C6 is C5 preparation:
the pool-level analogues of the setter-spec relations
(`split_types_update_rel`, `repair_types_update_rel`,
`delete_types_update_rel`, `registry_lookup_or_create`,
`registry_models`, `fresh_loc`) must be complete, and each WP file's
vocabulary substitution table written; then C5 restates the specs at
`(locs, pool)` file by file and C6 deletes the cell side.

- **C2, ytype layer** (collapsed into C6, see above). `own_ytype_runs` (already primitive) becomes THE
  `own_ytype_cells` replacement: the cell-shaped predicate becomes a
  wrapper over it, `type_state` callers start moving to `type_model`
  (`ty_arr` reads become `runs_flatten` through `cells_repr`).
- **C3, value files.** `value_cells.v` / `value_split.v` / `value_live.v` /
  `value_span.v`: the run/pool side (already present: `pool`, `all_runs`,
  `run_pool_invs`, `pool_run_covers`, `pool_origins_*`, `split_runs`
  analogues, the `_to_pool` / `_to_cell` transports) becomes primary;
  cell-shaped definitions become wrappers or die where unused.
- **C4, store heap.** `own_store_struct`'s state moves to
  `(ss_locs, ss_pool)` (today's `own_store_runs` reading becomes the
  definition); `own_type_pool` over `(locs, p)`; `own_item_map`'s
  per-client slice model becomes `client_locs locs p client`;
  `own_delete_set` takes runs.
- **C5, WP files, one at a time.** Specs restated in the 2.3 shape
  (indices plus `locs`), proofs transported; the windows already speak the
  node language, so each file is vocabulary substitution plus the
  entry/exit rewrite between the wrapper and the primitive. Order by
  footprint, smallest first: `doc/GetOrCreateText`, `ytype/Text`,
  `ytype/findPos`, `applyUpdate`, `deleteRange`, `GetNode`, `text/Insert`,
  `text/Delete`, `repair`, `Integrate`, `splitNode`.
- **C5/C6 per-file map** (added 2026-08-30). Specs already staged at
  `(locs, pool)`: `GetNode`, `splitNode` / `splitAtAndGetLeft` /
  `_Right`, `deleteRange` / `applyDeleteSpans`, `getOrCreateYType` /
  `repair`, `Integrate` (the nine `_runs` forms, today derived from the
  cell specs by one rewrite at entry and exit; the cutover flips the
  derivation). Relations: the setter specs' update relations all have
  pool-level forms with transports (`split_types_update_rel_to_pool`,
  `repair_types_update_rel_to_pool`, `delete_types_update_rel_to_pool`,
  `pool_lookup_or_create`, `pool_registry_coh`, `pool_registry_models`,
  `locs_fresh`). Internals: every DLL window already speaks the node
  language (the re-threading), so per file the conversion is the pure
  vocabulary of section 2.1's table plus the index materialization
  (`client_run` re-implemented at run granularity behind its bridge, per
  the owner decision). Heavy files by footprint: `splitNode` (~670 uses),
  `value_cells` (~450), `Integrate` (~290), `value_split` (~280),
  `repair` (~190); the sixteen `<| ss_types := … |>` setter sites
  (repair 7, splitNode 5, deleteRange 2, applyUpdate 1, Integrate 1)
  are where the state-update spelling changes by hand.
  PROGRESS 2026-09-02: `ytype/findPos`, `ytype/Text`, `ytype/newYType`,
  `deleteRange` / `applyDeleteSpans` (and `deleteNode`) and the
  `applyUpdate` drain core (`wp_store__applyUpdate_unlocked`, over
  `own_store_runs`, stepping by `runs_within_or_from` /
  `runs_apply_live_refine`; its `own_store` wrapper lifts and lowers) and
  `splitAtAndGetLeft` / `splitAtAndGetRight` (from `GetNode_runs` +
  `splitNode_runs`, reporting the index-explicit `pool_split_left_step` /
  `pool_split_right_step`) and `repair` (from the split helpers and
  `getOrCreateYType_runs`; the two origin slots are kept apart by
  `own_store_runs_covers_unique` and carried across each other's split by
  `pool_split_step_other_slot`) and `integrateDecoded` (bound / unbound /
  creation cases; the origins resolve to slots through the flatten,
  `runs_flatten_lookup_run`) are proved directly at `(locs, pool)`; the
  cell-level `repair` / `integrateDecoded` and their locals are deleted;
  `hasNode` / `originArrived` / `depsArrived` are direct too (the model
  agreement `docm_runs_agree` replaces `docm_cells_agree`); the
  run-count clause of `pool_after_split` / `pool_after_repair` was dropped
  (no consumer); the cell-level `applyDeleteSpans` is now
  DERIVED from the run-granular proof (for the `own_store` wrapper), the
  reverse of the original derivation. The store-level recipe: open
  `own_store_runs`, lift the pool (`own_type_pool_runs_of`), run the
  node-level core, lower it (`own_type_pool_runs_to_cells`) and re-close
  through the materialization laws (`types_of_locs_pool_insert`,
  `cells_of_locs_runs_flip`), so the cell-level pool lemmas apply verbatim
  until C6 swaps the definition.

  PROGRESS 2026-09-03: `Store.Integrate` is direct at `(locs, pool)`:
  `wp_itemPtrEqual_runs`, `wp_scanConflicts_runs` (over
  `integrate_loop_inv_runs`), `wp_findIntegrationLeft_runs`, the
  DLL-splice core `wp_Store__integrateCore_aux_runs` /
  `wp_store__integrateCore_runs` (the splice through `own_dll_runs_app`,
  `own_dll_runs_cons_unfold` / `_fold`, `own_dll_runs_insert_middle`; the
  post is `runs_integrate_splice_at` + `integrate_locs` + `run_denotes`)
  and `wp_store__Integrate_runs` (the parent's `own_ytype_runs` borrowed
  out of the cell pool through `own_ytype_runs_intro` / `_as_cells` so the
  cell `wp_addNode` and `pool_invs_integrate` still apply; the registry
  re-materializes by `types_of_locs_pool_insert_both`). The cell
  `wp_Store__Integrate` is DERIVED from it (for `text/Insert`), and the
  cell scan stack, `integrate_loop_inv`, `integrate_splice_runs(_locs)`
  and the cell prefix-sum laws it consumed are deleted. The
  `clientId < 2^64` premise of `wp_store__Integrate_runs` is gone (it is
  the linked item's own id).

  PROGRESS 2026-09-04: `store.splitNode` is direct at `(locs, pool)`. The
  Go gained the free function `splitItem(n, diff)` (the DLL half, y-octo's
  `Item::split_at`; `splitNode` keeps the per-client run-list insertion), so
  the split has a node-level spec `wp_splitItem_runs` over `own_ytype_runs`
  (the surgery through `own_dll_runs_app` / `own_dll_runs_cons_unfold` /
  `own_dll_runs_split`, one proof for both neighbour cases) and the store
  wrapper `wp_store__splitNode_runs` composes it with the item-map surgery
  written once (the two duplicated cell branches are gone; the pool
  bookkeeping `pool_invs_split` / `split_pool_perm` applies through
  `cells_of_locs_runs_split`). The cell `wp_store__splitNode` is DERIVED
  from it (for `text/Insert` / `text/Delete`); the cell
  `splitAtAndGetLeft` / `Right`, their `_range` locals and the split-pool
  laws only they consumed are deleted.

  PROGRESS 2026-09-04 (text): `Text.Insert` and `Text.Delete` are direct at
  `(locs, pool)`. Both keep `own_store_runs` whole and reach into it only
  through borrows: `own_store_runs_ytype_acc` (the type for `findPos` and
  the `len` read), `own_store_runs_node_acc_links` (a node with its links
  and flag byte, for `Indexable` / `Len` / the right-link walk),
  `own_store_runs_clock_acc` / `_client_acc` (the store's clock bump and
  client read). The store steps are the run-level specs
  (`wp_store__splitNode_runs`, `wp_store__Integrate_runs`,
  `wp_deleteNode_store_runs`, now public and shared with
  `applyDeleteSpans`), so the Go `Text.Delete` loop tombstones through
  `deleteNode(cur)` instead of an inline flag write plus `len` update
  (y-octo `ListType::remove_after` -> `delete_item`). The delete-set ghost
  still lives at cells: it follows the materialized
  `cells_of_locs_runs inner ls runs` through `cells_of_locs_runs_split` /
  `_flip` and the registry is lowered at Unlock by
  `types_of_locs_pool_ext_insert`. The cell `wp_Store__Integrate` and
  `wp_store__splitNode` and the cell laws only the text layer consumed
  (`split_pool_subrange`, `split_cells_length` / `_lookup_right`,
  `own_dll_update_gen_node`, `node_loc_lt_not_null(_layout)`,
  `num_visible_flip_run`, `cells_repr_update_run`, `find_pos` /
  `find_pos_runs_of`, `cell_kp_flip`, `wp_item__Indexable_node`,
  `linked_item_fresh_ytype`, `node_loc_splice_ge`,
  `run_flatten_take_length_le`) are deleted.

- **C6, delete the scaffolding.** `item_cell`, `cell_*`, `cells_of_locs_*`,
  the wrappers, `node_loc`, `ty_arr` (folded: `tm_arr = runs_flatten`),
  and the `_to_cell` transports are removed; `own_dll_fractional` and kin
  are re-proved over the run Fixpoint (mechanical inductions).

- **C6 execution order** (added 2026-09-04, after the text layer landed).
  Every WP spec is now stated at `(locs, pool)`, but the proof BODIES still
  open `own_store_runs` into the cell registry (`types_of_locs_pool`) and do
  their bookkeeping with the cell laws, and three invariants are still
  cell-shaped (`own_item_map`'s `client_run`, `own_delete_set`'s
  tombstoned-cells clause, `store_inv` / `types_frag`'s `types`). So C6 is
  five compiling slices, one PR each:
  - **C6-1, run-level invariants.** `client_locs` re-implemented over the
    `(address, run)` entries of `(locs, pool)` (merge-sorted by head clock;
    the bridge to `ic_loc <$> client_run (types_of_locs_pool locs p)` is a
    lemma under alignment plus same-client clock uniqueness, not the
    definition); `own_item_map_runs mref dq locs p` over it, with its
    transition laws proved loc-free (append at the newest clock for
    `addNode`, the right half inserted for a split, unchanged by a flip and
    by a type creation); `own_delete_set` over `all_runs p`
    (`delete_set_tombstoned` at runs, refined along `runs_within`);
    `run_pool_invs` / `locs_wf` / `pool_registry_coh` / `pool_registry_models`
    already exist.
    PROGRESS 2026-09-04: landed. `pool_entries` / `entry_kp` /
    `kp_clkloc` / `kp_client_locs` (value_cells), the four reshuffle laws
    proved once at the key level, `client_locs` over the entries with
    `client_locs_of` / `client_run_kp_locs` / `entries_kp_of` /
    `entries_kp_to_cells` as the bridges; `own_item_map_kp` (heap, with
    `own_item_map_as_kp`, `own_item_map_kp_keys_perm`) and
    `own_item_map_runs` (`_of` / `_to_cells`); `delete_set_tombstoned_runs`
    (model) with `own_delete_set_runs` and its transports, bridged by
    `own_delete_set_as_runs`. The witness law for `own_delete_set_grow` at
    runs waits for C6-3's `deleteRange`.
  - **C6-2, store heap flip.** `own_store_runs` becomes the Definition
    (fields at `(locs, pool)`: `own_type_pool_runs`, `own_item_map_runs`,
    `run_pool_invs`, `locs_wf`, `pool_registry_coh`); `own_store_struct st`
    is the derived wrapper `own_store_runs s (state_runs_of st)` with
    fold / unfold laws to the cell fields, so the cell-recipe bodies keep
    compiling; `store_inv` / `types_frag` carry `(locs, pool)` and the read
    API (`own_read_locked`, `text/Len`, `text/String`, `doc/*`) reads the
    pool.
    PROGRESS 2026-09-04 (C6-2a): `own_store_runs` is the Definition
    (`own_store_fields_runs` with `own_items_field_runs` over
    `own_item_map_runs`, `own_type_pool_runs`, and `store_invs_runs` =
    `run_pool_invs` plus `pool_registry_coh`; the address `NoDup` is
    `locs_wf`). `own_store_struct` stays a cell-level definition, reached
    from the store by `own_store_runs_to_state` and folded back by
    `own_store_runs_intro_state` (`own_store_runs_as_state` re-proved
    from them; `pool_invs_of_runs` is the pure converse). The readers and
    borrows are proved off the run fields; `own_store_runs_run_wf` and
    `_covers_unique` still read through the cell state. The consumers'
    direct unfolds became `own_store_runs_to_state` and their refolds
    `own_store_runs_intro_state` (one line each). C6-2b, the lock layer
    (`own_store` / `store_inv` / `types_frag` / the read API) at
    `(locs, pool)`, is next.
  - **C6-3, bodies at runs.** Each transition proof drops the cell recipe
    for the run-level laws: `splitNode` (pool bookkeeping over
    `own_type_pool_runs` and the item-map split law), `Integrate`
    (`wp_addNode` at runs), `deleteRange` (the flip law), `GetNode` (the
    index walk over `client_locs`), `getOrCreateYType` / `repair` /
    `applyUpdate` (type creation and the materialization sites), the text
    layer (the delete-set ghost at runs, `types_of_locs_pool_ext_insert`
    gone).
  - **C6-4, delete the cell side.** `item_cell`, the cell `own_dll` and
    `own_dll_cells_layout`, `own_ytype_cells`, `cells_of_locs_runs`,
    `types_of_locs_pool` / `state_of_runs`, `type_state` / `store_state`,
    `node_loc`, `all_cells`, `pool_invs`, `registry_coh`, `live_refine` and
    every `value_*` cell law; `own_dll_fractional` and kin re-proved over
    the run Fixpoint.
  - **C6-5, fold `tm_arr`.** `type_model` becomes the run list alone
    (`tm_arr = runs_flatten`), if the specs read better that way.

Each stage ends `./build.sh make`-green and is one reviewable commit (or
a small stack); the wrapper discipline keeps the tree compiling at every
point, and C6 is the enforcement that the coexistence was scaffolding
only.
