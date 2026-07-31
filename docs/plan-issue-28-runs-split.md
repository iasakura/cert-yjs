# Plan: relax the `Len() = 1` pin (issue #28): multi-element runs, offset, split

> Historical: written before the `src/proof` reorganization (issue #101).
> Module names below were updated to the current tree, but the `file:line`
> citations predate the store / text splits and no longer resolve; grep the
> symbol instead.

Status: design study (2026-07-12). Scope: the remaining half of issue #28
(the `Hcontlen` pin in `is_dll`), which is the prerequisite for Array
`Content::Any` (#25) and for wire interop with real y-octo peers.

Reference sources surveyed for this plan (exact commits):

- y-octo `ee7e6bd` (main, 2026-06-30), the port source;
- yjs `v13.6.29` (`a6b7a9b`), the semantics reference;
- yrs `03e14a0` (v0.27.2), the second Rust data point.

## 1. Where the pin lives today

`is_dll` (src/proof/item/item.v:184) pins every heap node to

```
"%Hcontlen" ∷ ⌜length (iv.(yjs.item.content').(yjs.content.content')) = 1%nat⌝
```

so one `item_cell` = one model `YjsItem A` = one clock. Consumers:

- `wp_yType__findPos`'s count loop (src/proof/ytype/ytype.v:217, 279) rewrites
  `wp_item__Len`'s result to `1` so each visible node costs exactly one unit of
  the index budget; positions never fall inside a node.
- `wp_Store__Integrate`'s fresh-item hypothesis (store/store.v:2274) and
  `own_fresh_item_raw`, `types_cell_acc` (store/store.v:3498), `is_update_item`'s
  `Hclen` (store/store.v:3405), plus every `own_dll` destructuring tuple
  (roughly 40 sites across item/item.v / store/store.v / text/text.v).
- `Hcellctr` (store/store.v:774) states the per-cell clock bound as
  `cell_clock c < k`, which is the run bound only because runs have length 1.

The Go is already half general: `item.Len()` returns the content byte length,
`LastId()` is `clock + Len - 1` (yjs/item.go:53-60), `getNodeIndex` binary
searches by `[clock, clock+Len)` coverage (yjs/store.go:64), `integrateCore`
bumps `parent.len` by `Len()` and `Delete` shrinks it by `Len()`. But:

- `yType.findPos` (yjs/ytype.go:60-66) subtracts `right.Len()` from a `uint64`
  budget without checking `remaining >= Len`, so a multi-byte item would wrap
  the counter and walk past the target. Today this is unreachable (every
  creator mints 1-byte content, and the proofs pin it), but it means the Go
  findPos must be rewritten, not just re-verified, in this work.
- `scanConflicts` (yjs/store.go:200) tests `containsId(itemsBeforeOrigin,
  *conflict.originLeftId)` against raw ids. This is only correct when node ids
  and element ids coincide, i.e. when all runs have length 1 (see 2.3).
- `store.repair` resolves origins with a plain `GetNode` and never splits
  (correct only because origins can never point mid-run today).

## 2. Reference-implementation survey

### 2.1 The common core (all three implementations)

- `len(item)` is the clock length of the content: element count for
  `Any`/`Json`, UTF-16 code-unit count for `String`, `1` for atomic variants
  (y-octo content.rs:218, yrs block.rs:1770, yjs ContentString/ContentAny).
- `last_id = (client, clock + len - 1)` (inclusive); the state vector uses the
  exclusive `clock + len`.
- Splitting an item `(client, clock)` of length `n` at offset `d` produces:
  - left half: same id, same `origin`, same `rightOrigin` (deliberately NOT
    recomputed: yjs comments "do not set leftItem.rightOrigin as it will lead
    to problems when syncing"), content truncated to `[0, d)`, same flags;
  - right half: `id = (client, clock + d)`,
    `origin = (client, clock + d - 1)` (the left half's new `last_id`),
    `rightOrigin` copied from the original, content `[d, n)`,
    DLL-wired between left and old right, and inserted into the per-client
    node list at `index + 1`.
  - yjs additionally inherits `deleted`/`keep` onto the right half and shifts
    `redone`; yrs inherits the whole flag word (`info.clone()`). See 2.3 for
    y-octo.
- Split triggers: (a) index walks that land inside a node (insert/delete at an
  offset), (b) origin resolution of remote items before integrate
  ("clean end" for left origins: the origin element becomes the LAST element
  of a node; "clean start" for right origins: the element becomes the FIRST
  element of a node), (c) delete ranges (both boundaries), (d) state-vector
  overlap trims of partially-known incoming items.
- The conflict-resolution scan itself NEVER splits; origin membership inside
  the scan is resolved at item granularity (yjs: `getItem`, with an explicit
  comment; yrs: `blocks.get_item(id)` into `ItemPtr` hash sets).
- Merge (the inverse of split) exists in all three but never runs inside
  integrate: yjs at transaction cleanup (`tryToMergeWithLefts`), yrs at
  transaction commit (`try_squash`), y-octo in `DocStore::optimize` /
  `make_continuous` (invoked at the end of `apply_update` when `opts.gc`,
  which is the default). Mergeability is the exact inverse of the split
  invariant: same client, contiguous clocks (`l.clock + l.len = r.clock`),
  `r.origin = l.last_id`, same `rightOrigin`, physically adjacent, same
  deleted flag, mergeable content (plus yjs/yrs extras: no `redone`, not
  weak-linked).
- Partially-known incoming items (state-vector overlap `0 < offset < len`)
  are trimmed, not split: `id.clock += offset`, content loses the known
  prefix, `origin` is re-pointed at `(client, clock + offset - 1)` with a
  clean-end split of the LOCAL predecessor (yjs Item.integrate prologue,
  y-octo store.rs:456, yrs `Item::trim`; yrs at HEAD moved the trigger up
  into `apply_update`'s `Update::exclude` pre-pass but kept the same trim).

### 2.2 y-octo specifics the Go port mirrors

- `DocStore::split_node(id, diff)` -> `split_node_at(items, idx, diff)`
  (store.rs:211/225): mutates the found node in place into the left half and
  inserts the fresh right node at `idx + 1` in the client's `VecDeque`.
- `split_at_and_get_left(id)` (store.rs:287): if `id` is not already the last
  clock of its node, split at `offset + 1`; returns the node ENDING at `id`.
  `split_at_and_get_right(id)` (store.rs:269): if `id` is not the first
  clock, split at `offset`; returns the node STARTING at `id`.
- `repair` (store.rs:351) resolves `origin_left_id` via
  `split_at_and_get_left` (then normalizes it to that node's `last_id`) and
  `origin_right_id` via `split_at_and_get_right` (normalized to that node's
  head id), installing the `left`/`right` pointers.
- `ListType::find_pos` (list/mod.rs:77) returns an `ItemPosition
  { left, right, offset }`: the walk skips leading tombstones, spends the
  index budget on `indexable` nodes only, and when the budget lands strictly
  inside a node sets `offset > 0` measured INTO `pos.left` (the cursor still
  advances, so `left` is the node containing the offset). `normalize`
  (list/mod.rs:42) then performs the split and rebinds `left`/`right`.
- `remove_after` (list/mod.rs:220): normalize (left boundary), then walk
  spending the delete budget; when `remaining < len` split first, and (the
  in-place trick) the still-held node reference IS the truncated left half,
  which is then tombstoned via `delete_item`.
- No stored clock counter: `get_state` derives `clock + len` from the last
  node of the per-client list; `add_node` enforces contiguity. (cert-yjs
  keeps an explicit `store.clock`, an already-documented deviation; with runs
  it advances by `Len` per created item.)

### 2.3 y-octo divergences found (candidate upstream bugs, do NOT port)

1. **`Item::split_at` drops the deleted/keep flags of the right half**
   (item.rs:204-209). The inheritance block is a tautological no-op
   (`if left_item.deleted() { left_item.flags.set_deleted(); }` on the freshly
   built halves; yjs sets `rightItem.markDeleted()` from the ORIGINAL, yrs
   clones the whole flag word). The left half only survives because
   `split_node_at` mutates the original in place. Reachable: `repair` or
   `delete_range` splitting a tombstoned run leaves the right half visible.
   cert-yjs MUST inherit the deleted bit on both halves; otherwise the split
   changes the visible document and is not a model no-op (see 3.4).

2. **Conflict-scan origin membership at raw-id granularity**
   (store.rs, `integrate`'s loop): `items_before_origin` /
   `conflicting_items` are `HashSet<Id>` filled with the HEAD ids of scanned
   nodes, and case 2 tests `items_before_origin.contains(&conflict_item_left)`
   with the conflict's raw `origin_left_id`. An origin id is the `last_id` of
   its node, which differs from the head id whenever that node has length
   >= 2, so the test answers "no" where yjs (`getItem` + item set) and yrs
   (`ItemPtr` set) answer "yes", and the scan breaks early instead of taking
   case 2: a genuine convergence divergence for multi-element runs.
   cert-yjs's `scanConflicts` must instead test containment of the origin id
   in the clock RANGE `[id.clock, id.clock + Len)` of scanned nodes (node
   granularity, equivalent to yjs's because scans always cover whole nodes:
   window boundaries are node-aligned after repair). This matches our
   per-element pure model (2.4).

Both should be reported upstream (y-octo repo) after approval; the Go port
carries a comment at each divergence site per the repo rules.

Also kept, already documented: cert-yjs counts String clock length in BYTES
under an ASCII assumption, where the references count UTF-16 code units (so
yjs's surrogate-pair guard in `ContentString.splice` has no counterpart).

### 2.4 Why the per-element model is the right wall (spec view)

In all three implementations, node granularity is an invisible optimization
over a per-element document: split and merge occur at arbitrary times
(transaction cleanup, gc-on-apply, snapshot handling) and are unobservable.
An abstract spec stated over nodes would not even be stable across a
transaction boundary. The stable observable is the per-element sequence with
per-element ids, which is exactly the rocq-yjs model cert-yjs already uses
(`YjsItem A` with one content `A` per clock; origins resolved by id via
`find_by_id`, insert_basic.v). This confirms the roadmap decision: the model
stays per-char forever; runs live purely in the heap-to-model representation
layer. The model needs NO split operation: heap origins that point mid-run
are ordinary per-element ids on the model side.

## 3. Design

### 3.1 The abstraction wall does not move

Unchanged, statement for statement:

- `own_ytype parent dq m` with `m : list (YjsItem A * bool)` (per-char items
  with tombstone bits), `is_Text t γh name L`, `is_Store`, `own_store`
  `(client, history, doc)`, `is_root` / `is_root_lb`;
- the ghost history: events, `is_op_cert`, `ValidReplay`, the network model
  (one wire run struct DECODES to n per-char ops; causal order inside the run
  holds because char k's origin is char k-1, its predecessor in the batch);
- the rocq-yjs order theory (`YjsArrInvariant`, `integrate`, `setintegrate`,
  commutativity, convergence). New pure lemmas are additive (3.6).

`wp_Text__Insert` / `wp_Text__Delete` / `wp_store__applyUpdate(_certs)` keep
their current public statements. Notably `wp_Text__Insert`'s postcondition
(consecutive clocks from `k0`, shared right origin `oR`, left origin chained
item i+1 from item i) is exactly the run well-formedness predicate below, so
even a later switch of `Text.Insert` to y-octo's one-item-per-edit shape (M5)
keeps the same public spec.

### 3.2 `item_cell` becomes a run cell

```coq
Record item_cell := MkItemCell {
  ic_loc : loc;
  ic_run : list (YjsItem A);   (* the per-char model items this node covers *)
  ic_deleted : bool;
  ic_parent : loc;
}.

Definition run_wf (r : list (YjsItem A)) : Prop :=
  r ≠ [] ∧
  ∀ k x y, r !! k = Some x → r !! S k = Some y →
    item_id y = MkYjsId (clientId (item_id x)) (S (clock (item_id x))) ∧
    origin y = itemPtr x ∧
    rightOrigin y = rightOrigin x.
```

`run_wf` is the model shadow of the split invariant of 2.1: consecutive
clocks, left origin chained to the previous element, right origin shared.
It is exactly what `splitItem` produces and what `mergeWith` checks.

`is_dll`'s per-node conjuncts become (replacing `Hid`/`Hcontent`/`Hcontlen`;
everything else, including the flag pin and the spine links, keeps its shape):

```coq
"%Hrun"     ∷ ⌜run_wf (ic_run c)⌝ ∗
"%Hid"      ∷ ⌜item_id  (run_head c) = toYjsId iv.(yjs.item.id')⌝ ∗
"%Hcontent" ∷ ⌜content <$> ic_run c = explode iv.(yjs.item.content')⌝ ∗
"%Holid"    ∷ ⌜origin_id (origin      (run_head c)) = toYjsId <$> olid⌝ ∗
"%Horid"    ∷ ⌜origin_id (rightOrigin (run_head c)) = toYjsId <$> orid⌝
```

where `run_head` is the first element of `ic_run` and
`explode (s : go_string) : list go_string := (λ b, [b]) <$> s` splits the
heap byte string into 1-byte contents. `length (ic_run c) = Len()` falls out
of `Hcontent`. For #25 (Array), `explode` becomes the per-content-type
element decomposition; nothing else in the layer changes.

Derived notions:

- `run_flatten cells := mjoin (ic_run <$> cells)` replaces `ic_item <$> cells`
  in `cells_repr`; `own_ytype`'s model is the flatten with each element
  tagged by its cell's `ic_deleted`.
- `num_visible cells := length (filter visible flatten)`, i.e. the sum of run
  lengths over non-deleted cells: this is what the heap `yType.len` field
  already computes (`parent.len += item.Len()`).
- `Hcellctr` generalizes from `cell_clock c < k` to
  `cell_clock c + run_len c ≤ k` (the exclusive `last_id + 1` bound, matching
  `get_state`).

The heap struct keeps ONE `originLeftId`/`originRightId`/flags word per node;
the coupling pins them to the HEAD element only. The origins of elements
1..n-1 are not stored anywhere on the heap: `run_wf` reconstructs them. This
is the formal content of "runs are an invisible compression of the
per-element document".

### 3.3 The split theorem: splits are model no-ops

Splitting cell `k` (run `r`, `0 < o < length r`) rewrites the cell list to

```coq
split_cells k o cells r_loc :=
  take k cells
  ++ [ MkItemCell (ic_loc c) (take o r) (ic_deleted c) (ic_parent c)
     ; MkItemCell r_loc      (drop o r) (ic_deleted c) (ic_parent c) ]
  ++ drop (S k) cells.
```

Pure facts (all list algebra):

- `run_flatten (split_cells …) = run_flatten cells` (take/drop);
- `num_visible` preserved (both halves inherit `ic_deleted`, hence the
  requirement in 2.3 item 1);
- `run_wf (take o r)` and `run_wf (drop o r)`; moreover `run_wf` gives the
  drop half's head exactly `origin = itemPtr (r !!! (o-1))` with id
  `(client, clock + o - 1)` and the shared `rightOrigin`, which is exactly
  what the heap right node carries (`originLeftId = left.LastId()`,
  `originRightId` copied), so the head-only coupling of 3.2 re-establishes
  itself with no model change.

Consequently `own_ytype parent dq m` is invariant under `splitNode`, and so
are `own_store` and every public predicate. `repair`, `normalize`, delete
boundary splits, and (later) merges are all model no-ops; only the cells
list changes shape. This is the single load-bearing spec insight of the
whole issue.

### 3.4 Go changes (mirroring y-octo, with the two divergence fixes)

1. `store.splitNode(n *item, diff uint64) (*item, *item)` (y-octo
   `split_node_at`): truncate `n.content` in place, build the right item with
   `id = (n.client, n.clock+diff)`, `originLeftId = n.LastId()` (of the
   truncated left), `originRightId = n.originRightId`, same parent, flags
   copied INCLUDING the deleted bit (divergence fix 1, with comment), splice
   into the DLL, and insert into `s.items[client]` at `index+1` (slice
   insert). `parent.len` unchanged.
2. `store.splitAtAndGetLeft(id) / splitAtAndGetRight(id)` (store.rs:269/287)
   over `GetNode` + `splitNode`; `repair` uses them and re-normalizes the
   origin ids (store.rs:351 shape).
3. `yType.findPos` rewritten to y-octo `find_pos`: same two loops, but the
   count loop checks `remaining < right.Len()` and stops with
   `offset = remaining` measured into that node (also fixing the latent
   uint64 underflow); returns `(left, right, offset)`. A `normalize` step
   (split when `offset > 0`) runs in the callers.
4. `Text.Insert`: after findPos, normalize, then the existing per-byte loop
   (unchanged otherwise). `Text.Delete`: normalize the left boundary, and in
   the loop split when `remaining < cur.Len()` before tombstoning (y-octo
   `remove_after` in-place trick).
5. `scanConflicts`: membership tests against scanned-node clock RANGES
   instead of raw id equality (divergence fix 2, with comment): keep the two
   accumulators as `[]id` of node head ids plus lengths, or `[]*item`, and
   test `id ∈ [n.clock, n.clock+Len)`.
6. `applyUpdate` / `updateItem`: drop the 1-char content restriction
   (update.go comment); `newItem` already takes the whole string.

### 3.5 Proof-layer re-threading (wide but mechanical)

- item/item.v: `own_dll` conjunct swap (3.2); all structural lemmas
  (`own_dll_app`, `_acc`, `_insert_middle`, `_update_gen`, head/last) keep
  their skeletons, tuples gain `Hrun` and lose `Hcontlen`. `cell_repr` /
  `cells_repr` become the flatten versions. `wp_item__Len` returns
  `length (ic_run c)` via `Hcontent`.
- ytype/ytype.v: `own_ytype_cells` (`num_visible`, flatten), `own_ytype`
  (flatten with tombstone tags), `wp_yType__findPos` re-proved against the
  new Go: the count loop invariant tracks the remaining budget against
  `run_flatten` positions, and the exit either sits on a node boundary
  (offset 0, current spec shape) or inside cell `p` at offset `off` with
  `0 < off < run_len p`. As today, the spec returns the straddle/offset
  facts; it does not relate `p` to `idx` (position faithfulness stays out of
  the public specs).
- store/store.v: `types_cell_acc`, `own_fresh_item*`, `is_update_item` (drop
  `Hclen`; one struct now denotes `ops_of_updateItem : list Op`, its per-char
  decomposition), `Hcellctr` new bound, `client_run` sortedness under the
  `idx+1` insert, `wp_store__GetNode` spec ("the node whose run covers the
  clock"), and new `wp_store__splitNode` / `wp_store__splitAtAndGet{Left,Right}`
  with the 3.3 no-op postcondition.
- text/text.v: Insert/Delete re-threading; Delete gains the boundary-split
  steps (each a no-op on `ty_arr`, so the `is_Text L` unchanged statement
  survives verbatim).

### 3.6 New pure theory (the genuinely novel part)

Runs enter `Integrate` in one heap step but n model steps. Two lemma families
are needed, both Iris-free, both about the existing `integrate`/`setintegrate`:

1. **Adjacency (no-successor insertion).** If `arr !! j = Some x`,
   `YjsArrInvariant arr`, the new input has `in_originId = Some (item_id x)`,
   a clock-safe fresh id, and NO element of `arr` has `origin = itemPtr x`,
   then `integrate input arr` inserts at exactly `j + 1`. Proof sketch: the
   scan's first candidate has an origin index `≤ j` by the order invariant
   (origins precede their items) and `≠ j` by the no-successor hypothesis, so
   `fii_loop` exits on its first test (or has fuel 0). The no-successor
   hypothesis is discharged from closedness plus id uniqueness: elements
   present before x was integrated cannot reference it (this is the same
   shape as the receiver-clock-safety hypothesis of #42).
   Corollary (`integrate_run`): folding `integrate` over the n per-char
   inputs of a `run_wf` run whose head integrates at position `d` yields
   exactly `take d arr ++ run ++ drop d arr`: one contiguous splice, which is
   what the heap performs.
2. **Run-block scan bridge.** The heap scan steps NODE by node while
   `setfii_loop` steps element by element. A block lemma shows a `run_wf`
   block behaves as one unit inside the scan: for k ≥ 1, element k of a
   scanned run has origin = element k-1, whose index is strictly greater than
   `leftIdx` (origins are node-boundary-normalized), so those iterations
   always take the "advance, extend destIdx when not scanning" branch; the
   block's net effect is decided by its head element alone. Membership
   (case 2) at element granularity coincides with the Go's range test at
   node granularity because scans cover whole blocks (window boundaries are
   node-aligned after repair).

Home: develop these next to `core` in cert-yjs first (fast iteration),
upstream to rocq-yjs once stable (same flow as the deliver_locally fix).
Nothing here exists in lean-yjs or rocq-yjs; it is the "genuinely novel
formalization" the roadmap anticipated for item ⑤.

### 3.7 Out of scope, recorded

- **Merge / squash** (`make_continuous`): the inverse no-op. Not needed for
  correctness or for #25; only for wire/GC compaction parity. When done, its
  WP spec is the mirror of 3.3 (merge_cells with `run_wf` glue, flatten
  invariant), triggered from an `optimize` entry point, never inside
  integrate. Deferred indefinitely.
- **State-vector overlap trims** (`integrate` with `offset > 0`): part of the
  pending/UpdateIterator machinery (#43 / pending totality), not of this
  issue. The trim's model content is "drop already-present prefix ops", which
  the history layer already expresses per op.
- **UTF-16 clock units** and surrogate splitting: ASCII byte assumption kept.
- **Position-faithful public specs** (Insert/Delete at index idx acting at
  model position f(idx)): unchanged scope-wise; findPos specs stay
  existential as today.

## 4. Milestones

- **M1: representation generalization.** 3.2 + 3.5 + the findPos Go rewrite
  (3.4 items 3; the Go change is mandatory because the current walk
  underflows on runs). All creators still mint singleton runs; behavior
  unchanged. Wide mechanical re-thread, comparable to the #35 item_cell
  refactor. Everything after M1 is incremental.
- **M2: split machinery.** 3.4 items 1-2 + `wp_store__splitNode` /
  `splitAtAndGet*` with the 3.3 no-op specs; `repair` generalized.
- **M3: offset paths.** 3.4 item 4: Insert normalize + Delete boundary
  splits; re-prove `wp_Text__Insert` / `wp_Text__Delete` (public statements
  unchanged).
- **M4: run integrate.** 3.4 items 5-6 + 3.6 lemmas: `wp_Store__Integrate`
  over a run (postcondition: one appended cell, model = fold of n
  `setintegrate` steps = contiguous splice), `is_update_item` per-run,
  `applyUpdate(_certs)` minting n certs per struct. This makes
  `store.applyUpdate` accept real y-octo updates. The hard milestone.
- **M5 (optional): local run minting.** `Text.Insert` creates ONE item per
  edit (y-octo `insert_after` shape). Public spec unchanged (3.1). Needs M4.

Roadmap fit (docs: post-#42 roadmap, item ⑤ last after ② delete-set and
③ #40): M1-M3 are self-contained representation surgery with no interaction
with ② or ③ and can slot in whenever #25/interop pressure rises; M4 touches
applyUpdate spec shapes and is better AFTER #40 restates the public claim
(else the run generalization of `ValidReplay`-adjacent statements is done
twice). ② delete-set interacts only at M2+: remote delete ranges hitting
mid-run need `splitNode` (y-octo `delete_range` splits both boundaries), but
with len-1 runs (pre-M4) ranges never hit mid-run.

## 5. Upstream reports to file (after approval)

1. y-octo `Item::split_at` (item.rs:204-209): right half does not inherit
   `deleted`/`keep`; the inheritance block is a tautological self-check.
   Divergence from yjs `splitItem` / yrs `ItemPtr::splice`; reachable via
   `repair` / `delete_range` splitting tombstoned runs.
2. y-octo `integrate` conflict scan: `HashSet<Id>` of node HEAD ids +
   `contains(origin_left_id)` diverges from yjs (`getItem`-resolved item
   sets) whenever an origin is a non-head element of a scanned multi-element
   node; can change integration order vs yjs/yrs.
