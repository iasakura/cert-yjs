# Plan: the state-based delete set (roadmap ②; issues #37, #43-delete half)

Status: design (2026-07-12). Supersedes the OpDelete extension paths sketched
in `plan-issue-42-ghost-history.md` §8.1/§8.4, per the post-#42 roadmap
decision: deletes are NOT ops in the history; they are a state-based
semilattice composed with the insert-only op history.

## 1. Why state-based (not OpDelete)

- y-octo itself is state-based: a delete set is per-client clock RANGES
  (`DeleteSet = HashMap<Client, OrderRange>`), unioned monotonically when
  updates apply (`DocStore::delete_range`), and regenerated from the item
  flags at encode time (`generate_delete_set`). Deletes carry no id of their
  own and consume no clock.
- The model's `OpDelete` would need per-op ids under the same clock
  discipline as inserts (`histories_UniqueId` quantifies over all
  broadcasts), but the Go consumes no clock on delete: minting Delete ops
  would need a ghost-only id scheme diverging from the heap clock
  (plan-issue-42 §8.1). A Delete certificate would also have no verified
  consumer.
- Composition is cleaner: the insert-only op history (issue #42's machinery)
  stays untouched; the delete set is a join-semilattice (set union) whose
  application is idempotent and commutative BY CONSTRUCTION. The visible
  document is a view: `visible = filter (id ∉ ds) items`. Convergence then
  composes componentwise (op-based items × lattice-join deletes), which is
  exactly the shape #40 wants to state.

## 2. The ghost: one store-global monotone delete set

`store_names` gains `sn_ds : gname` holding `auth (gset YjsId)`:

- `store_inv` owns the auth `● ds`;
- `is_ds_lb γs S := own γs.(sn_ds) (◯ S)` is the persistent, duplicable
  lower bound (the same idiom as the grow-only item-set `sn_seq`).

Store-GLOBAL, not per-type: wire delete ranges are `(client, clock-range)`
pairs and mention no parent (roadmap note), and ids are globally unique, so
one set serves all root types. The per-type model view is a projection:
`st_deleted(t) = ds ∩ ids(docm_get m t)`. (Issue #37's `ts_del : gset YjsId`
per `text_state` predates #49 multi-parent; the global set is its natural
generalization.)

## 3. Coherence: the Deleted bit mirrors the set

`store_inv`'s per-type body gains `deleted_match` (the name from #37's
earlier draft):

```
deleted_match ds cells :=
  ∀ c ∈ cells, ∀ y ∈ ic_run c,
    (ic_deleted c = true  → item_id y ∈ ds) ∧
    (ic_deleted c = false → item_id y ∉ ds)
```

Run-uniform by construction: a split's halves inherit the deleted bit
(issue #28 M2, the y-octo divergence we deliberately do not mirror), so a
node's bit speaks for all its chars. Additionally the domain invariant

```
ds ⊆ ids of the integrated items (all types)
```

keeps freshly minted insert ids out of `ds`, so `Insert`/`Integrate`
re-establish `deleted_match` for the new visible cell for free (its fresh id
cannot be in `ds`).

## 4. Who updates what

| operation | heap effect (today) | ghost effect (new) |
|---|---|---|
| `Text.Delete` | flips `itemDeleted` bits, shrinks `yType.len` | auth grows: `ds' = ds ∪ (ids of the tombstoned chars)`; post returns `is_ds_lb dels` |
| `store.applyUpdate` phase 2 (new) | `deleteRange` per wire span: split at range boundaries, tombstone whole nodes, shrink `len` | auth grows by the span's ids; post returns `is_ds_lb` certificates |
| `Text.Insert` / integrate | unchanged | none (fresh ids ∉ ds; `deleted_match` extends) |
| encode (unverified codec) | `generateDeleteSet` derives the wire set from flags | none (stays `//go:build !goose`) |

The heap `store.deletedSet` field REMAINS a codec-only cache (documented
deviation from y-octo's eager `delete_item_inner` recording): the verified
delete set is the ghost; the codec regenerates the wire form from the flags,
which `deleted_match` proves agrees with the ghost.

## 5. Go deltas (D2)

- `updateItem`-style decoded form for deletes: `Update` gains
  `deletes []deleteSpan` with `deleteSpan{client Client; start, end uint64}`
  (goose-visible; the byte-level decode stays in codec.go).
- `store.deleteRange(client, start, end)` mirroring y-octo
  `DocStore::delete_range` (store.rs:698): binary-search the run list to the
  first overlapping node; for each node overlapping `[start, end)` that is
  not already deleted: split at the head boundary (`clock < start`), split
  at the tail boundary (`end < clock + Len()`), set `itemDeleted`, shrink
  the parent's visible length. Already-deleted nodes are skipped (idempotence
  on the heap; the ghost union is idempotent by definition).
- `store.applyUpdate` applies `structs` first (existing loop), then
  `deletes` (new loop). Causality within the verified subset: a delete span
  only covers ids already integrated (an explicit precondition, matching the
  covered-batch discipline; the pending/laterals stay #43).

With every run 1-char (the M1 all-singleton invariant, in force until issue
#28 M4 part 6), both boundary splits are DEAD branches, discharged exactly
like `repair`'s (M2) and `Delete`'s (M3); they go live with M4 and are then
covered by the M2 no-op cell surgery (`split_cells_flatten` etc.).

## 6. Spec deltas

- `wp_Text__Delete` (D1): keeps `is_Text t L` preservation and additionally
  returns
  `∃ dels : gset YjsId, is_ds_lb γs dels ∧ size dels ≤ uint.nat len ∧
   dels ⊆ ids of the doc's items` (the ids stay existential because the spec
  does not pin positions; see §8).
- `wp_store__applyUpdate(_certs)` (D2): precondition gains the decoded
  spans + their covered-ness; postcondition returns `is_ds_lb` for the union
  of the spans and re-establishes `deleted_match` and the length bookkeeping.
- `is_Store` / `is_Text` arities grow by the ghost name only (threading,
  like #42's history plumbing).
- Reads: `Text.Len`/`String` are already flag-driven; `deleted_match` is what
  will let #40 restate them against `visible(items, ds)`.

## 7. Milestones

- **D1 (local tracking, trimmed)**: `sn_ds` ghost + the DOMAIN invariant
  only (`ds ⊆ integrated ids`) in `store_inv`; `wp_Text__Delete` mints the
  lower bound. The bit-mirror `deleted_match` is NOT yet carried: its
  visible-side direction needs store-global id uniqueness (same id in two
  cells would break the mirror under a flip), which is derivable from the
  history layer's global uniqueness but is real plumbing; it lands with D2,
  where `deleteRange`'s idempotence actually consumes it. Growth-only
  tracking needs no uniqueness: the domain bound is monotone in the pool and
  Delete only ever adds ids of chars it just tombstoned. No Go changes.
- **D2 (wire deletes)**: `deleteSpan`/`deletes` + `store.deleteRange` +
  `applyUpdate` phase 2, with the WP specs above. Depends on the issue #28
  M2 split machinery being merged (the split calls sit in `deleteRange` even
  while dead).
- **D3 (with #40)**: the visible-document view and the composed convergence
  statement; optionally #37's full functional-correctness strengthening
  (findPos position pinning, Insert-at-idx, Delete-exact-segment), which is
  orthogonal to the delete set itself (#21 tracks the Insert half).

## 8. Explicitly out of scope here

- Position-pinned specs (#37 goal 1-2, #21): the delete set makes them
  STATEABLE, but pinning `findPos`'s `p` to the visible index is its own
  surgery over the M1 offset-aware spec; bundled with D3/#40 at the latest.
- Pending/uncovered delete spans (#43): spans over not-yet-delivered ids
  buffer in y-octo's pending machinery; the verified subset keeps the
  covered-batch precondition.
- GC (y-octo `optimize`/`gc_delete_set`): content of deleted items is
  reclaimed; changes the item representation (GC nodes) and is far out of
  the verified subset.
