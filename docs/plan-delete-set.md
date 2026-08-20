# Plan: the state-based delete set (roadmap 2; issues #37, #133, #43-delete half)

Status: D1 in re-port (2026-08-11). Originally designed 2026-07-12 and D1
implemented ghost-only on branch `delete-set-d1` (PR #77) against the old
one-file-per-package proof layout; this revision retargets the file names to
the module split (store/heap.v etc.), records the RA reuse, and REVISES the
D2 causality treatment to pending-buffering (section 5), superseding the
covered-batch precondition. Supersedes the OpDelete extension paths sketched
in `plan-issue-42-ghost-history.md` sections 8.1/8.4, per the post-#42
roadmap decision: deletes are NOT ops in the history; they are a state-based
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
  document is a view: `visible = filter (id ∉ delete_set) items`. Convergence then
  composes componentwise (op-based items × lattice-join deletes), which is
  exactly the shape #40 wants to state.

## 2. The ghost: one store-global monotone delete set

`store_names` gains `sn_delete_set : gname` holding `auth (gset YjsId)` -- the SAME
RA as the accepted-id set (`accUR`, store/heap.v), so no new `inG` Context
anywhere and `algebra.v`'s `auth_gset_*` lemmas apply as is:

- `store_inv_excl` / `own_store` own the auth (bundled as `own_delete_set`, which
  also carries the domain bound of section 3);
- `is_delete_set_lb γs S := own γs.(sn_delete_set) (◯ S)` is the persistent, duplicable
  lower bound (the same idiom as the grow-only item-set `sn_seq` and the
  accepted set `sn_accepted`).

Store-GLOBAL, not per-type: wire delete ranges are `(client, clock-range)`
pairs and mention no parent (roadmap note), and ids are globally unique, so
one set serves all root types. The per-type model view is a projection:
`st_deleted(t) = delete_set ∩ ids(docm_get m t)`. (Issue #37's `ts_del : gset YjsId`
per `text_state` predates #49 multi-parent; the global set is its natural
generalization.)

REVISED at the re-port: the domain bound is stated over the DOC MODEL, not
the cell pool -- `delete_set_dom delete_set m := ∀ i ∈ delete_set, doc_model_has m i = true`
(store/model.v), with `own_delete_set γs m` carried by `store_inv_excl`/`own_store`
next to their existing `m`. The original cells-level bound needed bespoke
pool-transfer lemmas per surgery (snoc, flip, split); the model-level bound
transports through the lemmas the proofs already produce: `Text.Insert`
via `docm_has_integrate_mono`, `applyUpdate` via `ValidReplay_mem`,
`Text.Delete` and `GetOrCreateText` change `m` not at all. The cells-level
mirror (`deleted_match`, section 3) stays a D2 concern.

## 3. Coherence: the Deleted bit mirrors the set

`store_inv`'s per-type body gains `deleted_match` (the name from #37's
earlier draft):

```
deleted_match delete_set cells :=
  ∀ c ∈ cells, ∀ y ∈ ic_run c,
    (ic_deleted c = true  → item_id y ∈ delete_set) ∧
    (ic_deleted c = false → item_id y ∉ delete_set)
```

Run-uniform by construction: a split's halves inherit the deleted bit
(issue #28 M2, the y-octo divergence we deliberately do not mirror), so a
node's bit speaks for all its chars. Additionally the domain invariant

```
delete_set ⊆ ids of the integrated items (all types)
```

keeps freshly minted insert ids out of `delete_set`, so `Insert`/`Integrate`
re-establish `deleted_match` for the new visible cell for free (its fresh id
cannot be in `delete_set`).

## 4. Who updates what

| operation | heap effect (today) | ghost effect (new) |
|---|---|---|
| `Text.Delete` | flips `itemDeleted` bits, shrinks `yType.len` | auth grows: `delete_set' = delete_set ∪ (ids of the tombstoned chars)`; post returns `is_delete_set_lb dels` |
| `store.applyUpdate` phase 2 (new) | `deleteRange` per wire span: split at range boundaries, tombstone whole nodes, shrink `len` | auth grows by the span's ids; post returns `is_delete_set_lb` certificates |
| `Text.Insert` / integrate | unchanged | none (fresh ids ∉ delete_set; `deleted_match` extends) |
| encode (unverified codec) | `generateDeleteSet` derives the wire set from flags | none (stays `//go:build !goose`) |

The heap `store.deletedSet` field REMAINS a codec-only cache (documented
deviation from y-octo's eager `delete_item_inner` recording): the verified
delete set is the ghost; the codec regenerates the wire form from the flags,
which `deleted_match` proves agrees with the ghost.

## 5. Go deltas (D2)

File-name map for the re-port (the D1 commit predates the module split):
`yjs_store_base.v` -> `store/value.v` (pure: `deleted_match`, `delete_set_dom`,
`all_cells_pointwise`) + `store/heap.v` (ghost: `sn_delete_set`, `is_delete_set_lb`,
`own_delete_set`, laws; `store_inv_excl`/`own_store` conjunct; `store_tie_init`);
`yjs_store_integrate.v` -> `store/Integrate.v`; `yjs_store_update.v` ->
`store/applyUpdate.v` + `store/repair.v`; `yjs_text.v` ->
`text/Insert.v` + `text/Delete.v` (reads untouched: `own_delete_set` sits in the
exclusive slice, not `store_inv_ro`). `doc/GetOrCreateText.v`'s miss branch
transports `own_delete_set` over `all_cells_insert_empty`.

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
- `store.applyUpdate` applies `structs` first (existing total drain), then
  `deletes` (new loop). REVISED (supersedes the covered-batch precondition
  of the first draft): a span may cover ids that have NOT arrived -- the
  server's apply path is total (issue #40) and asserts no causality, so a
  precondition is not dischargeable there. Mirror y-octo's pending delete
  set instead: apply the covered portion of each span, buffer the uncovered
  remainder in a `pending deletes` store field next to the pending structs,
  and re-drain it after every apply (the same fixpoint discipline as
  `wire_drain`; a span's coverage only grows as structs arrive, and set
  union is idempotent, so re-application is harmless by construction).

With every run 1-char (the M1 all-singleton invariant, in force until issue
#28 M4 part 6), both boundary splits are DEAD branches, discharged exactly
like `repair`'s (M2) and `Delete`'s (M3); they go live with M4 and are then
covered by the M2 no-op cell surgery (`split_cells_flatten` etc.).

## 6. Spec deltas

- `wp_Text__Delete` (D1): keeps `is_Text t L` preservation and additionally
  returns
  `∃ dels S, is_delete_set_lb γs dels ∗ is_root_lb γs name S ∧ size dels ≤ uint.nat
   len ∧ dels ⊆ item ids of S` (the ids stay existential because the spec
  does not pin positions, see §8; the domain clause is witnessed by a content
  lower bound `is_root_lb` minted at entry, so "the doc's items" is itself a
  certificate, not a raw internal set).
- `wp_store__applyUpdate(_certs)` (D2): precondition gains the decoded
  spans + their covered-ness; postcondition returns `is_delete_set_lb` for the union
  of the spans and re-establishes `deleted_match` and the length bookkeeping.
- `is_Store` / `is_Text` arities grow by the ghost name only (threading,
  like #42's history plumbing).
- Reads: the #125 read API is flag-driven (`visible_items`/`visible_string`
  over the tombstone bits of the snapshot); `deleted_match` is what turns
  those into functions of `(items, delete_set)` -- e.g. `wp_Text__String_hist` can
  then say "the visible string is the delivered items MINUS a set that is at
  least your `is_delete_set_lb` certificate", the delete-aware strengthening of the
  issue #125 guarantee.

## 7. Milestones

- **D1 (local tracking, trimmed)**: `sn_delete_set` ghost + the DOMAIN invariant
  only (`delete_set ⊆ integrated ids`) in `store_inv`; `wp_Text__Delete` mints the
  lower bound. The bit-mirror `deleted_match` is NOT yet carried: its
  visible-side direction needs store-global id uniqueness (same id in two
  cells would break the mirror under a flip), which is derivable from the
  history layer's global uniqueness but is real plumbing; it lands with D2,
  where `deleteRange`'s idempotence actually consumes it. Growth-only
  tracking needs no uniqueness: the domain bound is monotone in the pool and
  Delete only ever adds ids of chars it just tombstoned. No Go changes.
- **D2 (wire deletes, issue #133)**, split into two steps so the tree stays
  green and the proof work is isolated from the API churn:
  - **D2a**: the `deleteSpan` type and `store.deleteRange` (Go + goose +
    behaviour tests: exact coverage, idempotence, skipping unintegrated
    chars, remote convergence), plus its WP `wp_store__deleteRange`. Touches
    no store field and no public signature, so nothing downstream moves.
    The WP is the substantial half: a loop over the clock range where each
    step is [wp_store__GetNode_total] (covering or absent) + up to two
    [splitNode] calls at the range boundaries (the M2/stage-D transport
    records) + the flag flip and [yType.len] bookkeeping of [Text.Delete]'s
    loop. Postcondition: the pool invariants and every type's [ty_arr]
    survive (tombstoning and splitting are both model no-ops), and the
    covered chars of the range are now tombstoned.
  - **D2b**: the wiring. `Update.deletes`, a `pendingDeletes` store field
    with its `store_inv` conjunct, `store.applyDeleteSpans` (apply + buffer
    the uncovered remainder, re-drained by later applies), the certificates
    ([is_delete_set_lb] out of [Text.Delete] and the wire path), and the wire-format
    ripple: `Codec` returns structs AND spans, `yjs_prot`'s `update_wf`
    covers spans, and `ApplySyncUpdate` / `ApplyEncodedUpdate` / the server
    proofs thread them (mechanical).
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
