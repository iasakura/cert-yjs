# Plan: total apply_update via pending (issue #40)

Status: design accepted baseline for the issue-40 branch, 2026-07-17.
Predecessor: PR #76 (closed without merge) proved order-independence for
causally-closed batches but kept `batch_ok` (causal closure) as a caller
obligation. This plan removes that obligation entirely: `applyUpdate` becomes
total, buffering unresolvable structs in the store and draining them on later
calls.

## 1. Upstream survey (which implementation to port)

We fetched and compared the three shipping implementations at pinned commits
(yjs v13 `2713308` = 13.6.31, yjs main `28e7e06` = 14.0.0-rc.24, yrs `67b0513`
= 0.27.3, y-octo `ee7e6bd`).

Readiness gate for a struct S = ((c, k), originLeft, originRight, parent),
against the local state vector sv (next expected clock per client):

| impl | own-client contiguity `k <= sv(c)` | dependency check | duplicate handling |
|---|---|---|---|
| yjs v13 | required; gap pends the client tail | `dep.clock < sv(dep.client)`, own-client deps exempt | per-struct offset; full dup dropped |
| y-octo | required (same) | same as v13 (`get_missing_dep`) | same (offset) |
| yrs 0.27 | NOT required: gap is filled with an integrated `Skip` hole | `is_missing` = frontier check OR inside a skip hole | update pre-trimmed against known state |
| yjs v14-rc | NOT required (same as yrs) | frontier + skip-hole, no own-client exemption | pre-excluded before integration |

Pending storage and retry:

- yjs v13: one merged encoded blob + a min-map `missing : client -> clock`;
  retry the whole blob once per apply when some `missing[c] < sv(c)`.
- y-octo: `DocStore.pending : Option<Update>` holding decoded structs +
  `missing_state`; at most two passes per `apply_update` call. Known y-octo
  defect: when both the new update and the store have leftovers, the OLD
  pending's `missing_state` is dropped by `Update::merge_into`
  (document.rs:293-295), so previously recorded wake-up thresholds are lost
  and pending structs can starve. yjs v13 min-merges both maps instead.
- yrs: `PendingUpdate { update, missing }`, decoded; same threshold retry.

Decision:

- Port basis: **y-octo** (the whole repo is a y-octo port), whose gate is
  semantically **yjs v13**: structural dependencies + per-client clock
  contiguity.
- The yrs / yjs-v14 "skip hole" semantics (integrate even with a gap in the
  author's own sequence) is NOT portable to the verified model today: every
  integrate lemma of the rocq-yjs stack (`maximalId`, `ValidReplay`'s
  per-client clock conditions, `yjs_concurrent_commute`'s distinct-client
  hypothesis) requires items of one client to be applied in clock order.
  Dropping contiguity admits same-client concurrent application, and for
  adversarial inputs (two ops of one client with identical origin pairs,
  impossible for an honest sequential author) the YATA tie-break then
  genuinely diverges: applied in opposite orders on two replicas, the
  same-left-origin + same-right-origin rule places whichever op is integrated
  second to the LEFT of the first, producing different documents. The
  contiguity gate forces same-client ops into clock order on every replica,
  which neutralizes that class and matches the available convergence theory.

## 2. The gate, phrased arrival-only

The store tracks no state vector. All checks are arrival checks against the
store's item set (GetNode):

```
ready(S) :=   (originLeftId  = nil or present)          // arrival of left origin
            and (originRightId = nil or present)          // arrival of right origin
            and (k = 0 or (c, k-1) present)               // arrival of own predecessor
dup(S)   :=   (c, k) present                              // already integrated
```

Parents never block in the verified subset: `parentName != nil` resolves by
`getOrCreateYType` (creating on miss), `parentName = nil` borrows the parent
from the resolved left/right origin (the wire format guarantees a struct
without origins carries a parent).

The own-predecessor clause is exactly y-octo/yjs-v13 contiguity for honest
(dense-clock) authors: run lists stay gap-free, so `(c, k-1)` present iff
`sv(c) >= k`. For an author that skips clocks both formulations starve the
op forever (y-octo: `sv(c)` never reaches k; ours: `(c,k-1)` never arrives),
so liveness agrees too. Phrasing it as arrival keeps the implementation free
of any tracked state vector, per the issue direction; it also keeps `AddNode`
append-only correct (a fresh `(c,k)` with `(c,k-1)` present appends exactly at
the run tail).

## 3. Go implementation shape

- `store` gains `pending []updateItem` (y-octo: `DocStore.pending:
  Option<Update>` whose `Update.structs` is `ClientMap<VecDeque<Node>>`; we
  keep the decoded, flat batch shape that `store.applyUpdate` already uses
  since #49 -- flattening is order-preserving per client and the batch is the
  unit we verify; deliberate container deviation, documented in code).
- `store.applyUpdate(structs)` becomes TOTAL:

  ```
  pending := s.pending ++ structs ; s.pending = nil
  repeat
      progress := false; rest := []
      for ui in pending:
          if GetNode(ui.id) hit        -> drop (duplicate; y-octo offset>=len)
          else if deps arrived         -> newItem; repair; Integrate; progress = true
          else if id not yet in rest   -> rest = append(rest, ui)   // in-pending dedup
      pending = rest
  until !progress
  s.pending = pending
  ```

  Deliberate structural deviations from y-octo (all commented in code and
  reported):
  1. round-based fixpoint instead of `UpdateIterator`'s stack-based dependency
     chase. Both compute the same applied set (the least structural-dependency
     closure over store + pending): the chase is a within-pass shortcut for the
     later rounds, and the parked-client analysis shows a pass of the iterator
     applies exactly the closure too. Rounds are O(n^2) worst case but trivial
     to verify; the applied SET (the spec) is identical.
  2. always drain the whole pending instead of the `missing_state`
     threshold check. The threshold is a retry optimization; y-octo implements
     it with the state-drop defect above. Draining is deterministic, never
     applies less than y-octo, and needs no missing-state bookkeeping.
  3. in-pending dedup by id instead of `merge_into`'s equal-struct pruning
     (equal ids imply equal certified ops, so keeping the first is enough).
- `Doc.ApplyUpdate` (codec.go): decode + run-split as today, then ONE locked
  call to `store.applyUpdate`; the unverified codec-side fixpoint loop is
  deleted (it is now the verified core).
- `AddNode` unchanged (append), justified by the gate (section 2).
- Tests: convergence tables for out-of-order delivery (per-item updates
  applied shuffled/reversed/duplicated across replicas), pending drain
  (apply an update whose deps arrive later; assert intermediate pending and
  final equality), self-echo (own ops re-delivered are dropped).

## 4. Pure model layer (new, Iris-free)

File: extend `yjs_network_model.v` (or a new `yjs_pending_model.v` imported
by it) over the doc model `DocModel` and pendings `list (TId * IntegrateInput)`.

- `deps_of (input) : list YjsId` = origins + own predecessor (clock > 0).
- `pending_step m pending = (applied, rest, m')`: one scan, mirroring the Go pass
  exactly (dup drop, ready -> `integrate` into its type's array, else keep,
  keeping first occurrence per id).
- `pending_drain m pending = (applied_list, rest)`: iterate `pending_step` to a
  fixpoint (fuel = |pending|; progress strictly shrinks).
- Characterization: `list_to_set applied_list` is the least fixpoint of
  `X ↦ { x ∈ pending | fresh(x) ∧ deps(x) ⊆ ids(m) ∪ ids(X) }`, and
  `rest = pending \ applied \ dups` (as multisets mod first-occurrence dedup).
- Composition / order independence (the headline): draining `(p1)` then
  `(rest1 ++ p2)` equals draining `(p1 ++ p2)` in one go, up to applied-list
  permutation with the same final document and the same rest set; hence store
  state after any sequence of `applyUpdate` calls is a function of the
  multiset-union of delivered batches (dedup makes it a set function).
- `ValidReplay` production: for certified pendings, the applied list in drain
  order is a `ValidReplay` (per-step `toItem` resolution from the gate,
  `maximalId` + doc-global clock bound from contiguity, `IsItemValid` from
  the certificate transport of section 5, `integrate = Some` from origins
  present + `YjsArrInvariant`).

## 5. Network-model rework (the theory)

The current pipeline derives per-step validity and convergence from the
network's CAUSAL DELIVERY (`hwf_causal_delivery`), which the pending gate
deliberately violates (we apply ops whose non-origin causal ancestors are
absent). Replacement:

- `history_wf` drops `hwf_causal_delivery` and gains:
  - `hwf_realizable`: some global linearization `L` of all events projects to
    the per-client histories and places every `EvBroadcast op` before any
    `EvDeliver op`. (The ghost layer trivially maintains it: every ghost step
    appends to one client's history while the certificate of a delivered op
    witnesses its earlier broadcast.) This is what keeps `raw_hb` acyclic
    once causal delivery is gone -- without it, happens-before on raw
    histories admits cycles and no order theory survives.
  - `hwf_fifo`: `delivered_from (N i) j` is a prefix of `broadcast_ops (N j)`
    (per-author FIFO). Today a lemma (`delivered_from_prefix`) proved FROM
    causal delivery; it becomes a field maintained by the deliver step, which
    the contiguity gate discharges. The sync-protocol material (#51/#79)
    keeps building on it.
- The structural dependency order: `dep_lt` = transitive closure of
  "x is an origin of y or x is y's same-client predecessor" over the
  broadcast universe. Packaged as `CausalOrder` (partial order): acyclicity
  via `dep ⊆ raw_hb` (an op's origins are delivered at its author before its
  broadcast) and `raw_hb ⊆ L-order` (realizability rank).
- `OperationReplayValidity` instance for `dep_lt` ("RV_dep"): an op broadcast
  anywhere is valid in any dep-consistent, dep-closed replay of its
  dep-past. Mirrors upstream `isValidState_insert_from_source`, but only the
  origin chain is transported: broadcast-time validity comes from
  `hwf_broadcast_valid`; the resolved origin items agree between the author's
  state and the replayed state by id-determinism over the shared broadcast
  universe (upstream item/toItem determinism lemmas). This is the precise
  sense in which structural dependencies, not happens-before, are what
  validity needs.
- Deliver step `history_deliver_pending`: given per-op certificates for the pending
  (NO `batch_ok`), compute `pending_drain`, append `EvDeliver` for the APPLIED
  list only (pending ops stay certificate-only), re-establish the relaxed
  `history_wf` + `history_state_coh`, and return the `ValidReplay` for the
  applied list. Own-client pending entries are provably duplicates (self
  delivery) and land in the dropped class, preserving the local clock
  invariant.
- Convergence endgame (redo of PR #76 on the new base):
  `yjs_strong_convergence` instantiated with `hb := dep_lt` and `RV_dep`:
  replicas whose applied sets agree have pointwise-equal documents (both
  applied orders are dep-consistent and dep-closed BY THE GATE; concurrent
  pairs have distinct clients because same-client applied ops are always
  dep-chained through their fully-applied predecessor chain). Combined with
  section 4's closure function: same received set => same applied set => same
  document. That is the total, assumption-free SEC statement.

## 6. WP layer

- `store_inv` / `own_store` gain the pending: model becomes
  `(c, h, m, pend)` with `pend : list (TId * IntegrateInput)` tied to the
  `pending` field (an `own_update`-style slice predicate, dq-owned by the
  lock). All lock-body threading (Insert / Delete / GetText / read API)
  extends mechanically.
- New public spec (replacing `wp_store__applyUpdate_certs`):

  ```
  {{{ own_store s c h m pend ∗ own_update sl dq inputs ∗
      is_pending_certified γh (pend ++ inputs) ∗ (W64 no-wrap seams) }}}
      store.applyUpdate(sl)
  {{{ RET #(); ∃ applied pend' m' h',
      own_store s c h' m' pend' ∗ own_update sl dq inputs ∗
      ⌜pending_drain m (pend ++ inputs) = (applied, pend')⌝ ∗
      ⌜ValidReplay applied m m'⌝ ∗ ⌜h' = h ++ (deliver_ev <$> applied)⌝ ∗
      (is_root_lb fragments for the applied roots) }}}
  ```

  No ordering, closure, freshness, or dedup obligations on the caller; the
  postcondition determines applied/pending/model from the pure `pending_drain`.
- The loop proof: outer fixpoint over rounds (progress measure), inner loop
  refining `pending_step`; the dup branch consumes `GetNode`'s hit, the ready
  branch reuses `wp_Store__Integrate`'s model-level spec, the keep branch is
  bookkeeping. `getOrCreateYType`'s MISS branch becomes verified (the #49
  pre-bound-roots restriction falls: totality requires on-the-fly root
  creation; the loop invariant lets `bind`/`types`/`m` grow).
- `Doc.ApplyUpdate` wrapper: lock + call + unlock over `is_Store`, with the
  caller's linearization view shift (as PR #76's `wp_Doc__applyUpdate`, minus
  the certification-against-`h` obligation).

## 7. Milestones

- M1 Go: pending field + total loop + codec thinning + tests; goose green.
- M2 pure closure theory: `pending_step` / `pending_drain` / closure
  characterization / composition; compiles standalone.
- M3 network-model rework: relaxed `history_wf` (realizability, FIFO),
  `dep_lt` CausalOrder, RV_dep, `history_deliver_pending`, and the ValidReplay
  production for drained pendings.
- M4 WP re-plumb: store field threading, the total `wp_store__applyUpdate`,
  certificate spec, `getOrCreateYType` miss branch, Text/Insert re-thread.
- M5 convergence endgame + `Doc.ApplyUpdate` public entry; strict
  `./build.sh` + Go tests.

## 8. Upstream findings to report (do not silently absorb)

- y-octo drops the stored pending's `missing_state` when merging with new
  leftovers (`document.rs:293-295` + `Update::merge_into`), losing retry
  wake-up thresholds that yjs v13 min-merges (`readUpdateV2`,
  encoding.js:405-414). Candidate upstream issue.
- y-octo `Update::merge_into` underflows `structs.len() - 1` on an
  empty per-client queue reachable via public `Update::merge` input.
- (Context only) yjs v14-rc / yrs integrate across own-client gaps via Skip
  holes; formal convergence for that gate over adversarial inputs is open
  (the identical-origin-pair divergence above), which is a reason to keep
  v13 semantics in a verified setting.
