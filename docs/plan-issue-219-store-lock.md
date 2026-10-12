# Plan: move the lock out of the store (issue #219)

Status: examination and design, 2026-10-05. This document answers the two
questions issue #219 leaves open before any code moves: whether the
proposed redesign actually resolves the deviation it targets (issue #220,
item 1: store functions that are public for the store have specs over
non-public predicates), and whether it creates new deviations against the
spec rules of `.claude/skills/spec-shape/SKILL.md`. It also decides the
three open points of #219 (what the read lock returns, what the lock type
is, whether the free functions become methods again), and cuts the work
into milestones.

## 0. TL;DR

The redesign resolves the deviation, and the reason is structural, not
cosmetic: the conjuncts of today's lock body split cleanly into those that
every public store method preserves and those that only the lock holder
re-establishes. The first group becomes the new public `own_store`; the
second group becomes the lock invariant of the new lock type. Every one of
the eight public-for-store functions then takes `own_store` whole and
returns it whole (section 2 checks them one by one).

It creates no new deviation, provided four design decisions are made (the
first is a uniformity choice, the others forced or strongly suggested by
the rules themselves):

1. the read lock hands out a fractional `own_store`, not a share of a
   partial predicate (section 5; this settles open point 1);
2. `deleteNode` and `addNode` become `*store` methods again, because a
   free function over `*item` cannot take the `own_store` its spec needs
   (section 6; this settles open point 3; `splitItem` stays free);
3. the lock type is a new unexported struct, the Go rendering of y-octo's
   `StoreRef = Arc<RwLock<DocStore>>` (y-octo 0.1.0 src/doc/store.rs:36),
   holding `mu` and the store (section 4; this settles open point 2);
4. the pool-coupled ghost authorities (the item-set authority, the
   registry authority, the delete-set authority with its tombstone clause)
   move INTO `own_store`, while the history, the counter tie, the accepted
   set and the pending certificates move into the lock invariant
   (section 3; the dividing line is "does every store method preserve
   it").

The public specs keep the cell model (`store_state`, with the address
lists), which #219 explicitly allows ("a spec may use any model, the cell
model included"), so the eight proofs port nearly one for one.

## 1. Why the specs cannot use the public predicate today

The store's public predicate on main is

```
own_store s γs γh c h m pend deleted m0 deleted0 :=
  own_store_data s γs γh c h m pend deleted ∗ own_observers s γs γh m0 deleted0
```

(src/proof/store/heap.v). `own_store_data` is `own_store_state` (the data
fields with the pure `store_invs`) closed over the public model: the
client's ghost operation history `h` with `history_state_coh h m`, the
registry-replayed model tie `pool_registry_models m bind p`, the clock
counter tie `pool_next_clock p c k`, the accepted-set authority with
`accepted_coh`, the delete set with its domain bound, and the pending
buffer's certificates.

Of those closure conjuncts, NONE is preserved by the store methods alone:

- `Integrate` grows the pool, so `m` moves; the history `h` is extended
  by the caller afterwards (`Text.InsertIn` appends the insert events,
  the update path appends the delivery), so between the two,
  `history_state_coh h m` is false.
- `Integrate` of a local item consumes the clock `k` that the caller
  bumps afterwards, so `pool_next_clock p c k` is false in between.
- the pending certificates and the accepted set move only in the
  applyUpdate drain, which is the transaction's loop, not a store method.
- the observers are told only by `notify` at the end of the transaction
  (their lag is already a parameter, `m0` / `deleted0`).

So a store method spec stated over `own_store` could not give it back, and
the specs retreated to the non-public `own_store_state`. That is the
deviation: the predicate the eight functions are stated over holds neither
`mu` nor `observers` nor any ghost resource.

The key observation this plan builds on: everything `own_store_state` DOES
hold, every public store method preserves, and the conjuncts listed above
that the methods break are exactly the ones the transaction re-establishes
before it releases the lock. The proposal of #219 is therefore not a
workaround but the correct type boundary: the store's invariant is what
the store's methods keep; the rest is the lock's invariant, and the lock
belongs to another type.

## 2. The check, function by function

The new public predicate (section 3 gives the full definition) is

```
own_store s γs q (state : store_state) (ds : gset YjsId)
          (m0 : DocModel) (deleted0 : gset YjsId)
```

every data field of the store at `state` (the cell model: client, clock,
address map, pool, registry, the two buffers), the `observers` field with
every registered observer told up to `(m0, deleted0)`, the pure
`store_invs state`, and the pool-coupled ghost authorities, all at
fraction `q`. For each public-for-store function, what its spec becomes
and why it closes:

| function | today (spec over) | after | why it preserves `own_store` |
|---|---|---|---|
| `Integrate` | `own_store_state` | `own_store` at 1, state steps by the splice | `store_invs` survive under the existing preconditions (`integrate_ready`, `pool_next_clock`, `origins_resolved`); the item-set authority grows by the spliced run inside the proof (grow-only, frame-preserving); observers and their `(m0, deleted0)` untouched |
| `GetNode` | `own_store_state` | `own_store` at `q`, unchanged | read-only; the returned node pointer appears through the holder's predicate plus the pure slot fact, which the first spec-shape rule explicitly blesses ("as the store's nodes appear in the store's predicate") |
| `getOrCreateYType` | `own_store_state` | `own_store` at 1, state steps by `pool_lookup_or_create` | the miss branch extends pool and registry together (`store_invs` closed by the existing lemmas); with the registry authority inside `own_store`, the spec also mints `is_type_binding` itself, which today a caller-side reconciliation pass does |
| `splitNode` | `own_store_state` | `own_store` at 1, state steps by the split | a split is a model no-op on `tm_arr` (issue #28), so the item-set authority does not even move; `store_invs` closed by the existing split lemmas |
| `splitAtAndGetLeft` / `Right` | `own_store_state` | `own_store` at 1 | composition of `GetNode` and `splitNode` |
| `repair` | `own_store_state` + `own_linked_item` | `own_store` at 1 + `own_linked_item` | composition of the splits and `getOrCreateYType`; the repaired item stays outside the store (its own predicate), linked to addresses that are part of the state model, so nothing new is exposed |
| `repair` (creation form) | `own_store_state` + `own_linked_item` | same shape | the second spec survives with its existing justification (it covers the unbound parent name that `wp_store__repair`'s `pool_repair_parent` premise excludes) |
| `deleteNode` | `own_type_pool` | `own_store` at 1, the addressed run's bit flips | becomes a method (section 6); tombstoning preserves `store_invs`, does not change `tm_arr` (so not the item-set authority), and only strengthens the delete set's tombstone clause |

Two things every row relies on:

- The model stays the cell model, because two of the eight specs must
  say WHICH heap node they mean, and the addresses in `ss_locs` are the
  words for that. `GetNode` returns a raw node pointer `l`, and its
  postcondition identifies it: `pool_covers (ss_pool state) parent k
  (toYjsId idv)` and `(ss_locs state !! parent) ≫= (λ ls, ls !! k) =
  Some l`, that is, `l` is the address of the `k`-th run of type
  `parent` and that run covers the id. `Integrate` receives the item
  already linked to its neighbours, and its precondition says where the
  item's `left` / `right` fields point: `own_linked_item item_l input
  parent (loc_at ls (kL - 1)) (loc_at ls kR)`, the addresses of the
  resolved origin runs read off the parent's address list `ls`. Both
  sentences mention `ss_locs` / `ss_pool`, so both are writable only
  while the state, addresses included, is a spec parameter. The
  alternative, a public spec over the doc model alone (`m`, the
  per-root char sequences, with the pool and the addresses existential
  inside `own_store`), erases that vocabulary: the address ties would
  have to move into a new predicate owning the store AND the fresh item
  under one existential, and a model-level meaning for `GetNode`'s
  returned pointer needs the run-granular model redesign that is
  issue #105. That is a separate, much larger refactor, and nothing
  requires it here: the deviation is about a predicate holding only
  part of the store's resources, not about the model, and #219 states
  that a spec may use any model, the cell model included. Keeping the
  cell model is what lets the eight proofs port nearly one for one.
- The observers ride along untouched: no store method reads or writes the
  `observers` field (only `Text.Observe` and `notify` do, and both run in
  the transaction layer), so `(m0, deleted0)` pass through every spec
  as-is.

The related transaction-layer deviation (`wp_Transaction__deleteNode`
passing `own_type_pool` through its spec, #220 item 1 second bullet)
resolves the same way one level up: `own_transaction` already holds
`own_store` whole (src/proof/transaction/heap.v), and once the store
methods close over `own_store`, the transaction methods
(`integrate`, `deleteNode`, `deleteRange`, `applyUpdate`) can be stated
over `own_transaction` without decomposing the store across a loop,
because re-closing `own_store` after each store call is free.

## 3. Where each resource of today's lock body lands

Today's lock body (`store_inv = store_inv_excl ∗ store_inv_ro`, plus
`own_observers` beside it in `tie_body`) redistributes as follows. The
dividing line: a resource whose shape every store method preserves goes
into `own_store`; a resource only the transaction re-establishes goes
into the lock invariant.

Into `own_store` (all fractional, section 5):

- every data field with its contents (today's `own_store_fields`:
  client, clock, deletedSet struct, item index, registry map, type pool,
  pending, pendingDeletes), at the `store_state` model;
- the `observers` field with `own_observer_registry` at `(m0, deleted0)`
  (today's `own_observers`);
- `store_invs state` (pure);
- the item-set authority `γs.(sn_seq)` at exactly the pool's item sets:
  maintained by `Integrate`, constant for everything else;
- the registry authority `ghost_map_auth γs.(sn_types)` at exactly
  `ss_bind state`, with the persistent `is_type_binding` copies:
  maintained by `getOrCreateYType`;
- the delete-set authority `γs.(sn_delete_set)` at the parameter `ds`,
  with the tombstone clause `delete_set_tombstoned ds (all_runs p)`
  (tombstoning only ever strengthens it; splits inherit the deleted bit,
  deliberately, see store.go `splitItem`); grown by the transaction
  through a state-transition law exported by heap.v
  (`own_store_grow_delete_set`, the successor of `own_delete_set_grow`);
- the client pin `is_store_client` (persistent).

Rationale for the authorities sitting inside rather than beside: first,
the readers need them (a reader compares `is_type_lb` /
`is_delete_set_lb` fragments against the authorities while holding only
its fraction, as `store_inv_ro` provides today); second, it makes
"authority equals heap state" definitional inside one predicate instead
of a release-time proof obligation smeared over callers; third, it lets
`getOrCreateYType` mint its own binding witness, deleting the
caller-side ghost-map reconciliation that `store/wp_private.v` carries
for the applyUpdate path.

Into the lock invariant of the lock type (the replica history bundle; one named
predicate, say `own_replica_history γs γh c h state m ds`):

- the client's ghost history `own_client_history γh c h` with
  `history_state_coh h m` and `pool_registry_models m bind p` (so `m` is
  the registry-replayed model of the state's pool);
- the counter tie `pool_next_clock p c k` (the clock FIELD is in
  `own_store`; its tie to the pool is not, because `Integrate` breaks it
  until the caller bumps the field);
- the accepted-set authority with `accepted_coh acc h pend`;
- the delete set's domain bound `delete_set_dom ds m` (it mentions the
  doc model, which only the history side knows);
- the pending certificates (`is_pending_certified`, `is_pending_rooted`,
  the length bound).

The lock invariant then says: `own_store` at fraction 1 with the
observers caught up (`m0 = m`, `deleted0 = pool_tombstoned p`), next to
the replica history bundle. `transact` acquires the write lock and receives both;
the closure runs over `own_transaction`, which becomes
`own_store (observers at the start state) ∗ own_replica_history ∗ the
record`; `notify` moves the observers; release demands the coherence
back. This is exactly the C1/C2 transaction design with the predicate
boundary redrawn, so `wp_Transaction__notify`'s job does not change.

`own_store_data` and `own_store_state` dissolve: the first into
`own_store ∗ own_replica_history`, the second into `own_store`'s body
(`own_store_fields` survives as the internal fields conjunct). The names
`store_inv_excl` / `store_inv_ro` disappear with the ro/excl split
(section 5). The agreement that `pool_frag` provides today (a reader's
share and the invariant's share are at the same pool) comes instead from
fractional validity of the shares themselves, as one heap.v law
(`own_store_agree : own_store q1 state1 … ∗ own_store q2 state2 … ⊢
⌜state1 = state2 ∧ …⌝`).

## 4. The Go change and the lock type (open point 2)

A new unexported struct, the Go rendering of y-octo's store handle
(y-octo 0.1.0 src/doc/store.rs:36,
`pub(crate) type StoreRef = Arc<RwLock<DocStore>>`):

```go
// storeRef is the shared, lock-guarded store: y-octo's StoreRef =
// Arc<RwLock<DocStore>> (src/doc/store.rs:36). The Go pointer *storeRef
// is the Arc, mu is the RwLock, store is the DocStore.
type storeRef struct {
	mu    sync.RWMutex
	store store
}
```

- `store` loses `mu` and keeps everything else, observers included
  (#219: "The store then consists of its data and its observers").
- `Doc` holds `*storeRef` where it holds `*store` today; `Text` likewise
  (text.go's comment already records that the Go follows y-octo in
  letting the type handle hold the store; it now holds the store ref,
  which is the same reading of YTypeRef).
- `Transaction` KEEPS `store *store` (the bare guarded store):
  `transact` becomes a function over `*storeRef` that locks and hands
  `&ref.store` to the transaction, which is yrs's shape (TransactionMut
  holds the write guard, yrs 0.27.2 src/transaction.rs:445). Inside the
  critical section nothing names the lock, so no store or transaction
  method changes except for losing `s.mu`.
- Not `Doc` itself as the lock type: `Text` needs the lock for
  `String` / `Len` / `Observe` / `Insert` / `Delete`, so making `Doc`
  the lock would force `Text` to hold a `*Doc`, which none of the three
  references does from the type handle, and would couple the server and
  Mirror proofs to `Doc` where they only need the store.

Embedding the store by value (not `*store`) mirrors `RwLock<DocStore>`
owning the DocStore, keeps one allocation, and gives the proofs the store
address as a pure field-reference computation off the ref (no extra load,
no persistent-pointer plumbing). If goose fights the field-address idiom
(`&ref.store`), the fallback is a `store *store` field with a
persistently-owned pointer, at the cost of one load per entry point.

Three-way difference to report (in the PR and at the struct): Yjs v14 has
no lock at all; yrs keeps the lock inside the Doc's store cell and
threads access through `TransactionMut` (the write guard); y-octo wraps
the store in `Arc<RwLock<_>>` shared by Doc and the type handles. The Go
follows y-octo for the handle (as it already does today) and yrs for the
transaction (as transaction.go already does); what changes is only that
the lock stops being a FIELD of the store, which none of the three
references has (y-octo's DocStore has no lock field; today's Go deviates
exactly there, and this change removes that deviation).

## 5. The read lock returns a fractional `own_store` (open point 1)

A design choice, not a rule. The spec-shape rules constrain the SPECS of
public functions, and `Text.String` / `Text.Len` already have public
specs; what the read-lock wrapper hands their proofs is proof-internal,
and a proof may open any shape it likes. The choice is uniformity. Today
the reader's view is its own predicate (`store_inv_ro`: the pool, the
item-set authority, the delete-set authority), maintained beside the
public predicate with its own agreement ghost (`pool_frag`) and bridge
laws; after the redesign that parallel family would survive only for the
two read methods. Handing the reader a fraction of `own_store` instead
leaves ONE predicate family at every lock boundary, and the rules'
observation that "a fraction of `own_X` still covers every resource and
is public" says the reader's share is as public a shape as the write
path's. A "read-only view" certificate could not replace it as the single
shape, because the readers really walk the heap (the DLL) and need
fractional points-tos. So:

- `own_store` takes a fraction `q` (every conjunct is fractional:
  points-tos, `own_map`, slices, `own_type_pool` already is, the
  authorities at `●{#q}`, `ghost_map_auth γ q`, the observer token halves
  via `ghost_var` fractions);
- `rlock` peels `rfrac` of `own_store` off the lock invariant (the
  reader-count accounting of issue #22 is unchanged); `runlock` returns
  it, with `own_store_agree` pinning that the state did not move;
- the certificate conversion at the linearization point
  (`store_inv_excl_hist_root`, what lets a reader relate its history
  prefix to the snapshot, issue #125) survives unchanged: at the atomic
  step the invariant is open and the replica history bundle (the history) is
  visible regardless of which fraction leaves.

Two costs come with this shape, and neither reaches the Go.

First, a reader's fraction covers resources a read never touches.
Today `rlock` hands `Text.String` exactly what it uses: a share of the
pool it walks and of the two authorities it compares its certificates
against (`store_inv_ro`). A fraction of `own_store` instead contains a
fraction of every resource of the store, the pending buffers, the
registry map, the clock and client fields and the observers included;
the reader's proof carries those along unread and `runlock` returns
them. This is proof-side plumbing only; `RLock` / `RUnlock` and the
read methods are unchanged.

Second, swallowing the observers into `own_store` would naively break
the lock proofs' later handling, and one exported law repairs it.
Opening the tie invariant yields its content under a `▷`, and at the
lock wrappers' linearization points, inside an atomic step, there is no
program step ahead to strip that later, so whatever the proof needs
there must come out through timeless strips (`>` intros). The
observers' callback contracts (`is_text_callback`, a Hoare triple) are
not timeless, which is why today's `tie_body` places `own_observers`
BESIDE the timeless `tie_store`: the proofs strip the store state with
one `>` intro, through the sealed `Timeless` instance that is also the
compile-time fix of issue #22, and carry the observers under the `▷`
untouched. The new `own_store` contains the observers, so the predicate
as one opaque blob is no longer timeless and that `>` intro would fail.
heap.v therefore exports
`own_store ⊣⊢ own_store_core ∗ own_observers_part`, the split into the
timeless core and the observers half, as a law of the predicate; the
lock wrappers are private to the lock type, so their proofs may rewrite
with it under the `▷` (`▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q`), strip the core, and
keep the observers half under the `▷` exactly as today. The discipline
and the compile-time behaviour of the current lock proofs are
preserved, only now the split is a lemma instead of the shape of
`tie_body`.

## 6. The free functions become methods again (open point 3)

`deleteNode(it *item)` is public for the store (Transaction calls it) and
its spec must take `own_store` whole, but the function does not receive
the store: as a free function, the spec would have to conjure the store
location out of thin air. So it becomes a `*store` method again, which is
what y-octo has (`DocStore::delete_item_inner`; Yjs's `Item.delete` and
yrs's `block.rs` delete sit on the item, a three-way difference already
reported at the function and re-reported in the PR).

`addNode` is private to the store (only `Integrate` calls it), so the
rules do not force anything; it becomes a method anyway
(`DocStore::add_item`) because the reason it was made free, the removed
"footprint visible in the program" rule of old CLAUDE.md "Spec shape", is
gone, and the method form is the faithful one.

`splitItem` stays a free function over the node: its counterpart is
`Item::split_at` (on the item, not the store) in y-octo, and `splitItem`
is private to the store, so both the references and the rules are happy.

The five comments citing `CLAUDE.md "Spec shape"` (on `deleteNode`,
`addNode`, `splitItem` in yjs/store.go, at `addNode` in
src/proof/store/Integrate.v, at `getOrCreateYType` in
src/proof/store/repair.v) are rewritten in the same milestone: the two
method moves get the three-way citation above, `splitItem` gets the
`Item::split_at` justification, and the proof-side comments cite the
spec-shape bullet they actually rely on.

## 7. New-deviation audit

Each rule of spec-shape, against the design above:

- "Values of Cert-Yjs types appear in specs through their predicates":
  satisfied; node pointers keep appearing through the store's predicate
  plus pure slot facts, the fresh item through `own_linked_item`.
- "Public and non-public predicates": `own_store` holds every field of
  the (new, mu-less) store and `store_invs`; the observers' lag
  parameters do not make it non-public, because the catch-up is the LOCK
  type's invariant, not the store's, exactly the boundary #219 draws.
  This reading must be written at the predicate (it is the one judgment
  call in the design).
- "Public and private functions" / "Specs of public functions use only
  public predicates": the eight store functions and the four transaction
  methods close over `own_store` / `own_transaction` (sections 2, 3);
  the lock wrappers (`wlock` / `wunlock` / `rlock` / `runlock`) and
  `notify` are private to the lock type / transaction and may keep
  internal shapes, though after the move even they are statable over
  `own_store` plus the named replica history bundle.
- "Everything a spec says about a value goes through a model parameter":
  unchanged; the cell model is a model. The goose-value binders in the
  PRIVATE scan specs (`wp_scanConflicts` / `wp_findIntegrationLeft`,
  issue #220 item 2) are a separate fix, orthogonal to this plan: those
  functions stay private and keep pool-level predicates either way.
- "Specs stay intuitive": the replica history bundle is ONE named predicate
  (`own_replica_history`), never spilled as loose conjuncts into
  `transact`'s closure contract; `own_transaction` keeps wrapping it.
- "A new conjunct goes into an existing predicate": no new conditions
  are introduced at all; every conjunct is one of today's, relocated.
  The PRs say, per conjunct of the dissolved `own_store_data` /
  `store_inv_excl`, where it went (the table in section 3).
- "No over-specification" / "One spec per function": the
  `wp_store__repair_create` second spec keeps its justification; the
  dissolved predicates take their helper lemmas with them
  (`store_inv_bridge`, `store_slices_own_store_data`, the
  `own_store_data` laws get successors over `own_store ∗
  own_replica_history`, and the ones nothing uses anymore are deleted).
- Naming: `is_Store` today names the lock handle while living on the
  store; it moves to the lock type as `is_store_ref` (with the tie
  invariant inside), freeing the store's `is_X` slot. `own_store_state`
  disappears as a name, so the two-"THE"-predicates confusion fixed
  cosmetically by PR #221 is resolved structurally.

Residual risks, named so the milestones can watch them:

- the fractionalization sweep (section 5) touches every field predicate;
  a conjunct that resists `Fractional` (none identified: `own_map`,
  slices, `ghost_map_auth`, `●{#q}`, `ghost_var` all split) would force
  the reader back to a partial predicate and reopen the deviation;
- the Mirror / server layers and open PR #214 (observers-c3) sit on
  `is_Store` and `own_store`; this work lands after #214 merges or
  rebases onto it, never in parallel;
- goose must accept `&ref.store` (section 4 fallback exists);
- the timeless discipline of the lock proofs (the `tie_body` strip)
  must be re-established over the new shape before the heavy files
  recompile, or the issue-#22 compile-time regression returns.

## 8. Milestones

Each lands green and separately reviewable; the spec-shape fresh-context
review runs before every push that touches a predicate.

- M0, Go and plumbing: introduce `storeRef`, move `mu`, make
  `deleteNode` / `addNode` methods, rewrite the five stale comments,
  re-run goose; proof side only re-plumbs addresses (`is_Store`'s mu
  path, entry points reading the store off the ref). No predicate
  changes meaning.
- M1, the predicate: define the new `own_store` (fields + observers +
  authorities + `store_invs`, fractional) and `own_replica_history`;
  restate the lock wrappers and `own_transaction`; dissolve
  `own_store_data`; keep the method specs on `own_store_state`'s
  successor shape compiling by a bridge law for one milestone.
- M2, the store specs: restate the eight functions over `own_store`,
  moving the authority updates into their proofs; delete the bridge.
- M3, the transaction specs: `integrate`, `deleteNode`, `deleteRange`,
  `applyUpdate`, `notify` over `own_transaction` / `own_store`; the
  `wp_Transaction__deleteNode` deviation closes here.
- M4, the read path: fractional `rlock` / `runlock`, port `String` /
  `Len` / `Poll`, retire `store_inv_ro` / `pool_frag`.
- M5, sweep: headers, dead laws, the #220 item 1 rows checked off.

## 9. What this plan does not do

It does not touch issue #220 item 2 (the goose struct values in the
conflict-scan specs), which is fixable today against the CURRENT
predicates, nor item 5 (findings on PR #214, which belong to that PR's
review). It does not change any model or any Rocq-Yjs interface, and it
does not alter what is proved about convergence or the observers; every
theorem statement outside the store/transaction predicate layer keeps its
meaning with renamed hypotheses.
