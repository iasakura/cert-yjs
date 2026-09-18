# Plan: a verified Text observer, the observe / diff / patch pattern (issue #198)

Status: Part I (sections 0 to 10, proposed 2026-09-13) is done: O1 to O5 are
merged (main 35193f3, 2026-09-15). Part II (sections 11 to 18, 2026-09-19)
revises O7 and after into synchronous callbacks at the end of a
`Doc.Transact` (issue #206, T1 and T4), retiring the pull API Part I built;
Part I stays as the record of the model, the Go delta and the store
prerequisite it still relies on.

## 0. TL;DR

An application keeps its own state in sync with a Yjs document by
subscribing to changes, taking the event's delta and patching its state
(`ytext.observe(event => patch(event.delta))`). What we verify is the
invariant such an application relies on,

```
app_synced app observed := app = visible_string observed
```

where `observed` is the document snapshot the application last observed
(the tombstone-tagged per-char sequence the read API already speaks in,
issue #125), and the two steps that keep it:

- a pull: `TextObserver.Poll` returns `delta = text_delta observed current`
  for the snapshot `current` it linearizes at, together with
  `snapshot_grows_to observed current`, the CRDT-level "the current state is
  the observed one plus an update";
- a patch: `apply_delta (text_delta observed current) (visible_string observed)
  = Some (visible_string current)`, a pure law.

Together:

```
app_synced app observed -> snapshot_grows_to observed current ->
  ∃ app', apply_delta (text_delta observed current) app = Some app' ∧ app_synced app' current
```

Pull first, then the callback: Part I is the pull API, `Poll` and the
theorem in `apply_delta`; Part II (section 11 onwards) is the callback
flavour, synchronous at the end of a `Doc.Transact`, whose theorem is that
the application's view is the document's at every transaction boundary
(`wp_Mirror__Check`). Part II supersedes the O6 / O7 of section 7.

## 1. Upstream survey

Yjs (`src/types/YText.js`, the `YTextEvent.delta` getter): walk
`target._start`; for each item, `adds(item)` (its clock is at or above the
transaction's `beforeState` for its client) and not deleted gives an
insert; else `deletes(item)` (its id is in the transaction's delete set)
gives a delete; else a live item gives a retain. Adjacent same-kind entries
merge and a trailing retain is dropped. `beforeState` is the document's
state vector before the transaction, `transaction.deleteSet` the ids it
tombstoned.

y-octo (`src/doc/publisher.rs`,
`DocPublisher::subscribe(impl Fn(&[u8], &[History]))`): a thread wakes every
100 ms, compares `store.get_state_vector()` and `store.delete_set` against
`last_update` / `last_deletes`, and on a change hands the subscribers
`store.diff_state_vector(&last_update)` encoded, plus `History` records (id,
parent, content, action). That is an encoded update for relaying to other
replicas (AFFiNE's server), not a positional delta an application can patch
its own state with; y-octo has no `observe`.

What we port: Yjs's delta computation, driven by y-octo's observation token
(a state vector and a delete set as of the last observation) instead of a
transaction's `beforeState` / `deleteSet`. It is a Yjs-derived addition to
the y-octo port and is marked as such in the Go.

## 2. The Go API (`yjs/observe.go`, goose-translated)

```go
// DeltaOp is one entry of a text delta (Yjs YTextEvent.delta, Quill's delta):
// retain length chars, insert content, or delete length chars.
type DeltaOp struct {
    kind    uint8  // deltaRetain / deltaInsert / deltaDelete
    length  uint64
    content string
}

// TextObserver observes one Text incrementally. Its token is what y-octo's
// DocPublisher keeps between wake-ups (last_update / last_deletes): the
// per-client next clock and the tombstoned ids as of the last Poll.
type TextObserver struct {
    text        *Text
    stateVector map[Client]Clock
    deleted     deletedSet          // range.go, goose-visible
}

func (t *Text) NewObserver() *TextObserver             // observes the EMPTY snapshot
func (o *TextObserver) Poll() []DeltaOp                // lock, one walk, classify, advance, unlock
func ApplyDelta(s string, delta []DeltaOp) (string, bool) // the application-side patch
```

`Poll` walks `t.inner.start` once under the store lock. For a run of client
`c` covering clocks `[k, k+len)`:

- `added := k >= stateVector[c]` (Yjs `adds`; per-client contiguity, section
  6.1, makes this exactly "not in the observed snapshot"; a run straddling
  `stateVector[c]` is classified in two parts);
- `wasDeleted := deleted.Contains(id)` (tombstoned at the last poll);
- `isDeleted := Deleted()` (tombstoned now).

added and live: `insert content`; added and deleted: nothing (never visible
to this observer); known and wasDeleted: nothing (invisible before and after,
tombstones never clear); known and isDeleted: `delete len`; otherwise
`retain len`. Adjacent same-kind ops merge and a trailing retain is dropped
(the Yjs normal form), so the result is a function of the two snapshots and
not of where the runs happen to be split. While walking, `Poll` rebuilds the
token: `stateVector[c]` becomes one plus the largest clock walked for `c`,
`deleted` the ids of the tombstoned runs.

`NewObserver` starts from the empty observation (`stateVector = {}`,
`deleted = {}`): the first `Poll` returns the whole visible text as inserts.
That is what removes the need for an atomic "read the string and take the
token" operation: the application starts at `""`, which is
`visible_string []`.

`ApplyDelta` is the pure patch: retain copies, insert emits, delete skips,
and it reports `false` when a retain or a delete runs past the end. The
application calls it; the theorem says it never fails on a `Poll` result.

Tests (`yjs/observe_test.go`): the delta of one insert / one delete / mixed
edits at both ends and in the middle; a remote batch through
`ApplySyncUpdate` (insert-only, with delete spans, with a pending drain);
the property `ApplyDelta(app, Poll()) == String()` over random edit
sequences with several observers polling at different rates; an editor
goroutine racing the observer (race detector).

## 3. The pure model (`src/proof/textobserver/model.v`)

The snapshot type is the read API's, `list (YjsItem A * bool)` (an item and
its tombstone bit), read off a type's runs by `runs_model` (ytype/model.v);
`visible_string` is ytype/value.v's.

```
Inductive DeltaOp := Retain (length : nat) | Insert (content : A) | Delete (length : nat).

(* the Yjs classification of one char of the current snapshot against the observed one *)
Definition delta_step (observed : snapshot) (x : YjsItem A * bool) : option DeltaOp :=
  if decide (x.1 ∈ observed.*1) then
    if decide ((x.1, true) ∈ observed) then None
    else if x.2 then Some (Delete 1) else Some (Retain 1)
  else if x.2 then None else Some (Insert (content x.1)).

(* merge adjacent same-constructor ops, drop a trailing Retain *)
Definition text_delta (observed current : snapshot) : list DeltaOp :=
  delta_normal_form (omap (delta_step observed) current).

(* [] gives Some s (the implicit trailing retain); Retain n / Delete n need n <= length s *)
Fixpoint apply_delta (delta : list DeltaOp) (s : A) : option A.
```

What the CRDT guarantees between two observations, the "current = observed
+ update" of the issue, as a relation on snapshots:

```
Definition snapshot_grows_to (observed current : snapshot) : Prop :=
  sublist observed.*1 current.*1 ∧                                (* new items only interleave *)
  (∀ x, (x, true) ∈ observed -> (x, true) ∈ current) ∧             (* tombstones never clear *)
  (∀ x y, x ∈ current.*1 -> y ∈ observed.*1 ->
     clientId (item_id x) = clientId (item_id y) ->
     clock (item_id x) < clock (item_id y) -> x ∈ observed.*1).    (* per-client contiguity *)
```

The laws:

- `apply_text_delta`: `snapshot_grows_to observed current ->
  YjsArrInvariant current.*1 ->
  apply_delta (text_delta observed current) (visible_string observed) =
  Some (visible_string current)`. The patch law. A merge induction over
  `current`: when its head is in `observed` it is the head of `observed`
  (the sublist, and ids are unique).
- `app_synced_patch`: the corollary in the TL;DR.
- the token laws, relating what the Go computes to membership:
  `snapshot_state_vector observed` (per client, one plus the largest clock
  in `observed.*1`) and `snapshot_deleted_ids observed`;
  `state_vector_classifies`: under `snapshot_grows_to observed current`, for
  `x ∈ current.*1`, `clock (item_id x) < sv_get (snapshot_state_vector
  observed) (clientId (item_id x)) <-> x ∈ observed.*1`;
  `deleted_ids_classify`: `(x, true) ∈ observed <-> x ∈ observed.*1 ∧
  item_id x ∈ snapshot_deleted_ids observed`.
- the `delta_normal_form` theory: `apply_delta` is invariant under
  normalization, and the append law the loop invariant of `Poll` needs.

Nothing here mentions Iris or the code; iterate on it alone with rocq-mcp.

## 4. The Iris layer

Files per the layout: `src/proof/textobserver/{model,value,heap,NewObserver,Poll,ApplyDelta}.v`
and the `textobserver.v` facade; the Require order gains `textobserver`
after `text`.

`value.v`: what a `DeltaOp` struct, the state-vector map and the
deleted-span lists denote (`delta_op_denotes`, `state_vector_denotes`,
`spans_cover`); `heap.v` builds `own_delta sl dq delta` (the `[]DeltaOp`
slice denoting a `list DeltaOp`) and `own_deleted_spans` on them. A count
denotes the model's `nat` as a machine word (`Length' = W64 n`, the way
`yType.len` denotes `runs_visible`): the walk adds `uint64` counts and
nothing in the model bounds a text below `2^64` chars, so the exact
denotation is not provable for `Poll` while the word-level one is,
unconditionally. `delta_fits delta` (every retain and delete count below
`2^64`) is the bound under which the words are the counts; a delta that
patches a Go string fits (`apply_delta_fits`), which is how `ApplyDelta`'s
proof recovers exact counts from its own `len` call. Its spec does not
mention the bound: it is the success triple below, stated on the model's
fact alone.

`heap.v`, the observer predicate (exclusive: the token fields are mutable):

```
Definition own_TextObserver (obs t : loc) (γs : store_names) (γh : history_names)
    (name : P) (observed : snapshot) : iProp Σ :=
  ∃ (parent : loc) (pool_items : gmap loc (gset (YjsItem A))) …,
    obs ↦ … ∗ (the token fields at snapshot_state_vector observed / snapshot_deleted_ids observed) ∗
    is_Text t γs γh name [] ∅ ∗ is_type_binding γs.(sn_types) name parent ∗
    "#Hitems"   ∷ own γs.(sn_seq) (◯ pool_items) ∗                       (* every type's item set at the observation *)
    "%Hthis"    ∷ ⌜pool_items !! parent = Some (list_to_set observed.*1)⌝ ∗
    "%Hcontig"  ∷ ⌜∀ c j, (j < sv_get (snapshot_state_vector observed) c)%nat ->
                     ∃ q it, it ∈ pool_items_get pool_items q ∧ item_id it = MkYjsId c j⌝ ∗
    "#Hdeleted" ∷ is_delete_set_lb γs (snapshot_deleted_ids observed) ∗
    "%Hsorted"  ∷ ⌜YjsArrInvariant observed.*1⌝.
```

Three persistent certificates carry the three conjuncts of
`snapshot_grows_to` across the unlock / lock gap, one each. The whole-pool
item-set fragment `◯ pool_items` (allocated from the `sn_seq` authority by
`auth_update_dfrac_alloc`; it is `is_type_lb` for every type at once) gives,
against the authority at the next poll, `sublist` for this type
(`sorted_subseteq_sublist`) and, with `Hcontig` and one-id-one-slot
(`pool_covers_unique`), the contiguity conjunct: an id below the observed
state vector sat in some type's set at the observation, that set only grew,
and at the next poll the id sits in exactly one slot, so the item found in
this type now was in this type then. `is_delete_set_lb` with
`delete_set_tombstoned` (the tombstone coherence `store_inv_ro` carries)
gives tombstone monotonicity.

Specs:

```
Lemma wp_Text__NewObserver … :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L deleted_ids }}}
    t @! (go.PointerType yjs.Text) @! "NewObserver" #()
  {{{ (obs : loc), RET #obs; own_TextObserver obs t γs γh name [] }}}.

Lemma wp_TextObserver__Poll … (observed : snapshot) (h0 : list Ev) :
  {{{ is_pkg_init yjs ∗ own_TextObserver obs t γs γh name observed ∗
      is_Text t γs γh name L deleted_ids ∗ is_store_client γs c ∗ is_history_lb γh c h0 }}}
    obs @! (go.PointerType yjs.TextObserver) @! "Poll" #()
  {{{ (sl : slice.t) (delta : list DeltaOp) (current : snapshot), RET #sl;
      own_TextObserver obs t γs γh name current ∗ own_delta sl delta ∗
      ⌜delta = text_delta observed current⌝ ∗ ⌜snapshot_grows_to observed current⌝ ∗
      ⌜text_snapshot L current⌝ ∗ ⌜history_reflected h0 name current⌝ ∗
      ⌜visible_excludes deleted_ids current⌝ }}}.

Lemma wp_ApplyDelta (s s' : go_string) (sl : slice.t) (dq : dfrac) (delta : list DeltaOp) :
  apply_delta delta s = Some s' ->
  {{{ is_pkg_init yjs ∗ own_delta sl dq delta }}}
    @! yjs.ApplyDelta #s #sl
  {{{ RET (#s', #true); own_delta sl dq delta }}}.
```

The failing case (a retain or a delete past the end returns `("", false)`)
has no verified caller and is not specified; a `Poll` result patches the
observed text (`apply_text_delta`), which is the premise.

`Poll`'s walk indexes a node's content by a `uint64` offset
(`string(cur.content.content[i])`), which is a valid `int` index only
because a Go string is shorter than `2^63`: the bound Perennial's string
model grants when `len` is called (an angelic assumption). `wp_item__Len`
passes it on in its postcondition, since `Poll` calls `cur.Len()` first.

The `Poll` postcondition is the read API's (`text_snapshot`,
`history_reflected`, `visible_excludes`, all about `current`) plus the two
observer facts. Proof shape: lock; open the type's run view as
`wp_Text__String` does; run the classification walk with the loop invariant
"the ops so far are `text_delta` of the walked prefixes, up to
normalization" (the model's append law); mint the three certificates for
`current` and the new token; unlock. The first cut is under the WRITE lock
(section 6.2); the read-lock version changes the lock wrappers and the
delete-set half only.

The application theorem, on a demo (`observeapp/`,
`src/proof/demo/observe_app.v`): a `mirror` struct holding the application's
string, and `mirror.sync(obs)` = one `Poll` then one `ApplyDelta`, with spec

```
{{{ own_mirror m app ∗ ⌜app_synced app observed⌝ ∗ own_TextObserver obs … observed ∗ … }}}
  m.sync(obs)
{{{ RET #true; ∃ current app', own_mirror m app' ∗ ⌜app_synced app' current⌝ ∗
    own_TextObserver obs … current ∗ ⌜history_reflected h0 name current⌝ }}}
```

the patch always succeeds and the invariant closes on the new snapshot.
Composed with `wp_Doc__ApplySyncUpdate`'s `is_history_lb`, it says every
delivered insert the application holds a receipt for is in its mirror after
the next `sync` (as an item; visibility carries the read API's caveat on
deletes).

## 5. What is in the tree already

- The snapshot vocabulary: `runs_model`, `visible_items` / `visible_string`,
  `text_snapshot`, `history_reflected`, `visible_excludes` (issue #125,
  PR #197).
- The monotone certificates: `is_type_lb` (item sets grow),
  `is_delete_set_lb` (the delete set grows, PR #197), `is_history_lb` (the
  history is a prefix), and `sorted_subseteq_sublist` turning set growth
  into `sublist` (the `inserted_run` technique).
- The read-locked walk: `wp_Store__rlock` / `wp_Store__runlock`,
  `store_inv_ro` with the item-set and delete-set authorities at a fraction
  and `delete_set_tombstoned`, and `wp_yType__Text` as the shape of the walk
  WP.
- The writer's delete-set growth law `own_delete_set_grow` (needs
  `ids_tombstoned S (all_runs p)`, which a walk that saw the runs tombstoned
  has).
- The contiguity gate in the Go and in the model: `depsArrived`'s
  predecessor clause (`store.go`), `input_deps` (`network_model.v`).

## 6. Prerequisites

### 6.1 Per-client clock contiguity of the pool (P1)

Each client's integrated clocks are gap-free from 0: the local client's
because `Text.Insert` consumes `s.clock` one char at a time from 0, the
remote ones because `depsArrived` integrates `(c, k)` only once `(c, k-1)`
is in (`store.go`, y-octo's `state.contains(id)` check; Yjs's
`StructStore.addStruct` throws `unexpectedCase` when a struct does not start
at the previous one's end, and its `getState` is that end). Nothing states
it: `own_store`'s `Hctr` is an upper bound on the local client's clocks, and
`pool_invs` says nothing per client.

The observer needs it because the token is a state vector:
`clock x < stateVector[c]` must mean "x was in the observed snapshot", the
contiguity conjunct of `snapshot_grows_to`.

Where (DONE, O3): `store/model.v` states it over the pool's documents,

```
Definition pool_has (p : pool) (d : YjsId) : Prop :=
  ∃ q tm x, p !! q = Some tm ∧ x ∈ tm_arr tm ∧ item_id x = d.
Definition pool_clocks_contiguous (p : pool) : Prop :=
  ∀ d, pool_has p d -> ∀ j, (j < clock d)%nat -> pool_has p (MkYjsId (clientId d) j).
Definition pool_next_clock (p : pool) (c n : nat) : Prop :=
  (∀ q tm x, p !! q = Some tm -> x ∈ tm_arr tm -> clientId (item_id x) = c ->
     (clock (item_id x) < n)%nat) ∧
  (n = 0%nat ∨ pool_has p (MkYjsId c (n - 1))).
```

`store_invs` (and the lock body `store_inv_excl`) carry
`pool_clocks_contiguous`; the counter clause `Hctr` of `own_store` /
`store_inv_excl` is `pool_next_clock p c (uint.nat k)` (two-sided: nothing at
or above the counter, the clock just below it taken unless the counter is
0); `wp_store__Integrate` and `wp_store__integrateDecoded` take
`pool_next_clock (ss_pool state) (clientId (in_id input)) (clock (in_id input))`
where they took `pool_clock_below`. Transports: a step that keeps every
type's document (`pool_after_split` / `pool_after_repair` /
`pool_after_delete`, or one type rebuilt with the same document) keeps both
facts (`_same_docs` / `_ext`), a fresh empty type too (`_insert_empty`), and
an integrate splice at the client's next clock keeps contiguity
(`pool_clocks_contiguous_integrate`) and moves the next clock past the run
(`_integrate_same`, `_integrate_other`). The remote case reads the
predecessor off `input_ready` through the registry
(`pool_has_doc_model_has`); the local case off the counter clause. The
document starts at clock 0 (`store_tie_init`). No Go change.

### 6.2 The delete-set half: write lock first

To carry tombstone monotonicity across polls the observer mints
`is_delete_set_lb (snapshot_deleted_ids current)`. Under the write lock that
is `own_delete_set_grow` on what the walk saw tombstoned (`ids_tombstoned`,
`doc_model_has` from the registry coherence): no new invariant. Under the
READ lock the authority is fractional and cannot grow; the certificate then
needs the converse of `delete_set_tombstoned` (every tombstoned char's id is
in the ghost set) as a `store_inv_ro` clause, which today is false: the wire
delete path tombstones without growing the ghost (`store/deleteRange.v`
drops its coverage record deliberately and names the delete-side
`is_accepted` analogue as its own milestone). So `Poll` takes the write lock
first (y-octo's publisher thread only reads: a performance point, not a
semantic one), and the read-lock version is O6, after the wire path grows
the ghost set.

## 7. Milestones

- O1 the pure model (section 3), rocq-mcp only. DONE (PR #200).
- O2 Go + goose + tests (section 2): `./build.sh go`, `./build.sh goose`,
  `go test ./yjs/`. DONE (PR #201).
- O3 P1 (section 6.1): the store invariant and its transports, full build. DONE (PR #202).
- O4 `wp_Text__NewObserver`, `wp_TextObserver__Poll` (write lock),
  `wp_ApplyDelta`. DONE: O4a (value, heap, `NewObserver`, `ApplyDelta`) is
  PR #203, O4b (`Poll` and its helpers `deltaSnoc` / `deletedContains`) is
  PR #204.
- O5 the demo and the application theorem (section 4), the composition with
  `ApplySyncUpdate`. DONE (PR #205): `observeapp/` (`Mirror`, `Sync` = one
  `Poll` and one `ApplyDelta`) and `src/proof/demo/observe_app.v`
  (`own_mirror`, `wp_NewMirror`, `wp_Mirror__Sync`). The theorem states the
  new mirror directly, `own_mirror m (visible_string current)`, instead of
  `∃ app', own_mirror m app' ∗ ⌜app_synced app' current⌝` (the same fact,
  one conjunct fewer), and returns the read API's three facts about
  `current`, so the composition with `wp_Doc__ApplySyncUpdate`'s history
  certificate is by instantiating `h0`.
- O6 (the read-locked `Poll`) and O7 (a callback loop over `Poll`) are
  superseded by Part II: under a transaction the observer keeps no token
  between transactions, so the read-locked walk has no purpose, and the
  callback is not a loop over `Poll` but the end of every transaction
  (section 11).

O1 and O2 are independent of O3; O4 needs all three.

## 8. Decisions and alternatives

- Pull, not callback. The callback flavour is O7, built on `Poll`; the
  theorem lives in `Poll` and `apply_delta`.
- A state-vector token (Yjs `beforeState`, y-octo `last_update`), hence P1.
  The alternative that needs no contiguity is a token of observed id RANGES
  per client (the walk records exactly what it saw): sound by construction,
  but the ranges fragment in document order and membership becomes linear in
  the fragments, and under contiguity it degenerates to the state vector
  anyway. P1 is worth having on its own: it is the invariant Yjs asserts.
- The merged normal form, pinned: the spec says
  `delta = text_delta observed current`, not merely "the delta patches". The
  weaker form would admit `[delete everything; insert the new string]`,
  which is not what an observer is for; pinning the Yjs normal form makes
  the returned delta a function of the two snapshots.
- The observer starts empty. `Text.NewObserver` observes `[]`; there is no
  snapshot-plus-token atomic read, and the first `Poll` is the initial load
  (as Yjs applications apply the initial `toDelta()`).
- The deletes token is `deletedSet` from range.go (goose-visible,
  `Contains`) with a goose-visible `addRange` (fragments, merged per client
  at the end of the walk if it ever matters; y-octo's `sort_and_merge`).
- A run straddling `stateVector[c]` cannot arise without a merge pass
  (issue #94, not implemented), but the walk classifies it in two parts
  anyway, so the proof is over the per-char model and needs no
  all-singleton or no-straddle assumption.

## 9. Faithfulness notes (to report with the PRs)

- The observer is a Yjs-derived addition; y-octo has no positional observe.
  Marked in `observe.go`'s header.
- `Poll` under the write lock in O4 (y-octo's publisher only reads); lifted
  in O6.
- P1 states a property the Go already has (`depsArrived` and the local
  clock), matching Yjs's `addStruct` assertion; no behaviour change.
- The Go's delta counts are `uint64` and wrap at `2^64` chars, where Yjs's
  JavaScript numbers do not; the spec denotes them modulo `2^64` and
  `ApplyDelta`'s proof recovers the counts under the Go string bound
  (section 4). No behaviour change; a text that long does not exist.

## 10. Out of scope

- A Doc-level `on('update')` with an encoded update (y-octo's publisher
  payload): that is the sender-side diff of the sync protocol (`sync.go`
  names it as separate follow-on work), a replica-to-replica update, not an
  application patch.
- Attribute / formatting deltas (Yjs `ContentFormat`), embeds, and non-text
  types (#23 to #27).
- GC of tombstones (the token's delete set only grows, as y-octo's
  `last_deletes`).
- Part II adds: nested transactions and reentrant writes from a callback
  (#206 item 2), provenance (`origin`, `local`, T5), the cleanup after the
  observers (run merge, gc, the `update` emit, T3), and `Unobserve`.

## 11. Part II: synchronous callbacks at the end of a transaction

Revision of 2026-09-19, after O1 to O5 merged, with two facts in hand: the
reference base is now Yjs v14, yrs and y-octo (issue #208), and the
Transaction of issue #206 is the boundary the observer wants.

What changes. The document gets Yjs's write scope, `Doc.Transact(f)`: the
store's write lock is taken once, `f` makes its writes with the transaction
handle, and at the end the observers of every type the transaction changed
are called once, synchronously, with that type's delta. `Text.Observe(cb)`
registers a callback. The pull API of Part I (`TextObserver`, `Poll`) is
retired: under a transaction the observer needs no token of its own, since
the transaction records what it inserted and deleted (Yjs v14's
`insertSet` and `deleteSet`); `ApplyDelta`, the delta model and the patch
law stay.

Why callbacks under the lock and not a poll loop: with the callback run
before the transaction releases the lock, the application's view moves
whenever the document moves (a remote update applied by `ApplySyncUpdate`
reaches the application before the next transaction can start), the
lockstep Yjs gets from its single thread; and the transaction gives the
same boundary in the write direction: an index read from the application's
view and the `InsertIn` that uses it happen inside one transaction, so no
remote callback moves the view in between.

The theorem. Per observer a ghost token `own_observed γo s`, "this observer
has been told everything up to the snapshot `s`", split in halves between
the store's lock invariant and the application. The store's half sits at
the type's current snapshot (the lock invariant), the application's half at
the snapshot its state was built from (its own invariant), and the callback
is the only thing that moves either. So inside a transaction, before it
writes, the application's snapshot is the document's:

```
wp_Mirror__Check : {{{ is_Mirror m … }}} m.Check() {{{ RET #true; True }}}
  where Check() = d.Transact(func(tr) { ok = t.StringIn(tr) == m.Text() })
```

The store holds no application predicate: the callback's contract
`is_text_callback` is a first-order specification over the ghost token and
the delta, and the application's state lives under the application's own
lock.

## 12. References

Cited by implementation and version (issue #208): Yjs v14.0.0-rc.18
(`~/ghq/github.com/yjs/yjs`, `git show v14.0.0-rc.18:<path>`), yrs 0.27.2
(`~/ghq/github.com/y-crdt/y-crdt`, commit 03e14a0), y-octo 0.1.0
(`~/ghq/github.com/y-crdt/y-octo`, commit 0241c52). Every place where the
three differ is in section 18 and is reported again at the milestone that
meets it.

**The transaction.** Yjs v14 `src/utils/Transaction.js`: the class (:45)
and its fields `deleteSet` (:60), `insertSet` (:69), `changed` (:86),
`_mergeStructs` (:96), `origin` (:100), `meta` (:105), `local` (:110);
`beforeState` and `afterState` are getters derived from `insertSet` (:136,
:153), no longer recorded. `transact` (:391): a nested call reuses
`doc._transaction` (:398), only the outermost runs `cleanupTransactions`
(:422). yrs `src/transaction.rs`: `TransactionMut` (:445) with
`before_state`, `after_state`, `merge_blocks`, `delete_set`, `insert_set`,
`cleanups`, `changed`, `changed_parent_types`, `subdocs`, `origin`, `local`,
`committed`, `needs_cleanup`; `Doc::transact_mut` takes the store's write
lock and keeps the guard inside the transaction (`src/transact.rs:131-134`);
`commit` runs on drop (`src/transaction.rs:488-492`). y-octo has no
transaction: each operation takes the store's `RwLock` on its own.

**Recording the change.** Yjs `src/structs/Item.js`: `integrate` adds the
item to `transaction.insertSet` (:270) and its parent to `changed` (:274);
`delete` adds to `deleteSet` and `changed` (:366-375).
`addChangedTypeToTransaction` (`src/utils/transaction-helpers.js:211-216`)
skips a type whose own item was inserted in this transaction; a root type
(`_item === null`) is always marked. yrs `src/block.rs`: `insert_set`
(:1085, :1115), `add_changed_type` (:1090), `delete_set` (:635, :864);
`TransactionMut::add_changed_type` (`src/transaction.rs:1314-1324`) applies
the same skip through `before_state`.

**Dispatch.** Yjs `cleanupTransactions` (`src/utils/Transaction.js:211`):
sort the delete set, then for each entry of `changed` call `_callObserver`
(:231-236), which builds a `YEvent` and calls the type's listeners
(`src/ytype.js:760-762`, `callTypeObservers` :619-631); merge, gc and the
`update` emit follow (:266-301). `observe` adds a listener to the type's
handler `_eH` (`src/ytype.js:779-782`). yrs `commit`
(`src/transaction.rs:1031-1045`) calls `call_observers` (:978), which
triggers each changed branch's observers; `Observable::observe`
(`src/types/mod.rs:299`) registers on the branch. y-octo `DocPublisher`
(`src/doc/publisher.rs`): a thread wakes every 100 ms (:13, :60), compares
the state vector and the delete set with `last_update` / `last_deletes`
(:73-75) and hands the subscribers (an `Arc<RwLock<Vec<_>>>`, :18) an
encoded diff (:90, :116); `Doc::subscribe` is `src/doc/document.rs:510`.

**The delta.** Yjs v14 `YEvent.getDelta` (`src/utils/YEvent.js:95-123`)
renders the items in `(insertSet ∖ deleteSet) ∪ (deleteSet ∖ insertSet)`
through `toDelta` with `retainDeletes`; `adds` and `deletes` are membership
in the two sets (:70, :82). yrs `TextEvent::get_delta`
(`src/types/text.rs:1243`, the walk :1315-1340): per item, `txn.has_added`
gives an insert unless also `has_deleted`, `has_deleted` a delete, a live
item a retain. y-octo has no positional delta.

**Bindings.** y-codemirror.next `src/y-sync.js` at `main`: the update hook
forwards editor changes inside `doc.transact(…, this.conf)` and the observer
skips `tr.origin === this.conf`. Provenance (`origin`, `local`) is #206 T5,
out of scope here.

## 13. The Go

Files: `yjs/transaction.go` (new: `Transaction`, `store.transact`,
`Doc.Transact`, `notify`, `textDelta`), `yjs/text.go` (`InsertIn`,
`DeleteIn`, `StringIn`, `Observe`, the wrappers), `yjs/observe.go` (loses
`TextObserver`, `NewObserver`, `Poll`), `yjs/store.go` (the `observers`
field; `tr` on `Integrate` and on the delete path), `yjs/sync.go`,
`yjs/range.go` (`deletedSet` becomes `idSet`).

```go
// Transaction is the scope of one write to the document (Yjs v14 Transaction,
// src/utils/Transaction.js:45; yrs TransactionMut, src/transaction.rs:445;
// y-octo has none): created by transact under the store's write lock, passed
// to every write inside, closed by transact, which notifies the observers of
// the types it changed. Of Yjs's fields this milestone keeps the three the
// observer reads; merge, gc and the update emit (#206 T3) and origin / local
// (T5) come later.
type Transaction struct {
	insertSet idSet           // ids integrated in this transaction (Yjs transaction.insertSet)
	deleteSet idSet           // ids tombstoned in this transaction (Yjs transaction.deleteSet)
	changed   map[*yType]bool // types written in this transaction (Yjs transaction.changed)
}
```

`idSet` is `range.go`'s per-client span list (today's `deletedSet`, with
`Contains` and `addRange`), the shape of Yjs's `IdSet` and yrs's `IdSet`;
renamed because it now records inserts too.

```go
// transact runs f as one transaction: lock, f, notify, unlock (Yjs transact,
// src/utils/Transaction.js:391-422, without the reentrant branch; yrs
// transact_mut with commit on drop). Go has no goroutine identity, so a
// nested Transact cannot be recognised and deadlocks (#206 item 2): f, and
// the callbacks it triggers, use the In-variants and never lock the document.
func (s *store) transact(f func(tr *Transaction)) {
	s.mu.Lock()
	tr := &Transaction{insertSet: newIdSet(), deleteSet: newIdSet(), changed: make(map[*yType]bool)}
	f(tr)
	s.notify(tr)
	s.mu.Unlock()
}

func (d *Doc) Transact(f func(tr *Transaction)) { d.store.transact(f) }
```

Recording, at the two mutation points, where Yjs and yrs record:
`store.Integrate(tr, parent, item)` adds the item's ids to `tr.insertSet`
and `parent` to `tr.changed` (Item.js:270, :274; block.rs:1085, :1090);
`deleteNode(tr, item)` adds to `tr.deleteSet` and marks `item.parent`
(Item.js:366-375; block.rs:635). `tr` is threaded through their callers,
`integrateDecoded`, `applyUpdate`, `deleteRange` and `applyDeleteSpans`. A
split (`splitNode`) records nothing: the right half carries ids that were
already integrated (Yjs pushes it to `_mergeStructs`, T3).

The in-transaction API and the one-write wrappers:

```go
func (t *Text) InsertIn(tr *Transaction, index uint64, content string) // today's Insert body, s.Integrate(tr, …)
func (t *Text) DeleteIn(tr *Transaction, index uint64, length uint64)  // today's Delete body, deleteNode(tr, …)
func (t *Text) StringIn(tr *Transaction) string                        // t.inner.Text()

func (t *Text) Insert(index uint64, content string) {
	t.store.transact(func(tr *Transaction) { t.InsertIn(tr, index, content) })
}
func (t *Text) Delete(index uint64, length uint64) {
	t.store.transact(func(tr *Transaction) { t.DeleteIn(tr, index, length) })
}
func (d *Doc) ApplySyncUpdate(structs []updateItem, deletes []deleteSpan) {
	d.store.transact(func(tr *Transaction) {
		d.store.applyUpdate(tr, structs)
		d.store.applyDeleteSpans(tr, deletes)
	})
}
```

`Insert`, `Delete` and `ApplySyncUpdate` keep their specs. `String`, `Len`
and `GetOrCreateText` keep taking the lock directly: they change no type's
snapshot, so they notify nobody. `Doc.applyUpdate` (the codec route) becomes
a `transact` too.

The observers:

```go
// store.observers: per type, the callbacks Text.Observe registered (Yjs keeps
// the list on the type, ytype.js:779; yrs on the branch, types/mod.rs:299;
// y-octo on the publisher, publisher.rs:18). On the store rather than on the
// yType so that the pool's type cells, the heaviest proof machinery, keep
// their shape: reported as a divergence.
observers map[*yType][]func(delta []DeltaOp)

// Observe registers callback on t (Yjs YType.observe). Under the store lock:
// one immediate call with the whole visible text as inserts (the initial
// load a Yjs binding does with toString() before observing, here atomic with
// the registration), then one call at the end of every transaction that
// changed t, with that transaction's delta (Yjs YEvent.getDelta). Callbacks
// run under the store's write lock: a callback must not lock the document
// again (no Transact, Insert, Delete, ApplySyncUpdate, Observe, String, Len:
// deadlock) and a lock it takes is ordered after the store's. Not callable
// inside a transaction, for the same reason.
func (t *Text) Observe(callback func(delta []DeltaOp)) {
	s := t.store
	s.mu.Lock()
	initial := []DeltaOp{}
	text := t.inner.Text()
	if len(text) > 0 {
		initial = append(initial, DeltaOp{Kind: DeltaInsert, Content: text})
	}
	callback(initial)
	s.observers[t.inner] = append(s.observers[t.inner], callback)
	s.mu.Unlock()
}

// notify is the observer half of Yjs cleanupTransactions
// (Transaction.js:231-236; yrs call_observers, transaction.rs:978): for every
// type the transaction changed and somebody observes, one walk yields the
// delta, shared by that type's callbacks. Go map order: the types are
// notified in no particular order (Yjs: the insertion order of changed).
func (s *store) notify(tr *Transaction) {
	for ty := range tr.changed {
		callbacks := s.observers[ty]
		if len(callbacks) > 0 {
			delta := textDelta(ty, tr.insertSet, tr.deleteSet)
			for i := 0; i < len(callbacks); i++ {
				callbacks[i](delta)
			}
		}
	}
}

// textDelta is Yjs YEvent.getDelta for a text (YEvent.js:95-123; yrs
// TextEvent::get_delta, text.rs:1315-1340): one walk of ty's runs, char by
// char. An id in insertSet is an insert when live and nothing when already
// tombstoned; a known char in deleteSet is a delete; a known tombstoned char
// not in deleteSet was invisible before and after; a known live char is a
// retain. deltaSnoc merges and the trailing retain is dropped: the merged
// normal form, text_delta in the model.
func textDelta(ty *yType, insertSet idSet, deleteSet idSet) []DeltaOp
```

Poll's walk (Part I, section 2) is this walk with the observer's token in
place of the transaction's sets; the loop, `deltaSnoc` and the trailing
retain are reused verbatim.

Tests (`yjs/transaction_test.go`, `yjs/observe_test.go`, `observeapp`), run
with `-race` locally and in CI: several `InsertIn` / `DeleteIn` in one
`Transact` reach a callback as one merged delta; `Observe` on a non-empty
text gets the whole text first; a remote `ApplySyncUpdate` (inserts, delete
spans, a pending drain) reaches the callback once with the batch's delta;
editing one text leaves the other text's observers silent; a mirror patched
by its callback equals the text after every public operation and after a
random sequence; editors on goroutines racing `Observe` and `Check` (the
initial delta and the later ones compose); `ApplyDelta`'s tests stay.

## 14. The Iris layer

The exact model. `own_store s γs γh c h m pend deleted` gains the exact set
of tombstoned ids `deleted` (pinned to the pool's flags, as `m` is pinned to
its items), so that a type's snapshot is a function of the public model:

```
type_snapshot m deleted name := (λ x, (x, bool_decide (item_id x ∈ deleted))) <$> doc_model_get m name
```

the read API's `model`, made exact. The store-internal specs are stated
over `own_store_state` (the pool explicit) and do not change for this; the
public method proofs bind one more existential at the lock.

The transaction. The record, `transaction/heap.v`:

```
own_transaction_changes tr inserted tombstoned changed
  (* the three fields as sets: gset YjsId, gset YjsId, gset loc *)
```

threaded through `wp_store__Integrate` (`inserted ∪ run ids`,
`changed ∪ {parent}`), `wp_deleteNode`, `wp_store__deleteRange`,
`wp_store__applyDeleteSpans` and `wp_store__applyUpdate` (`changed ∪` the
parent of every applied input). The public predicate, `store/heap.v`:

```
own_transaction tr γs γh c h m pend deleted inserted tombstoned changed :=
  own_transaction_changes tr inserted tombstoned changed_locs ∗
  own_store s γs γh c h m pend deleted ∗
  own_observer_registry s γs γh (m ∖ inserted) (deleted ∖ tombstoned) ∗
  ⌜(m ∖ inserted, deleted ∖ tombstoned) is per-client contiguous⌝ ∗
  ⌜changed and changed_locs are one set through the type registry⌝
```

where `m ∖ inserted` drops the items inserted in this transaction and
`deleted ∖ tombstoned` the tombstones it set: the state at the start of the
transaction, what the observers were last told (the registry sits there
until notify). `changed` is what the transaction touched, in type names; a
type outside it has no id in either set, so its snapshot now is its
snapshot at the start, the fact that lets notify skip it. The
in-transaction specs are exact transitions:

```
wp_Text__InsertIn :
  {{{ own_transaction tr γs γh c h m pend deleted I T C ∗ is_Text t γs γh name L D }}}
    t.InsertIn(tr, idx, cs)
  {{{ L' ins h' k0 originLeft originRight, RET #();
      own_transaction tr γs γh c h' (<[RootId name := L']> m) pend deleted (I ∪ char_ids ins) T (C ∪ {[name]}) ∗
      ⌜inserted_run (doc_model_get m name) L' ins cs c k0 originLeft originRight⌝ ∗
      is_Text t γs γh name L' D ∗
      ([∗ list] it ∈ ins, is_op_cert γh (RootId name, OpInsert (input_of_item it))) }}}

wp_Text__DeleteIn :
  … own_transaction … deleted' … T ∪ (deleted' ∖ deleted) … (C ∪ {[name]}) ∗
  ⌜deleted' = deleted ∪ delete_range_ids (type_snapshot m deleted name) idx len⌝ …
    (* delete_range_ids: the ids of the visible chars the Go tombstones, the
       model of findPos plus the split at both ends *)

wp_Text__StringIn :
  {{{ own_transaction tr γs γh c h m pend deleted I T C ∗ is_Text t γs γh name L D }}}
    t.StringIn(tr)
  {{{ RET #(visible_string (type_snapshot m deleted name)); own_transaction tr γs γh c h m pend deleted I T C }}}
```

and the transaction wrapper is higher-order in `f`, as `wp_Once__Do` is:

```
wp_store__transact (f : func.t) (Q : ClientId → list Ev → DocModel → list Input → gset YjsId → iProp Σ) :
  {{{ is_Store s γs γh ∗
      (∀ tr c h m pend deleted,
         {{{ own_transaction tr γs γh c h m pend deleted ∅ ∅ ∅ }}}
           #f #tr
         {{{ h' m' pend' deleted' I T C, RET #();
             own_transaction tr γs γh c h' m' pend' deleted' I T C ∗ Q c h' m' pend' deleted' }}}) }}}
    s.transact(f)
  {{{ RET #(); ∃ c h' m' pend' deleted', Q c h' m' pend' deleted' }}}
```

`wp_Doc__Transact` is the same over `is_Doc`; `wp_Text__Insert` and the
other wrappers are proven by instantiating `f` with the closure and `Q`
with today's postcondition, so the public specs do not change.

The observers. Per observer a ghost token, `own_observed γo s :=
ghost_var γo (1/2) s`: the store's half in the lock invariant, the
application's half wherever it keeps its state. The callback's contract, a
first-order persistent specification:

```
is_text_snapshot γs γh name s :=
  ∃ parent c h,
    is_type_binding γs.(sn_types) name parent ∗ is_type_lb γs.(sn_seq) parent (list_to_set s.*1) ∗
    is_store_client γs c ∗ is_history_lb γh c h ∗ is_delete_set_lb γs (snapshot_deleted_ids s) ∗
    ⌜YjsArrInvariant s.*1⌝ ∗ ⌜history_reflected h name s⌝
  (* what String / Poll say about a snapshot, minted by the writer at call time; persistent *)

is_text_callback γs γh name cb γo :=
  □ ∀ sl dq observed current,
    {{{ own_observed γo observed ∗ own_delta sl dq (text_delta observed current) ∗
        ⌜snapshot_grows_to observed current⌝ ∗ is_text_snapshot γs γh name current }}}
      #cb #sl
    {{{ RET #(); own_observed γo current ∗ own_delta sl dq (text_delta observed current) }}}

wp_Text__Observe :
  {{{ is_Text t γs γh name L D ∗ is_text_callback γs γh name cb γo ∗ own_observed γo [] }}}
    t.Observe(cb)
  {{{ RET #(); is_text_observed γs name γo }}}
```

`is_text_observed γs name γo` is the persistent registration witness ("γo is
one of name's observers": a `□` element of a ghost map `γs.(sn_observers)`
whose authority the registry holds). It is what lets a transaction read the
registry's half without opening it:

```
own_transaction_observed_agree :
  own_transaction tr γs γh c h m pend deleted I T C -∗ is_text_observed γs name γo -∗ own_observed γo s -∗
    ⌜name ∉ C -> s = type_snapshot m deleted name⌝ ∗ own_transaction tr γs γh c h m pend deleted I T C ∗ own_observed γo s
```

The lock invariant clause, `store/heap.v`, in `store_inv_excl` at the
current `(m, deleted)`:

```
own_observer_registry s γs γh m deleted :=
  ∃ observers,
    s.[store, "observers"] ↦ mref ∗ own_map mref (DfracOwn 1) observers ∗
    ghost_map_auth γs.(sn_observers) 1 (the γo of every entry, keyed to its type) ∗
    [∗ map] parent ↦ cbs_sl ∈ observers, ∃ name cbs γos,
      is_type_binding γs.(sn_types) name parent ∗ own_slice cbs_sl (DfracOwn 1) cbs ∗
      [∗ list] (cb, γo) ∈ zip cbs γos,
        is_text_callback γs γh name cb γo ∗ own_observed γo (type_snapshot m deleted name)
```

Every registered observer has been told everything up to the type's current
snapshot: the lockstep invariant, in one clause. Its `□` WPs are not
timeless, so it leaves `wp_Store__wlock` under a `▷` (stripped by the next
program step, `wp_auto_lc`), while the rest of `store_inv` keeps the
`tie_body` timeless trick as it is; `wp_Store__wunlock` takes the registry
at the new `(m, deleted)`, `rlock` and `runlock` pass it through, readers
never touch it.

`wp_store__transact`'s proof: lock; strip the `▷`; build `own_transaction`
at the start state; run `f`; notify: iterate `changed` (`wp_map_for_range`),
and for a type with callbacks run `wp_textDelta` (over `own_store` whole and
the two id sets: `own_delta sl (DfracOwn 1) (text_delta before now)` with
`before = type_snapshot (m' ∖ I) (deleted' ∖ T) name` and
`now = type_snapshot m' deleted' name`, `snapshot_grows_to before now` from
the contiguity clause), mint `is_text_snapshot γs γh name now`, and call
each callback with the entry's half, which comes back at `now`; a changed
type without callbacks and an unchanged type need nothing; close the
registry at `(m', deleted')`; unlock. The model laws this needs
(`textobserver/model.v`): `snapshot_before` (the filter by the two sets),
`delta_step` characterised by membership in them,
`snapshot_grows_to (snapshot_before …) …` from contiguity, and
`text_delta_from_empty` for `Observe`'s initial call.

Layering. `textobserver/{model,value,heap}.v` mention nothing of the store
and move below it in the Require order (`… history -> textobserver -> store
-> text -> doc`); `textobserver/heap.v` keeps `own_delta` and the id-set
predicate (`own_deleted_spans`, renamed `own_id_set`), `own_TextObserver`
goes with the pull API, `ApplyDelta.v` and `wp_deltaSnoc` stay. The observer
predicates above are conjuncts of the lock body and are defined in
`store/heap.v` next to it; they cannot mention `is_Text` (it contains
`is_Store`, whose invariant would contain them: a cycle), so
`is_text_snapshot` is stated over the store witnesses that `is_Text`
projects to. The transaction record is `transaction/heap.v` (below the
store: it is what the store specs mark); `own_transaction` and
`wp_store__transact` are the store's (`store/heap.v`, `store/transact.v`),
the walk `wp_textDelta` is `store/wp_private.v`, `wp_Doc__Transact` is
`doc/Transact.v`, the In-methods and `Observe` are `text/`. The adequacy
theorem (`ws_server_dist_adequate`) gains the `ghost_var` and `ghost_map`
functors.

## 15. The demo and the final theorem

`observeapp`, with Part I's `Mirror` replaced:

```go
type Mirror struct {
	mu   sync.Mutex
	doc  *yjs.Doc
	text *yjs.Text
	view string
}

func NewMirror(d *yjs.Doc, t *yjs.Text) *Mirror // registers the callback; the initial call fills view
//   the callback: m.mu.Lock(); view, ok := yjs.ApplyDelta(m.view, delta); if ok { m.view = view }; m.mu.Unlock()
func (m *Mirror) Text() string  // m.mu.Lock(); v := m.view; m.mu.Unlock(); return v
func (m *Mirror) Check() bool   // m.doc.Transact(func(tr) { ok = m.text.StringIn(tr) == m.Text() })
```

```
is_Mirror m d t γs γh name γo :=
  is_Doc d s_loc γs γh ∗ is_Text t γs γh name [] ∅ ∗ is_text_observed γs name γo ∗
  is_Mutex (m.[Mirror, "mu"]) (∃ s, m.[Mirror, "view"] ↦ visible_string s ∗ own_observed γo s ∗ is_text_snapshot γs γh name s)

wp_NewMirror :
  {{{ is_Doc d s_loc γs γh ∗ is_Text t γs γh name L D }}} NewMirror(d, t) {{{ m γo, RET #m; is_Mirror m d t γs γh name γo }}}
wp_Mirror__Text :
  {{{ is_Mirror m d t γs γh name γo }}} m.Text() {{{ s, RET #(visible_string s); is_text_snapshot γs γh name s }}}
wp_Mirror__Check :
  {{{ is_Mirror m d t γs γh name γo }}} m.Check() {{{ RET #true; True }}}
```

`NewMirror` allocates `γo` with both halves at `[]` (the mirror is `""`,
which is `visible_string []`), proves the closure meets `is_text_callback`
(lock the mirror, agree the halves, `apply_text_delta` gives `ApplyDelta`'s
premise, move both halves to `current`, unlock with the snapshot handed in)
and calls `Observe`. `Check`'s closure: `StringIn` is exact, `Text` returns
the mirror's snapshot with its half, and `own_transaction_observed_agree`
with `C = ∅` makes the two snapshots one. Not provable and not needed:
`m.Text() == t.String()` from outside a transaction (the handles are
monotone, and a remote update may land between the two reads).

## 16. Milestones

Stacked PRs, each green under `./build.sh` and `go test -race`, each
described as what, why and how with the spec and invariant changes before
and after; merged only on explicit instruction.

- C1 the transaction. Go: `Transaction`, `idSet`, `transact` / `Transact`
  (no observers yet), `tr` threaded, `InsertIn` / `DeleteIn` / `StringIn`,
  the wrappers, `Doc.applyUpdate`; tests. Proofs: `own_store` gains
  `deleted`, `own_transaction_changes` through the store specs,
  `own_transaction`, `wp_store__transact` (notify empty), the In-specs, the
  wrappers over `transact` with the public specs unchanged,
  `wp_Doc__Transact`. About four days.
- C2 the observers. Go: `store.observers`, `Observe`, `notify`,
  `textDelta`, the pull API removed with its tests folded into the callback
  tests; tests with `-race`. Proofs: `textobserver` below the store, the
  observer predicates and the lock clause with the `▷` handling in the lock
  lemmas, `wp_textDelta`, notify in `wp_store__transact`,
  `wp_Text__Observe`, `is_text_observed`, `own_transaction_observed_agree`.
  About five days.
- C3 the application. `observeapp`'s `Mirror` (callback, mutex, `Check`),
  `wp_NewMirror`, `wp_Mirror__Text`, `wp_Mirror__Check`, the adequacy
  functors. About two days.

Issue #206: T1 (the transaction) and T4 (the observer over it) are this
plan; T2 (`own_transaction` and the rethreaded write path) is C1's proof
half; T3 (merge, gc, the `update` emit) and T5 (provenance) come after and
are out of scope here.

## 17. Decisions and open points

Decided, with the rejected alternatives:

- Synchronous callbacks at the end of the transaction, not a goroutine loop
  over `Poll` (Part I's O7): the loop is asynchronous, so nothing ties the
  application's view to the document's, and it is throwaway under #206.
- The observer's token is the transaction's record (`insertSet` and
  `deleteSet`, Yjs v14), not a per-type snapshot token kept between
  transactions (v13's `beforeState`, rendered per type) and not the pull
  observer's state vector: the transaction knows exactly what it did, the
  proof carries no certificate across a lock gap, and `changed` says which
  types to walk.
- The pull API goes: with the transaction the callback is the API, y-octo's
  polling publisher is the only reference for a pull, and keeping
  `TextObserver` would keep a second walk, its certificates and a heap
  layer above the store for no theorem. `ApplyDelta`, the delta model and
  the patch law stay.
- A ghost token per observer and no application predicate in the store: the
  store's invariant says what every observer was told, the application's
  says what it did with it, and they meet in the callback. A single-writer
  "writer token" is subsumed by `own_transaction`; observer-relative writes
  (Yjs `RelativePosition` on inserts) are unnecessary once writes live in
  transactions.
- `changed` recorded at `Integrate` and `deleteNode` (the Yjs and yrs
  points), not at the In-methods: `ApplySyncUpdate` then marks exactly the
  types the batch touched. The alternative, walk every observed type at
  every transaction end and call when the snapshot moved, needs no marking
  and is observationally the same, but costs a walk of every observed type
  per transaction; and T3 threads `tr` through the same functions anyway.
- The registry in the store's lock invariant (the store lock protects it in
  Go, as the document lock does in Yjs and yrs), at the cost of a
  non-timeless lock body and of the observer predicates living in
  `store/heap.v`. The alternative, a second Go mutex for the registry
  (y-octo's `RwLock<Vec<_>>`) with a ghost map linking its snapshots to the
  store's, keeps the store layer ignorant of observers but adds a lock to
  the Go and two ghost structures to the proof.
- `Observe` takes the lock itself and is not callable inside a transaction:
  a registration mid-transaction would be at the transaction's current
  state while the registry entry must be at its start state.

To confirm in the plan PR (names spelled out; the defaults are what the
code will use unless told otherwise):

1. `InsertIn(tr, index, content)`, `DeleteIn(tr, index, length)` and
   `StringIn(tr)` for the in-transaction variants; alternatives
   `InsertWith(tr, …)`, or methods on the transaction, `tr.Insert(t, …)`.
   yrs puts the transaction first (`text.insert(&mut txn, index, chunk)`),
   Yjs keeps it implicit; the public one-write `Insert` keeps its name and
   spec, so the variant needs a suffix.
2. `Transaction`, `Doc.Transact(f)`, `store.transact(f)`,
   `Text.Observe(callback)`, `store.observers`, `notify`, `textDelta`,
   `idSet` (today's `deletedSet`).
3. The callback signature `func(delta []DeltaOp)`: the event's payload
   only, no transaction handle (Yjs passes `(event, transaction)`, yrs
   `(&TransactionMut, &TextEvent)`), since a callback must not write until
   reentrancy is designed (#206 item 2).
4. The pull API's removal (C2), and the name of the `textobserver/`
   directory, which afterwards holds the delta type and the observation
   model.
5. `Mirror`'s API: `NewMirror(d, t)`, `Text()`, `Check()`.

## 18. Faithfulness notes: the three-way differences

Reported here, again in each PR that meets them, and in a comment at the
divergence in the Go.

| where | Yjs v14.0.0-rc.18 | yrs 0.27.2 | y-octo 0.1.0 | the Go |
|---|---|---|---|---|
| the transaction | `Transaction` with `insertSet`, `deleteSet`, `changed`, `_mergeStructs`, `origin`, `meta`, `local`, subdocs (Transaction.js:45-110) | `TransactionMut`, the same plus the `before_state` / `after_state` caches, `cleanups`, `committed`, `needs_cleanup` (transaction.rs:445-468) | none: each op locks the store | `insertSet`, `deleteSet`, `changed`; the rest at T3 / T5 |
| the scope | `transact` reentrant through `doc._transaction`, cleanup on the outermost (Transaction.js:391-422) | `transact_mut` holds the store's write guard, `commit` on drop (transact.rs:131, transaction.rs:488) | n/a | `transact`: lock, `f`, notify, unlock; no reentrancy, `tr` explicit (#206 item 2) |
| the in-transaction write API | implicit transaction (`ytext.insert(index, text)`) | transaction first (`text.insert(&mut txn, index, chunk)`) | `text.insert(index, str)`, locks inside | `t.InsertIn(tr, index, content)` and the one-write wrappers |
| recording | `Item.integrate` / `Item.delete` (Item.js:270-274, :366-375); a type inserted in this transaction is not marked (transaction-helpers.js:211) | block.rs:1085-1090, :635; the same skip via `before_state` (transaction.rs:1314) | n/a | `Integrate` / `deleteNode`; only root types exist, always marked |
| dispatch | the end of `cleanupTransactions`, before merge and gc (Transaction.js:211-301) | `commit`, then `call_observers` (transaction.rs:1031, :978) | a thread every 100 ms with an encoded diff (publisher.rs:13-116) | the end of `transact`, synchronous, under the lock |
| the registry | on the type (`_eH`, ytype.js:779) | on the branch (types/mod.rs:299) | on the publisher, `RwLock<Vec<_>>` (publisher.rs:18) | `store.observers` keyed by type: the pool's type cells keep their shape |
| the delta | `getDelta` over `insertSet` / `deleteSet` through `toDelta` (YEvent.js:95-123) | the `get_delta` walk with `has_added` / `has_deleted` (text.rs:1315-1340) | none (no positional observe) | `textDelta`: the same walk per char, verified as `text_delta before now` |
| the callback | `(event, transaction)` | `(&TransactionMut, &TextEvent)` | `(&[u8], &[History])` | `func(delta []DeltaOp)` |
| the initial load | the binding reads `toString()` then observes; atomic by the single thread | the same | n/a | `Observe` calls back with the whole text, under the lock |
| the order of notification | the insertion order of `changed` (a `Map`) | `HashMap` order | n/a | Go map order |
| cleanup after the observers | merge (`tryToMergeWithLefts`), gc, the `update` emit (Transaction.js:266-301) | the same, in `commit` | n/a | none (T3) |
