# Plan: a verified Text observer, the observe / diff / patch pattern (issue #198)

Status: proposal, 2026-09-13. Nothing implemented; the pure model (O1) and
the Go (O2) can start independently.

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

Pull rather than callback: the callback flavour (y-octo `subscribe`, Yjs
`observe`) is a goroutine loop over `Poll` plus a spec for the callback, and
adds nothing to the theorem (section 7, O7).

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

`value.v`: `own_delta sl delta` (the `[]DeltaOp` slice denoting a
`list DeltaOp`), and the state-vector map and the delete set as the values
of `snapshot_state_vector` / `snapshot_deleted_ids`.

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

Lemma wp_ApplyDelta (s : go_string) (sl : slice.t) (delta : list DeltaOp) :
  {{{ is_pkg_init yjs ∗ own_delta sl delta }}}
    @! yjs.ApplyDelta #s #sl
  {{{ RET (#(default "" (apply_delta delta s)), #(bool_decide (is_Some (apply_delta delta s))));
      own_delta sl delta }}}.
```

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

Where: `pool_invs p` (store/model.v) gains

```
Definition pool_clocks_contiguous (p : pool) : Prop :=
  ∀ q k d, pool_covers p q k d -> ∀ j, (j < clock d)%nat ->
    ∃ q' k', pool_covers p q' k' (MkYjsId (clientId d) j).
```

and `own_store`'s `Hctr` becomes two-sided for the local client (every
`j < uint.nat k` is covered). Maintenance: `addNode` / Integrate for a local
item (`clock = k`, the two-sided `Hctr`) and for a remote one (`input_ready`
gives `doc_model_has m (c, k-1)`, hence covered, hence everything below);
`splitNode`, `deleteRange`, `Text.Delete` (coverage unchanged, the same
no-op transports the delete set uses); `getOrCreateYType` (an empty type).
One store-invariant addition with its transport lemmas, no Go change.

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

- O1 the pure model (section 3), rocq-mcp only.
- O2 Go + goose + tests (section 2): `./build.sh go`, `./build.sh goose`,
  `go test ./yjs/`.
- O3 P1 (section 6.1): the store invariant and its transports, full build.
- O4 `wp_Text__NewObserver`, `wp_TextObserver__Poll` (write lock),
  `wp_ApplyDelta`.
- O5 the demo and the application theorem (section 4), the composition with
  `ApplySyncUpdate`.
- O6 the read-locked `Poll`: the wire delete path grows the ghost set (the
  `deleteRange.v` milestone), the converse tombstone clause in
  `store_inv_ro`, `Poll` over `wp_Store__rlock`.
- O7 (optional) the callback layer: `Text.Subscribe(callback)` as a
  goroutine loop over `Poll`, with the callback spec
  `{{{ own_app a ∗ ⌜app_synced a observed⌝ ∗ own_delta sl delta ∗
  ⌜delta = text_delta observed current⌝ ∗ ⌜snapshot_grows_to observed current⌝ }}}
  callback sl {{{ own_app a' ∗ ⌜app_synced a' current⌝ }}}` (goose passes
  function values: `Codec` in `ApplyEncodedUpdate`); it needs a sleep or a
  wake-up channel and nothing else.

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

## 10. Out of scope

- A Doc-level `on('update')` with an encoded update (y-octo's publisher
  payload): that is the sender-side diff of the sync protocol (`sync.go`
  names it as separate follow-on work), a replica-to-replica update, not an
  application patch.
- Attribute / formatting deltas (Yjs `ContentFormat`), embeds, and non-text
  types (#23 to #27).
- GC of tombstones (the token's delete set only grows, as y-octo's
  `last_deletes`).
