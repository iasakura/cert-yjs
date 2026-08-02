# Design: the P2P causal-delivery layer (model-faithful, transport-agnostic)

Companion to `docs/plan-issue-42-ghost-history.md` (the ghost op-history,
issue #42) and `docs/plan-network-yjs-protocol.md` (the Yjs sync-protocol
transport). This document specifies the **logical delivery layer**: what any
transport must do so that a system of replicas refines the rocq-yjs network
model. It deliberately contains **no wire, no topology, no FFI** — those are
implementation choices, and the Yjs protocol document is *one* implementation
of the interface defined here.

## 0. TL;DR

- The rocq-yjs model (`YjsOperationNetwork`) is **peer-to-peer**: per-node
  event histories, causal delivery, no distinguished server. The #42 ghost
  history refines exactly this, with **no topology constraints anywhere** —
  `history_wf` never mentions who talks to whom.
- The layer's interface is two entry points that already exist in the #42
  plan — call them **mint** and **deliver**: *mint* = the certificate-minting
  `Text.Insert`, and *deliver* = `wp_store__applyUpdate_certs`, whose one
  nontrivial precondition is `batch_ok` (freshness + causal-floor coverage).
  Anything that interacts with the history *only* through mint and deliver
  keeps `is_history` and inherits #40's convergence. Under the **covered-batch
  spec** (§3.1), transports differ **only** in how they discharge `batch_ok`
  at each delivery.
- **The covered-batch precondition is a stepping stone, not the endpoint.**
  Shipping Yjs implementations make `apply_update` *total*: a batch whose
  dependencies are missing is not rejected but parked in a **pending buffer**
  and retried when later updates fill the gap; duplicates are dropped
  internally. §3.1 records that contract (with y-octo/yrs/yjs citations),
  states the target spec (`ready_closure` over per-replica state `(delivered,
  pending)`), and stages it as three specs: the **total heap spec** (no ghost)
  and the **covered-batch spec** (ghost, applicable batches only) are provable
  against today's model; the **arbitrary-arrival spec** (ghost, any input —
  the realistic endpoint) provably *requires* the weakened delivery model
  (§7), because the Yjs release gate is strictly weaker than happens-before
  coverage. The #42 ghost architecture is unaffected throughout: buffered ops
  are ghost-invisible until released (arrival is not delivery).
- Certificates are persistent and transferable, so **transmission is
  unrestricted**: relays forward ops they did not author (`Broadcast` = ghost
  mint, author-gated; physical send = repetition of certified ops). The
  `Hcerts` amendment to #42 makes certificates recoverable from the invariant
  by anyone, so relays need not thread them through local state.
- The layer ships a **guard toolkit** every implementation reuses: state
  vectors characterize delivered sets *exactly* (the **state-vector
  characterization**, needs the `hwf_dense_clocks` discipline), and
  sv-filtering turns any floor-covered certified batch into a `batch_ok` batch
  (the **sv-filter guard**). What remains implementation-specific is **floor
  coverage**, and §5 maps the topology spectrum: two-replica FIFO suffices; a
  FIFO hub suffices (the Yjs protocol doc); own-ops-only mesh does **not**;
  mesh needs explicit floors or the weakened model (§7 — also the
  arbitrary-arrival spec's prerequisite, hence the tracked endpoint).

## 1. Why a separate layer (and why this split)

Three reasons to keep this layer distinct from the Yjs protocol:

1. **Model faithfulness.** The convergence theorems we consume
   (`YjsOperationNetwork_converge_final`) are stated over an arbitrary causal
   network. The refinement obligation is topology-free; baking the star
   topology into the layer would narrow the theorem for no gain.
2. **The OpLib precedent** (`docs/aneris-oplib-artifact.md`): OpLib consumes an
   *abstract* reliable-causal-broadcast specification; RcbLib is one
   implementation. Our mint/deliver interface plays the role of that abstract
   spec; the Yjs sync protocol plays RcbLib's role. The modularity is the
   methodological point of that line of work.
3. **Swap-ability.** A future mesh transport (explicit floors) or the
   weakened-model route (§7) replaces the other document without
   touching this one, #42, or #40.

## 2. Scope and trust

- **Safety only**: "delivered same set ⇒ same document" (#40) and "every
  applied op was validly generated". No liveness/fairness.
- **Trusted peers**: sender-side validity presumes peers run verified code.
  Byzantine input would need receiver-side re-validation (out of scope).
- **One document** (one `γh`), matching #42's single-root-text scope.
- **No topology assumptions in this document.** Star appears only in the
  protocol document, as one way to meet §5's obligation.

## 3. The interface

A **replica** is a store as in #42: persistent `is_history γh`, and a lock
invariant (`store_inv`) owning `own_client_history γh c h` plus the local doc
tied by `history_state_coh h (ts_arr ts_gov)`. The server of the protocol doc
is just a replica that never edits.

The logical layer is touched through exactly two entry points, both already
specified in the #42 plan:

- **mint (local edit).** `wp_Text__Insert` (#42 §6.3): under the store
  lock, integrates locally and runs `history_broadcast`, which appends
  `EvBroadcast op; EvDeliver op` to *this* replica's history and mints the
  persistent certificate `is_op_cert γh op D` with `D ⊆ delivered_ids h`
  (the minting replica's frontier — automatically a correct floor). Minting is
  the **only** authorship-gated operation, guarded by the exclusive
  `own_client_history` token.
- **deliver (remote batch).** `wp_store__applyUpdate_certs` (#42 §6.5):
  requires, per op, `is_op_cert`, and for the batch
  `batch_ok h inputs Ds` — every op is **fresh** (not yet delivered here) and
  its certified causal past is **covered** by
  `delivered_ids h ∪ (earlier ops in the batch)`. `history_deliver_batch`
  advances the ghost history; the existing `applyUpdate` proof does the heap.

> **Definition — *floor* (used throughout both network documents).** The
> *floor* of a batch is the baseline set of op-ids that the batch's certified
> causal pasts are measured against: the ops the batch *assumes are already
> delivered* at the receiver. Formally it is the `F : gset YjsId` of `batch_coh`
> (yjs-protocol doc §5.2); a batch is *self-contained relative to floor `F`*
> when every op's certified causal past `D` satisfies
> `D ⊆ F ∪ {earlier ops in the same batch}`. **Floor coverage** at delivery is
> then `F ⊆ delivered_ids h` — the receiver has actually delivered everything
> the batch stands on — which is exactly the half of `batch_ok` that no local
> computation can supply (§5). Intuition: the floor is the causal "ground
> level" a batch is built on; the term for it elsewhere is *causal context* /
> *dependency set*. A vector-clock protocol ships the floor **on the wire** (so
> the receiver checks coverage directly); the Yjs protocol does **not** carry a
> floor, which is the entire reason the star topology has to pin it structurally
> instead (yjs-protocol doc §4).

mint and deliver are the **only two writers of the ghost history** (plus
one-time allocation) — see the lifecycle table in #42 §3.1. Everything the
transport does between them (`Send`/`Receive`, framing, the sync handshake) is
**invisible to the ghost state**: it moves already-minted certificates and
already-integrated bytes around, never creating or delivering a logical op.
That is why this layer can be specified without a wire: a transport is correct
iff, whenever it delivers, it can meet `batch_ok` (§5) — nothing it does to the
bytes in transit can affect soundness.

**Composition claim (the layer's payoff, stated once #42/#40 land):** any
program whose interactions with `γh` are exclusively mint and deliver maintains
`is_history γh` and every replica's `store_inv`; hence for any two replicas
with equal delivered op sets, #40's convergence applies. There is nothing to
prove *here* — the mint and deliver specs already re-establish everything — but
the claim is worth recording as the contract the transport document programs
against.

**Transmission (a pattern, not an obligation).** The layer places no
constraint on sending: certificates are persistent, hence duplicable and
logically transferable, so any party that ever obtained an op's certificate
may retransmit the op — relays forward ops they did not author. To spare
relays from threading certificates through local state, #42's `history_inv`
carries a copy of every persisted fragment
(`"#Hcerts" ∷ [∗ map] id ↦ p ∈ ops, id ↪[γh.(hn_ops)]□ p`, amendment recorded
in #42 §5.2): opening `is_history` lets anyone duplicate the certificate of
any registered id. What a *wire* must carry so that the **receiver** can meet
the deliver precondition is the transport's design problem (§5).

### 3.1 What shipping implementations actually do: total `apply_update` with a pending buffer

The `batch_ok`-preconditioned deliver entry point assumes the *caller* only
ever hands over applicable batches. No deployed Yjs-family implementation asks
that of its callers — all three make `apply_update` **total** and absorb
inapplicable input into store state (local checkouts; y-octo is normative for
cert-yjs):

- **y-octo** (`y-octo/src/doc/document.rs:242`): `apply_update` iterates
  `update.iter(store.get_state_vector())`; the `UpdateIterator` yields only
  *ready* structs and moves the rest into `pending_structs` +
  `missing_state` (smallest missing clock per client)
  (`codec/update.rs:328–386`). Leftovers merge with the store-held
  `DocStore.pending` (`store.rs:30`) and the loop **retries** whenever an
  integration filled a previously missing clock (`document.rs:276–317`).
  Already-known prefixes are dropped by offset (`update.rs:369–376`) — dedup
  is internal, re-delivery is a no-op.
- **yrs** (`yrs/src/transaction.rs:815–819`, doc comment): "Out of order
  updates from the same peer will be stashed internally and their integration
  will be postponed until missing blocks arrive first." Same shape: trim
  known blocks, integrate, merge remainder into `store.pending`, retry on
  missing-clock progress (`transaction.rs:820–882`).
- **yjs** (v14.0.0-rc.18, `src/utils/encoding.js:246–327`): same store fields
  (`pendingStructs`/`pendingDs`), retry when an incoming update touches a
  missing client or fills its clock (`encoding.js:277–282`), recursion to
  fixpoint (`:322–326`). v14 additionally fills same-author gaps with `Skip`
  placeholder blocks (`:200–203`) — an even more permissive gap policy.
- Pending is **not a silo**: state-as-update encoding merges the pending
  buffer into the emitted diff (y-octo `diff_state_vector(sv, with_pending =
  true)`, `store.rs:769–780`; yjs `encodeStateAsUpdateV2`,
  `encoding.js:400–411`), so anti-entropy re-floods buffered ops.
- Pending fires **even in the star deployment**: y-websocket registers a new
  connection in the relay fan-out (`bin/utils.cjs:261`) before any handshake
  message is sent (`:296`), so a relayed `Update` can reach a client before
  its `SyncStep2` — the client buffers it until the diff arrives. Buffering
  is not a mesh exoticism; it is how the reference deployment absorbs its own
  handshake race (yjs-protocol doc §4).

**The release gate** (v13-family; what the code checks before integrating an
op, `update.rs:280–310, 340–346`): every dependency already *integrated* —
`origin` and `rightOrigin` (cross-client; the same-client case is subsumed by
contiguity), `parent` (fixed for our single root text) — and **per-author
clock contiguity** (no gap below the op's clock). Id-level, for our `Len = 1`
subset:

```rocq
Definition deps (input : IntegrateInput) : gset YjsId :=
  {[ author-predecessor (c, k−1) if k > 0 ]} ∪ {[ origin ]} ∪ {[ rightOrigin ]}.
Definition ready (S : gset YjsId) (input) : Prop := deps input ⊆ S.

(* The (unique) largest Δ ⊆ R enumerable with each op ready over
   S ∪ earlier-released; lfp of a monotone operator, so order-free. *)
Definition ready_closure (S : gset YjsId) (R : gset op) : gset op * gset op.
```

Note `ready` is exactly the per-op precondition the verified core already
consumes: `toItem` resolves (origins present) + `maximalId` (contiguity +
dense clocks) — the model's own integrate gate (`isClockSafe`). What is *new*
is only the closure bookkeeping, not the per-op theory.

**The realistic contract** (target shape; per-replica state = delivered
history `h` plus pending set `P`, both under the store lock):

```rocq
{{{ own_replica γh c (h, P) ∗ own_update sl dq inputs ∗ certs(inputs) }}}
  s @! … @! "applyUpdate" #parent #sl
{{{ RET #(); ∃ Δ P',
    own_replica γh c (h ++ (EvDeliver <$> Δ), P') ∗
    ⌜(Δ, P') = ready_closure (delivered_ids h) ((P ∪ inputs) ∖ delivered_ids h)⌝ }}}
```

Total: no `batch_ok`, no freshness (set semantics absorbs duplicates — sound
because certificates pin the op value per id, no equivocation among trusted
peers). Since `ready_closure` is a deterministic function of
`(delivered, P ∪ inputs)`, the post-state is a **function of the received op
set** — the API-level form of #40's slogan.

**Three specs, each separately meaningful** (named, not numbered, so a mention
carries its own meaning):

- **The total heap spec** (no ghost). Doc extends by a valid replay of `Δ`,
  `YjsArrInvariant` preserved, pending bookkeeping exact. Provable against the
  current model: every released op satisfies `wp_Store__Integrate`'s
  precondition by construction of `ready` (op well-formedness comes from the
  wire/cert side). Needs the Go pending port (the *pending-buffer port*
  milestone, §6). The genuinely new proof content is the
  iterator-refines-`ready_closure` argument.
- **The covered-batch spec** (ghost, applicable batches only). The total heap
  spec plus the history advance when the arrival is floor-covered: `deps ⊆ D`
  (certified pasts contain dependencies), so a covered fresh batch is swallowed
  whole — `Δ ⊇ inputs`, and with the buffer empty, `Δ = inputs`, `P' = ∅`.
  This is exactly #42's `wp_store__applyUpdate_certs` restated on top of the
  total heap spec; the star transport keeps every delivery in this case
  (yjs-protocol doc §4), making "pending stays empty" a provable *invariant*
  of the verified deployment — realistic code, idealized run.
- **The arbitrary-arrival spec** (ghost, any input — the endpoint). The
  contract above, unconditional. **Not provable against the current model**:
  the release gate checks `deps`, but `hwf_causal_delivery` demands the full
  happens-before past at each `EvDeliver`. The gap is semantic, not
  bookkeeping — B mints `z`; A delivers `z`, then mints `x` at an unrelated
  position (so `z ∉ deps(x)` but `z hb x`); `x` alone reaches C, whose gate
  releases it while `z` is still missing. No permutation of the released set
  fixes this (`z` may not have arrived at all), so the arbitrary-arrival spec
  is exactly as strong as the weakened-model route — see §7. It is where
  `apply_update`'s spec stops mentioning the transport altogether.

The #42 ghost architecture is **unchanged by all three specs** (the global
invariant, `history_wf`'s record shape, certificates, the ghost API
`history_alloc`/`history_broadcast`/`history_deliver_batch`): buffering is
ghost-invisible, the model's "deliver" event happens at *release* time, and
under the arbitrary-arrival spec only the *content* of one `history_wf` field
(`hwf_causal_delivery`) weakens — a model-side change (§7), not a plumbing
change.

## 4. The guard toolkit (generic lemmas)

Freshness — the first half of `batch_ok` — is decidable locally and the same
for every transport, via state vectors:

```rocq
Definition state_vector (h : list Ev) : gmap ClientId nat := …  (* per-author max delivered clock + 1 *)
Definition sv_ids (sv : gmap ClientId nat) : gset YjsId := …    (* {(c,j) | j < sv !! c} *)
```

**State-vector characterization (exact dedup).** Under
`history_wf N`, `N !! c = Some h`:
`delivered_ids h = sv_ids (state_vector h)`.
Needs per-author prefix-closedness in clock order (already a consequence of
`history_wf`: authors broadcast in strictly increasing clocks and causal
delivery preserves per-author order) **plus clock density** — an author's
clocks are consecutive. Density is a property of the minting discipline, so it
becomes a `history_wf` field (`hwf_dense_clocks`), established by
`history_broadcast` (the store counter advances one unit per single-char op,
single governed text) and consumed here. *Difficulty: M. Home:
`network_model.v`.* Under trusted peers this is sound; an author that
skipped clocks would only make sv-dedup over-approximate (drop a genuinely-new
op — a completeness, not safety, failure).

**The sv-filter guard.** If a batch satisfies the certified self-containment
`batch_coh` with floor `F` (each op's `D ⊆ F ∪ earlier-in-batch`), the floor
is covered (`F ⊆ delivered_ids h`), and the receiver drops exactly the ops
with `clock < sv[author]` (its current sv), then the remaining subsequence
satisfies `batch_ok h · ·`: dropped ops are delivered (by the state-vector
characterization above), so any later `D`-reference to them is still covered;
retained ops are fresh (same lemma again).
*Difficulty: M. Home: `network_model.v`.*

(`batch_coh` — certificates + ghost floor `F`, never on the wire — is defined
with the transport-facing predicates in the protocol document §5.2; it is
transport-agnostic and any implementation reuses it.)

So every transport's delivery path is: *establish floor coverage somehow* →
sv-filter → sv-filter guard → deliver. The toolkit reduces the transport's
whole correctness problem to **floor coverage**.

Go-side counterpart: `stateVector()` reads the store's per-client run lists
(`store.items`); its verification needs `own_item_map` back in `store_inv`
(issue #29 re-land) — on the critical path for any transport milestone.

**After the pending-buffer port** (§3.1/§6): freshness stops being a caller
problem — dedup happens inside `applyUpdate` (the `∖ delivered_ids h` in the
contract), so the receive-path `filterBySV` step and the sv-filter guard's
role there disappear; the state-vector characterization remains load-bearing
for `SyncStep1`/`diffSince` and *inside* the closure proofs (it is how the Go
dedup is shown exact). Until the pending port lands, the toolkit is used
exactly as above.

## 5. What an implementation must supply: floor coverage across the topology spectrum

The one thing deliver needs that no local computation can produce: at each
delivery, the incoming batch's ghost floor `F` is covered by the receiver's
current delivered set. How hard that is depends on topology:

| topology / discipline | floor coverage | status |
|---|---|---|
| **2 replicas, pairwise FIFO** | ✔ sufficient (two-replica-FIFO lemma below) | this layer's two-replica demo |
| **N replicas, star hub + FIFO links** | ✔ sufficient (hub sequencing; the stream-induction lemma) | the Yjs protocol document |
| **N replicas, mesh, pairwise FIFO, own-ops-only** | ✘ **insufficient** | counterexample below |
| mesh with **explicit floors on the wire** (vector clocks / sv per message) | ✔ sufficient (receiver checks `sv_ids F ⊆ delivered`) | possible, but off the Yjs wire protocol — future |
| **any topology + receiver pending buffer gated on Yjs-readiness** (= what yjs/yrs/y-octo actually ship, §3.1) | not established at all — the gate checks `deps`, not the floor; release order can violate hb-delivery even when every op eventually arrives | ✔ deployed reality, ✘ for **our model**; sound iff the model itself is weakened to the `deps` relation — §7 (the arbitrary-arrival spec) |

**The two-replica-FIFO lemma.** Between exactly two replicas exchanging
their **own** ops in mint order over FIFO channels, every delivery's floor is
covered: an op `y` minted by `A` has causal past ⊆ (A's own earlier ops —
arrive FIFO-before `y`) ∪ (ops A had delivered from `B` — which are `B`'s own
ops, so `B` has them). *Difficulty: M (a two-node instance of the hub
argument; good warm-up for the stream-induction lemma). Home:
`network_model.v` or the wire file.*

**Mesh counterexample (why N > 2 needs more).** `B` mints `x`, sends to `A`
and `C`. `A` delivers `x`, then mints `y` **at an unrelated position**, so
`x ∉ deps(y)` while `x` happens-before `y`, and sends `y` to `C`. Pairwise
FIFO says nothing about the relative arrival of `B→C : x` and `A→C : y`; if
`y` arrives first, its floor contains `x` which `C` lacks — coverage fails.
Nor can `C` *detect* the gap: the Yjs wire carries only `deps` (origin
lookups + author contiguity), which `y` satisfies without `x` — the real
implementations' pending gate (§3.1) would release `y` here. That is
precisely the arbitrary-arrival obstacle: under the model's happens-before
this delivery is mis-ordered; under the `deps` relation it is fine. Hence:
hub (next document), explicit floors, or model weakening (§7).

## 6. Milestones

Named, not numbered; the "depends on" column names its prerequisites too.
The Yjs protocol document's milestones are cross-referenced by their names
(the *Grove spike*, *in-process hub*, *Grove transport*).

| milestone | contents | acceptance | depends on |
|---|---|---|---|
| **Guard toolkit** | `hwf_dense_clocks` field (`history_broadcast` carries it), `Hcerts` amendment, `state_vector`/`sv_ids`/`filterBySV` (Rocq + Go), the state-vector characterization + sv-filter guard | lemmas Qed; `stateVector()` verified | #42's pure bridge / ghost layer / WP rethreading; #29 re-land for `own_item_map` |
| **Two-replica demo** | model-faithful P2P demo: two replicas in one process, direct exchange of own-op batches over an in-process FIFO mailbox (a mutex-guarded queue; no server, no sync protocol), the two-replica-FIFO lemma; end-to-end theorem: after a quiescent exchange the two docs are equal | theorem Qed, axiom-clean; `go test` exercising the real exchange code | guard toolkit, #40 (convergence consumption), #42's applyUpdate-certs spec |
| **Generic mesh transport** *(optional, off the critical path)* | a fully model-faithful **generic** P2P transport over Grove: mesh topology, N replicas, every message carrying an **explicit causal floor** (an sv, on a custom wire format — deliberately *not* the Yjs protocol, which cannot express floors); the receiver checks `sv_ids F ⊆ delivered` and buffers/stalls until covered | multi-replica convergence theorem with no hub and no protocol-specific argument — the direct implementation of the model's causal-broadcast discipline | guard toolkit, two-replica demo; **nothing later consumes it** (the Yjs server does not build on it) |
| **Pending-buffer port — the realistic receiver** (§3.1) | port y-octo's pending machinery to Go, insert-only subset (`store.pending` = pending inputs + missing sv; the iterate-or-pend loop; sv/offset dedup — `document.rs:242`/`update.rs:328` as the source), keeping today's integrate loop as the inner kernel on each released run; prove the **total heap spec** (`(Δ, P') = ready_closure …`) and restate #42's certs spec as the **covered-batch spec** on top (covered ⇒ `Δ = inputs`, `P' = ∅`) | total heap + covered-batch specs Qed, axiom-clean; `go test` includes an out-of-order delivery case (pend then drain); receive path drops `filterBySV` (§4) | **changes `yjs/*.go` behavior — maintainer sign-off per CLAUDE.md before implementation**; depends on #29 (sv), #42's bridge through applyUpdate-certs spec; independent of the Grove spike / in-process hub / Grove transport (the star line runs on the covered-batch spec either way); **the arbitrary-arrival spec additionally needs §7** |

The two-replica demo is the smallest closed system that exercises mint,
deliver, certificates, and the guard toolkit end-to-end — before any protocol
or FFI complexity. The Yjs protocol document's milestones build on the guard
toolkit and two-replica demo — **not** on the generic mesh transport.

**On the generic mesh transport — "build a model-faithful network
implementation first", made precise.** The natural instinct is to implement a
network faithful to the causal-broadcast model before committing to the Yjs
protocol. The generic mesh transport is that project: an RCB-shaped layer
(cf. Aneris's RcbLib, ~5.6k LOC of Coq there; ours would be smaller — safety
only, floors instead of full vector-clock machinery, no retransmission). Two
reasons it is optional rather than the first step: (a) its wire format must
carry floors, which the Yjs protocol cannot, so **none of it is reusable for
the actual deployment target** (the Yjs server) — it would be built and then
set aside; (b) the de-risking value of "faithful implementation first" is
captured by the two-replica demo at a fraction of the cost, because for two
replicas pairwise FIFO already *is* causal delivery (the two-replica-FIFO
lemma) — the demo is a genuine model-faithful exchange with real code, just
minimal. What the generic mesh transport uniquely adds is validation of the §5
mesh row and of the interface's generality; do it if and when that matters
(e.g. for a paper's "the layer is transport-generic" claim), not as a
prerequisite.

## 7. The weakened-model route (the tracked endpoint for realistic verification)

Yjs-family implementations rely on integration needing less than causal
delivery: origins integrated + per-author clock contiguity — the `deps`
relation of §3.1, which is also the model's own per-op integrate gate
(`isClockSafe` + origin resolution). Our model's `causal_delivery` axiom
demands more (the full happens-before past, delivered, in order), which is
*why* floors are needed at all — and why the arbitrary-arrival spec, the
unconditional spec of the implementations' actual `apply_update`, cannot be
proved against it (§3.1's release-order obstacle; §5's counterexample is its
minimal witness).

The route: weaken `hwf_causal_delivery` (equivalently the model's
`causal_delivery` axiom) from hb-past coverage to **`deps`-past coverage**
(transitive closure of origin/rightOrigin/author-predecessor edges), and
re-prove the rocq-yjs network-level convergence (`effect_list_reorder` and
everything above it) under delivery orders that are `deps`-consistent but not
hb-consistent. Consequences worth recording now:

- The **ghost plumbing survives unchanged** (#42's maps, certificates, the
  ghost API `history_alloc`/`history_broadcast`/`history_deliver_batch`); only
  the pure content of one `history_wf` field moves, plus the deliver-step
  lemma gets a sibling whose hypothesis (`deps ⊆ delivered`) is discharged
  *directly by the release gate* — no floor, no wire content, no topology.
  The certificate floor `D` becomes redundant for delivery (kept for value
  agreement / `deliver_has_a_cause` / any theorem that still wants hb).
- With the arbitrary-arrival spec on top, **§5 collapses**: every row is ✔,
  the transport owes the logical layer nothing but eventual message movement,
  and convergence is "equal received sets ⇒ equal documents" with no
  delivery-order caveat.
- The claim being mechanized — YATA converges under `deps`-consistent
  delivery — is exactly the folklore the ecosystem runs on in production and
  has never been machine-checked; this project already found one real
  convergence bug in y-octo (non-adjacent origins out of `ListType::find_pos`),
  so the exercise has ecosystem value beyond our deployment. It is also where
  a genuinely new counterexample would surface if the folklore is wrong.

Substantial lean-yjs/rocq-yjs work — its own upstream project, sequenced
**after** the star line (the guard toolkit and two-replica demo here, the
in-process hub in the protocol doc) proves the covered-case system end to end.
Until then the star deployment needs none of it; after it, the pending-buffer
port's total-heap and covered-batch specs upgrade to the arbitrary-arrival
spec with no change to the Go code or the wire.
