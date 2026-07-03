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
  plan: **T1 (mint)** = the certificate-minting `Text.Insert`, and **T2
  (deliver)** = `wp_store__applyUpdate_certs`, whose one nontrivial
  precondition is `batch_ok` (freshness + causal-floor coverage). Anything
  that interacts with the history *only* through T1/T2 keeps `is_history` and
  inherits #40's convergence. Transports differ **only** in how they discharge
  `batch_ok` at each delivery.
- Certificates are persistent and transferable, so **transmission is
  unrestricted**: relays forward ops they did not author (`Broadcast` = ghost
  mint, author-gated; physical send = repetition of certified ops). The
  `Hcerts` amendment to #42 makes certificates recoverable from the invariant
  by anyone, so relays need not thread them through local state.
- The layer ships a **guard toolkit** every implementation reuses: state
  vectors characterize delivered sets *exactly* (NL1, needs the
  `hwf_dense_clocks` discipline), and sv-filtering turns any floor-covered
  certified batch into a `batch_ok` batch (NL4). What remains
  implementation-specific is **floor coverage**, and §5 maps the topology
  spectrum: two-replica FIFO suffices (NL5); a FIFO hub suffices (the Yjs
  protocol doc); own-ops-only mesh does **not**; mesh needs explicit floors or
  a weakened model (research note, §7).

## 1. Why a separate layer (and why this split)

Three reasons to keep this layer distinct from the Yjs protocol:

1. **Model faithfulness.** The convergence theorems we consume
   (`YjsOperationNetwork_converge_final`) are stated over an arbitrary causal
   network. The refinement obligation is topology-free; baking the star
   topology into the layer would narrow the theorem for no gain.
2. **The OpLib precedent** (`docs/aneris-oplib-artifact.md`): OpLib consumes an
   *abstract* reliable-causal-broadcast specification; RcbLib is one
   implementation. Our T1/T2 interface plays the role of that abstract spec;
   the Yjs sync protocol plays RcbLib's role. The modularity is the
   methodological point of that line of work.
3. **Swap-ability.** A future mesh transport (explicit floors) or the
   weakened-model research route (§7) replaces the other document without
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

- **T1 — mint (local edit).** `wp_Text__Insert` (#42 §6.3): under the store
  lock, integrates locally and runs G2, which appends
  `EvBroadcast op; EvDeliver op` to *this* replica's history and mints the
  persistent certificate `is_op_cert γh op D` with `D ⊆ delivered_ids h`
  (the minting replica's frontier — automatically a correct floor). Minting is
  the **only** authorship-gated operation, guarded by the exclusive
  `own_client_history` token.
- **T2 — deliver (remote batch).** `wp_store__applyUpdate_certs` (#42 §6.5):
  requires, per op, `is_op_cert`, and for the batch
  `batch_ok h inputs Ds` — every op is **fresh** (not yet delivered here) and
  its certified causal past is **covered** by
  `delivered_ids h ∪ (earlier ops in the batch)`. G3 advances the ghost
  history; the existing `applyUpdate` proof does the heap.

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

T1 and T2 are the **only two writers of the ghost history** (plus one-time
allocation) — see the lifecycle table in #42 §3.1. Everything the transport
does between them (`Send`/`Receive`, framing, the sync handshake) is
**invisible to the ghost state**: it moves already-minted certificates and
already-integrated bytes around, never creating or delivering a logical op.
That is why this layer can be specified without a wire: a transport is correct
iff, whenever it calls T2, it can meet `batch_ok` (§5) — nothing it does to the
bytes in transit can affect soundness.

**Composition claim (the layer's payoff, stated once #42/#40 land):** any
program whose interactions with `γh` are exclusively T1 and T2 maintains
`is_history γh` and every replica's `store_inv`; hence for any two replicas
with equal delivered op sets, #40's convergence applies. There is nothing to
prove *here* — T1/T2's specs already re-establish everything — but the claim
is worth recording as the contract the transport document programs against.

**Transmission (a pattern, not an obligation).** The layer places no
constraint on sending: certificates are persistent, hence duplicable and
logically transferable, so any party that ever obtained an op's certificate
may retransmit the op — relays forward ops they did not author. To spare
relays from threading certificates through local state, #42's `history_inv`
carries a copy of every persisted fragment
(`"#Hcerts" ∷ [∗ map] id ↦ p ∈ ops, id ↪[γh.(hn_ops)]□ p`, amendment recorded
in #42 §5.2): opening `is_history` lets anyone duplicate the certificate of
any registered id. What a *wire* must carry so that the **receiver** can meet
T2 is the transport's design problem (§5).

## 4. The guard toolkit (generic lemmas)

Freshness — the first half of `batch_ok` — is decidable locally and the same
for every transport, via state vectors:

```rocq
Definition state_vector (h : list Ev) : gmap ClientId nat := …  (* per-author max delivered clock + 1 *)
Definition sv_ids (sv : gmap ClientId nat) : gset YjsId := …    (* {(c,j) | j < sv !! c} *)
```

**NL1 (sv characterizes the delivered set — exact dedup).** Under
`history_wf N`, `N !! c = Some h`:
`delivered_ids h = sv_ids (state_vector h)`.
Needs per-author prefix-closedness in clock order (already a consequence of
`history_wf`: authors broadcast in strictly increasing clocks and causal
delivery preserves per-author order) **plus clock density** — an author's
clocks are consecutive. Density is a property of the minting discipline, so it
becomes a `history_wf` field (`hwf_dense_clocks`), established by G2 (the
store counter advances one unit per single-char op, single governed text) and
consumed here. *Difficulty: M. Home: `yjs_network_model.v`.*
Under trusted peers this is sound; an author that skipped clocks would only
make sv-dedup over-approximate (drop a genuinely-new op — a completeness, not
safety, failure).

**NL4 (filter guard).** If a batch satisfies the certified self-containment
`batch_coh` with floor `F` (each op's `D ⊆ F ∪ earlier-in-batch`), the floor
is covered (`F ⊆ delivered_ids h`), and the receiver drops exactly the ops
with `clock < sv[author]` (its current sv), then the remaining subsequence
satisfies `batch_ok h · ·`: dropped ops are delivered (NL1), so any later
`D`-reference to them is still covered; retained ops are fresh (NL1 again).
*Difficulty: M. Home: `yjs_network_model.v`.*

(`batch_coh` — certificates + ghost floor `F`, never on the wire — is defined
with the transport-facing predicates in the protocol document §5.2; it is
transport-agnostic and any implementation reuses it.)

So every transport's delivery path is: *establish floor coverage somehow* →
sv-filter → NL4 → T2. The toolkit reduces the transport's whole correctness
problem to **floor coverage**.

Go-side counterpart: `stateVector()` reads the store's per-client run lists
(`store.items`); its verification needs `is_item_map` back in `store_inv`
(issue #29 re-land) — on the critical path for any transport milestone.

## 5. What an implementation must supply: floor coverage across the topology spectrum

The one thing T2 needs that no local computation can produce: at each
delivery, the incoming batch's ghost floor `F` is covered by the receiver's
current delivered set. How hard that is depends on topology:

| topology / discipline | floor coverage | status |
|---|---|---|
| **2 replicas, pairwise FIFO** | ✔ sufficient (NL5 below) | this layer's demo milestone P2 |
| **N replicas, star hub + FIFO links** | ✔ sufficient (hub sequencing; lemma NL3) | the Yjs protocol document |
| **N replicas, mesh, pairwise FIFO, own-ops-only** | ✘ **insufficient** | counterexample below |
| mesh with **explicit floors on the wire** (vector clocks / sv per message) | ✔ sufficient (receiver checks `sv_ids F ⊆ delivered`) | possible, but off the Yjs wire protocol — future |
| raw-Yjs discipline (origins present + per-author contiguity, no causal floors) | ✔ for Yjs *in reality*, ✘ for **our model** | research route, §7 |

**NL5 (two-replica FIFO suffices).** Between exactly two replicas exchanging
their **own** ops in mint order over FIFO channels, every delivery's floor is
covered: an op `y` minted by `A` has causal past ⊆ (A's own earlier ops —
arrive FIFO-before `y`) ∪ (ops A had delivered from `B` — which are `B`'s own
ops, so `B` has them). *Difficulty: M (a two-node instance of the hub
argument; good warm-up for NL3). Home: `yjs_network_model.v` or the wire file.*

**Mesh counterexample (why N > 2 needs more).** `B` mints `x`, sends to `A`
and `C`. `A` delivers `x`, then mints `y` (so `x` happens-before `y`) and
sends `y` to `C`. Pairwise FIFO says nothing about the relative arrival of
`B→C : x` and `A→C : y`; if `y` arrives first, its floor contains `x` which
`C` lacks — coverage fails, and there is nothing on the Yjs wire that would
even let `C` *detect* which ops are missing beyond origin lookups (weaker than
the model's happens-before). Hence: hub (next document), explicit floors, or
model weakening.

## 6. Milestones

| M | contents | acceptance | depends on |
|---|---|---|---|
| **P1** | the toolkit: `hwf_dense_clocks` field (G2 carries it), `Hcerts` amendment, `state_vector`/`sv_ids`/`filterBySV` (Rocq + Go), NL1, NL4 | lemmas Qed; `stateVector()` verified | #42 M1–M3; #29 re-land for `is_item_map` |
| **P2** | model-faithful P2P demo: two replicas in one process, direct exchange of own-op batches over an in-process FIFO mailbox (a mutex-guarded queue; no server, no sync protocol), NL5; end-to-end theorem: after a quiescent exchange the two docs are equal | theorem Qed, axiom-clean; `go test` exercising the real exchange code | P1, #40 (convergence consumption), #42 M4 |
| **P3** *(optional, off the critical path)* | a fully model-faithful **generic** P2P transport over Grove: mesh topology, N replicas, every message carrying an **explicit causal floor** (an sv, on a custom wire format — deliberately *not* the Yjs protocol, which cannot express floors); the receiver checks `sv_ids F ⊆ delivered` and buffers/stalls until covered | multi-replica convergence theorem with no hub and no protocol-specific argument — the direct implementation of the model's causal-broadcast discipline | P1, P2; **nothing later consumes it** (the Yjs server does not build on it) |

P2 is the smallest closed system that exercises T1, T2, certificates, and the
guard toolkit end-to-end — before any protocol or FFI complexity. The Yjs
protocol document's milestones (N0–N3) build on P1/P2 — **not** on P3.

**On P3 — "build a model-faithful network implementation first", made
precise.** The natural instinct is to implement a network faithful to the
causal-broadcast model before committing to the Yjs protocol. P3 is that
project: an RCB-shaped layer (cf. Aneris's RcbLib, ~5.6k LOC of Coq there;
ours would be smaller — safety only, floors instead of full vector-clock
machinery, no retransmission). Two reasons it is optional rather than the
first step: (a) its wire format must carry floors, which the Yjs protocol
cannot, so **none of it is reusable for the actual deployment target** (the
Yjs server) — it would be built and then set aside; (b) the de-risking value
of "faithful implementation first" is captured by P2 at a fraction of the
cost, because for two replicas pairwise FIFO already *is* causal delivery
(NL5) — P2 is a genuine model-faithful exchange with real code, just minimal.
What P3 uniquely adds is validation of the §5 mesh row and of the interface's
generality; do it if and when that matters (e.g. for a paper's "the layer is
transport-generic" claim), not as a prerequisite.

## 7. Research follow-up: the weakened-model route (not now)

Raw Yjs converges over arbitrary topologies because its integration needs less
than causal delivery: origins present + per-author clock contiguity. Our
model's `causal_delivery` axiom is stronger, which is *why* floors are needed
at all. Weakening the model to Yjs's actual requirement would make the
own-ops-only mesh row of §5 sound — but it means re-proving the iris-yjs
network-level convergence (`effect_list_reorder` and everything above it)
under a weaker delivery discipline where the delivery order is no longer
hb-consistent. Substantial lean-yjs/iris-yjs work; tracked as a note, pursued
only if a non-star deployment ever matters. The star deployment (the actual
target) does not need it.
