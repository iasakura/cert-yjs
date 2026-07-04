# Design: the Yjs sync-protocol transport (star topology over Grove)

One implementation of the transport interface in
`docs/plan-network-p2p-layer.md`: a **Yjs server (hub) and N clients** speaking
**y-protocols/sync** (SyncStep1 / SyncStep2 / Update) over **Perennial's Grove
FFI**. Its entire correctness job, per that interface, is to discharge
**floor coverage** at every delivery (the deliver entry point's `batch_ok`,
via the guard toolkit's state-vector characterization + sv-filter guard);
everything Yjs-protocol-specific below exists to that end.

No network code exists yet; this fixes the target. Perennial citations are
into `mit-pdos/perennial` (local checkout).

**Sequencing — why this document exists before any of its work can start.**
Everything here is the *last* stage of the network story; the working order is

```
#42 (ghost history) → #40 (convergence) → guard toolkit + two-replica demo
    (p2p-layer: model-faithful exchange) → in-process hub → Grove transport
```

with only the **Grove spike** (the feasibility spike, issue #45) runnable
early — and already executed. The design was written first because its
wire-level constraints fed *backwards* into #42: the discovery that Yjs
`Update`s carry no causal floor forced the star + FIFO decision and the
`Hcerts` / `hwf_dense_clocks` amendments, which had to be in #42's plan before
#42 is implemented. Read this document as the recorded target and the source
of those requirements, not as current work. (If a *generic* model-faithful P2P
implementation — floors on the wire, no hub — is ever wanted as an
intermediate stage, that is the p2p-layer document's optional generic mesh
transport; no milestone here builds on it.)

## 0. TL;DR

- **Grove**: one global `gmap endpoint (gset message)`; `Send` atomically adds
  to the receiver's mailbox set, `Receive` nondeterministically samples it —
  duplication, reordering, loss; **no FIFO**. Specs are Hoare triples over a
  per-endpoint points-to `e c↦ ms` you place in a shared invariant yourself.
  In Perennial **New** the GooseLang code model of `gokv/grove_ffi` exists but
  the WP wrapper layer is a stub with no upstream consumer — building it is the
  **Grove spike** milestone (upstream candidate).
- **The star + FIFO argument**: Yjs `Update`s carry no causal *floor* (the
  set of ops a batch assumes already delivered — its dependency baseline;
  defined in the p2p-layer doc §3), so a receiver cannot *decide* coverage over
  an arbitrary topology (p2p-layer doc §5). A **hub with FIFO links** yields
  coverage by construction: the server
  relays every batch it applies, in apply order, to every other connection
  (the **stream-induction lemma**). FIFO over Grove's unordered mailboxes is
  restored by a small sequence-numbering layer whose ghost is one `mono_list`
  per direction per connection. This matches the y-websocket deployment (§4's
  reality note for the one divergence) and is *why* the wire protocol can omit
  floors. Role update (p2p-layer doc §3.1): real Yjs `apply_update` is
  *total* — it buffers non-applicable input rather than requiring covered
  batches — so once the **pending-buffer port** lands, this discipline is no
  longer what makes `applyUpdate` safe to call; it is what keeps every
  delivery in the **covered-batch spec**, i.e. it makes "the pending buffer
  stays empty" a provable invariant of the verified deployment. The
  unconditional **arbitrary-arrival spec** is the weakened-model route,
  p2p-layer doc §7.
- **Protocol mapping**: SyncStep1 (state vector) is advisory — no safety
  payload; SyncStep2/Update carry certified batches; the receive path is
  process-in-stream-order → sv-filter (state-vector characterization +
  sv-filter guard) → `wp_store__applyUpdate_certs`.

## 1. Scope

Star topology, one server + N clients, one connection each; one document
(room) = one `γh` — a multi-room server runs one instance per room keyed by
the y-websocket room name (plumbing only). Safety-only, trusted peers, as in
the p2p-layer document §2. Reconnection/resumption: a fresh Step1/Step2
re-handshake is *safe* by design (dedup), but its spec is future work (§9).

## 2. Perennial's distributed model, precisely

### 2.1 The Grove FFI (semantics — shared by old goose and New)

`src/goose_lang/ffi/grove_ffi/impl.v`:

- Global network state: `grove_net : gmap endpoint (gset message)` with
  `Record message := Message { msg_sender : endpoint; msg_data : list u8 }`
  (`impl.v:67`). One mailbox **set** per endpoint (`endpoint` = `w64`).
- `SendOp` atomically inserts into the *receiver's* set; it may fail early
  (nothing sent) or **fail late** (message inserted, error still reported) —
  at-most-once per call, and retries duplicate.
- `RecvOp` on a connection `(c_l, c_r)` nondeterministically returns either
  `err` or some `Message c_r data ∈ ms` from the receiver's own mailbox
  `c_l c↦ ms`, **without removing it** — duplication, reordering, loss.
  Receive is already filtered to the connection's peer `c_r`, so
  per-connection message streams are natural.

### 2.2 The spec layer (old goose — to be lifted to New in the Grove spike)

`src/goose_lang/ffi/grove_ffi/grove_ffi.v`:

```rocq
Notation "c c↦ ms" := (pointsto (L:=endpoint) (V:=gset message) c (DfracOwn 1) ms)   (* :75 *)

Lemma wp_ListenOp (c : w64) : {{{ True }}} … {{{ RET listen_socket c; True }}}      (* :191 *)
Lemma wp_ConnectOp c_r :
  {{{ True }}} … {{{ err c_l, RET (#err, …); if err then True else c_l c↦ ∅ }}}     (* :201 *)
Lemma wp_AcceptOp c_l : {{{ True }}} … {{{ c_r, RET connection_socket c_l c_r; True }}} (* :221 *)
Lemma wp_SendOp c_l c_r ms l data :
  {{{ c_r c↦ ms }}} …
  {{{ err_early err_late, RET #(err_early || err_late);
      c_r c↦ (if err_early then ms else ms ∪ {[Message c_l data]}) }}}              (* :231 *)
Lemma wp_RecvOp c_l c_r ms :
  {{{ c_l c↦ ms }}} …
  {{{ err data, RET (#err, #data); ⌜if err then True else Message c_r data ∈ ms⌝ ∗ c_l c↦ ms }}} (* :246 *)
```

Consequences that shape everything below:

- `Send` needs the **receiver's** `c↦` → the sender opens the *receiver's*
  mailbox invariant around one atomic `ExternalOp` and must re-establish the
  per-message predicate for the inserted message — where "only certified ops
  travel" becomes a proof obligation.
- `Receive` needs only your **own** `c↦` and returns the set unchanged → the
  per-message predicate must be **persistent** (the message stays and can be
  received again), and is extracted as a copy.
- `wp_ConnectOp` allocates the client's fresh mailbox `c_l c↦ ∅`;
  `wp_AcceptOp` gives the server *no* resources about the new peer — logical
  handles for the reply direction must travel with the client's first message
  (§5.3).
- Initialization: `ffi_global_start` hands out `e c↦ ms` for every endpoint
  in the initial net map, and a grove adequacy theorem exists
  (`goose_lang/ffi/grove_ffi/adequacy.v`) — a **closed-system theorem**
  (server + clients from initial state) is expressible (a Grove-transport
  stretch goal).

### 2.3 Status in Perennial New, and the Go side

- `new/trusted_code/github_com/mit_pdos/gokv/grove_ffi.v` defines the New code
  model of the **real Go package** `github.com/mit-pdos/gokv/grove_ffi`
  (`Listen/Connect/Accept/Send/Receive` as GooseLang `val`s over the same
  `ExternalOp`s; `Connection.t := loc`), re-exporting the old semantics
  (`Existing Instances grove_op grove_model`).
- `new/manualproof/github_com/mit_pdos/gokv/grove_ffi.v` — the New WP layer —
  is a **stub** (8 lines). No file in perennial@HEAD imports the trusted code,
  so the goose-translation wiring for a Go import of `gokv/grove_ffi` is
  **unexercised**. The Grove spike validates the pipeline end-to-end and writes
  the wrapper WPs (New-style, `own_slice` bytes, delegating to the `wp_*Op`
  lifting lemmas). Upstream candidate; mechanical (~150 lines by analogy with
  other manualproof files). Tracked as issue #45 (also covers recovering the
  removed urpc/memkv mailbox-invariant precedents from perennial history).
- Deployment: `gokv/grove_ffi` is a real Go package (TCP underneath), so
  verified binaries run unmodified. cert-yjs proofs are FFI-parametric
  (`Context {hG: heapGS Σ, !ffi_semantics _ _}`), so existing results transfer
  to the grove instantiation; only closed top-level theorems fix the FFI.

## 3. The protocol, mapped

y-protocols/sync over one bidirectional connection:

| wire message | payload | logical content |
|---|---|---|
| `SyncStep1(sv)` | state vector | **advisory**: "I claim to have delivered `sv`". No safety payload — a wrong `sv` yields a wrong *diff* (superset ⇒ deduped on arrival; subset ⇒ completeness loss, never corruption). Wire predicate: pure well-formedness only. |
| `SyncStep2(update)` | diff against the peer's `sv` | certified batch, self-contained relative to the **requester's own sv** — the one floor a receiver knows locally (it sent it, and its frontier only grew) |
| `Update(update)` | incremental batch | certified batch, self-contained relative to the sender's stream history (§4) |

Handshake (y-websocket): on connect each side sends `SyncStep1`; each answers
with `SyncStep2`; thereafter live `Update`s. The server **relays** every
applied `Update` to all other connections, in apply order — that relay
discipline is load-bearing (§4), not an optimization.

## 4. Why star + FIFO discharges floor coverage

With one hub and FIFO per-connection streams:

- *Client → server*: when the server processes client `u`'s op `y` (in stream
  order), `y`'s causal past is `P ∪ O`: `P` = the prefix of the **server's
  own outbound stream** that `u` had processed before minting `y` — the server
  delivered all of `P` before it even sent it; `O` = `u`'s own earlier ops —
  arrived FIFO-before `y` on the same stream. Covered. ✓
- *Server → client*: the server's outbound stream to `v` is
  `SyncStep2(diff vs sv_v)` followed by **every batch the server subsequently
  applies, in apply order**. When `v` processes entry `n`: the diff's floor is
  `sv_v` (`v`'s own past frontier — monotone since), and every later entry's
  content was delivered by the server under this same argument and forwarded
  to `v` in order, inductively. Covered. ✓
- Base case: `v`'s own `SyncStep2` to the server is self-contained relative to
  the server-prefix `v` had plus `v`'s own ops inside the same batch.

This is the classic "a sequencer gives causal order for free", and it is why
the wire protocol can omit floors. **FIFO over Grove** is restored by framing
every payload as `(seq n, payload)` and processing `n` only after `n−1`
(buffering ahead-of-order arrivals, dropping duplicates by counter). Loss ⇒
the stream stalls; safety unaffected; no retransmission needed for safety.

**Reality note — the Step2-first stream discipline is a deliberate
strengthening of y-websocket.** The server→client argument above needs the
outbound stream to *start* with `SyncStep2` (the §5.4 relay obligation).
y-websocket itself does not guarantee this: `setupWSConnection` registers the
connection in the relay fan-out (`bin/utils.cjs:261`) before the handshake
even starts (`:296`), and `updateHandler` broadcasts to **all** registered
connections (`:80–85`) — so a relayed `Update` can reach a fresh client
before its `SyncStep2`, and the real client absorbs it with the pending
buffer (p2p-layer doc §3.1). Our verified server queues relays behind the
connection's Step2 instead, which is what makes the covered-batch spec — and
"pending stays empty" — provable; the race-tolerant behavior is recovered,
without any wire change, by the arbitrary-arrival spec when the weakened-model
route lands (p2p-layer doc §7).

## 5. Ghost architecture of the wire

Per connection, gnames bundled in `conn_names := { cn_c2s : gname; cn_s2c : gname }`.

### 5.1 Per-direction stream ghosts

Two `mono_list (leibnizO syncPayload)` per connection (Perennial's wrapper:
`new/ghost/mono_list.v` — `mono_list_auth_own` / `mono_list_lb_own` /
`mono_list_idx_own`; the idx form is persistent, exactly what a wire message
needs):

- the **sender** holds `mono_list_auth_own γdir 1 sent` in its lock invariant
  and appends (`mono_list_auth_own_update_app`) before each `Send`;
- each wire message `(n, payload)` is pinned by the persistent
  `mono_list_idx_own γdir n payload` — two receives of "message n" agree on
  the payload; in-order processing by counter makes handling exactly-once;
- the **receiver** holds a processed-counter and (persistently) the lb of the
  processed prefix.

### 5.2 Per-message wire predicates

```rocq
(* Decoded-level payloads; bytes enter only at the Grove transport via the codec relation. *)
Inductive syncPayload :=
  | SyncStep1 (sv : gmap ClientId nat)
  | SyncStep2 (inputs : list (IntegrateInput (A := A)))
  | SyncUpdate (inputs : list (IntegrateInput (A := A))).

(* Transport-agnostic: certificates + a ghost floor (never on the wire).
   Which F a stream entry may use is constrained by stream_coh (§5.4). *)
Definition batch_coh (γh : history_names) (inputs : list _) : iProp Σ :=
  ∃ (Ds : list (gset YjsId)) (F : gset YjsId),
    ([∗ list] input;D ∈ inputs;Ds, is_op_cert γh (OpInsert input) D) ∗
    "%Hself" ∷ ⌜∀ i input D, inputs !! i = Some input → Ds !! i = Some D →
                  D ⊆ F ∪ list_to_set (in_id <$> take i inputs)⌝.

Definition payload_coh γh (p : syncPayload) : iProp Σ :=
  match p with
  | SyncStep1 sv => ⌜sv_wf sv⌝
  | SyncStep2 inputs | SyncUpdate inputs => batch_coh γh inputs
  end.

Definition msg_coh γh (dir : gname) (m : message) : iProp Σ :=
  ∃ n payload, ⌜frame_dec m.(msg_data) = Some (n, payload)⌝ ∗
               mono_list_idx_own dir n payload ∗ payload_coh γh payload.

(* One mailbox invariant per endpoint; msg_coh is persistent, as Grove's
   set semantics requires (§2.2).  Φfirst covers first-contact messages
   from not-yet-known peers (§5.3). *)
Definition is_inbox γh (e : endpoint) (Φfirst : message → iProp Σ) : iProp Σ :=
  inv wireN (∃ ms, e c↦ ms ∗ [∗ set] m ∈ ms, (msg_coh γh (dir_of m) m ∨ Φfirst m)).
```

### 5.3 Connection establishment (handle escrow)

`wp_AcceptOp` yields no resources about the peer, so logical handles travel
with the first message:

- The client, after `Connect` (fresh `c_l c↦ ∅`), allocates its own inbox
  invariant `is_inbox γh c_l …` and its `conn_names`, then sends its first
  frame (`SyncStep1`).
- The **server-inbox** `Φfirst` for a first-contact message from endpoint `c`
  carries, persistently: `is_inbox γh c …` (so the server may later `Send` to
  `c`) and the `conn_names` structure for both directions. The server's
  receive loop extracts these copies into its per-connection table.
- The **server's own** inbox invariant + `is_history γh` are allocated at
  system init (from `ffi_global_start`'s `e c↦ ∅` for the well-known server
  endpoint) — the static configuration every client is verified against.

### 5.4 Stream coherence (where the star argument lives)

The lock invariants tie streams to histories:

- **Client `u`'s lock** (extends #42's `store_inv`): auth of its outbound
  stream; processed-counter into the server's outbound stream; pure tie: `u`'s
  delivered history = (initial Step2 floor) ∪ (processed server-stream prefix)
  ∪ (own minted ops), in stream order.
- **Server's lock**: per connected client — auth of the server-outbound
  stream, equal to `Step2(diff)` followed by *every batch the server applied
  since, in apply order* (the **relay obligation**, an equality between the
  stream tail and a suffix of the server's delivered order); processed-counter
  into that client's inbound stream; plus the server's own
  `own_client_history γh c_srv h_srv`.

**Stream induction ⇒ floor coverage.** With these ties, when a receiver
processes stream entry `n` in order, the entry's ghost floor `F` satisfies
`F ⊆ delivered_ids (its current history)` — §4's two bullets made precise per
direction. Combined with the guard toolkit (the state-vector characterization
+ sv-filter guard, p2p-layer doc §4) this discharges the deliver entry point's
`batch_ok` with **no wire-level floor and no undecidable receiver check**.
*Difficulty: H — the transport's central lemma; where the star topology and
the relay obligation are consumed. Home: new `yjs_wire.v`.*

## 6. Specs

### 6.1 Transport wrappers (Grove spike / Grove transport)

```rocq
Lemma wp_Send γh (c : Connection.t) (s : slice.t) (data : list w8) dir n payload :
  frame_dec data = Some (n, payload) →
  {{{ is_inbox γh (remote c) Φ ∗ s ↦* data ∗
      mono_list_idx_own dir n payload ∗ payload_coh γh payload }}}
    grove_ffi @ "Send" #c #s
  {{{ (err : bool), RET #err; s ↦* data }}}.
    (* err covers early AND late failure; on late failure the message IS in
       flight — callers rely only on the invariant, never on delivery. *)

Lemma wp_Receive γh (c : Connection.t) :
  {{{ is_inbox γh (local c) Φ }}}
    grove_ffi @ "Receive" #c
  {{{ (err : bool) (s : slice.t) (data : list w8), RET (#err, #s);
      s ↦* data ∗ (⌜err⌝ ∨ ∃ n payload, ⌜frame_dec data = Some (n, payload)⌝ ∗
                    mono_list_idx_own (dir_of …) n payload ∗ payload_coh γh payload) }}}.
```

At the in-process hub the same two shapes are stated against an in-process
mailbox module (a mutex-guarded queue of `syncMsg` structs) — deliberately
identical, so the Grove transport is a transport swap.

### 6.2 The receive/processing loop (per connection)

```
loop:
  (err, data) := Receive(conn); if err retry
  (n, payload) := decode frame
  if n ≠ processed_count: buffer (n > p) or drop (n < p); continue   // FIFO/exactly-once
  lock store
  match payload:
    SyncStep1(sv)   => reply SyncStep2(diffSince(sv))                          // §6.3
    SyncStep2(b) | SyncUpdate(b) =>
      fresh := filterBySV(b)                       // state-vector char.: exact dedup
      applyUpdate(parent, fresh) via wp_store__applyUpdate_certs (deliver)
        -- batch_ok from stream-induction (floor) + sv-filter guard (filter)
      (server only) append b to every other connection's outbound stream; Send
  processed_count++
  unlock; continue
```

Handler spec sketch (decoded level, in-process hub):

```rocq
Lemma wp_handleSyncMsg … :
  {{{ is_history γh ∗ is_conn … ∗ own_conn_state … ∗ payload_coh γh p ∗
      ⌜stream position facts⌝ }}}
    … @ "handleSyncMsg" #…
  {{{ RET #(); own_conn_state (advanced) }}}.
```

where `own_conn_state` packages §5.4's lock-protected per-connection ghost.
The apply branch composes the stream-induction lemma → sv-filter guard →
`wp_store__applyUpdate_certs` (`history_deliver_batch` inside) → re-close
`store_inv` with the grown history.

Staging note: the explicit `filterBySV` stage is how the covered-batch spec
is met while `applyUpdate` is still the no-pending core. Once the
pending-buffer port lands (p2p-layer doc), dedup is internal to `applyUpdate`
and this stage collapses into it; the loop shape and the ghost bookkeeping
above are unchanged either way.

### 6.3 Serving SyncStep1: the diff

```
func (s *store) diffSince(sv map[uint64]uint64) []updateItem   // under s.mu
```

returns, **in the server's delivery order**, every op with
`clock ≥ sv[author]`, re-attaching certificates recovered from `is_history`
(the `Hcerts` amendment, p2p-layer doc §3).

**Diff correctness.** Under `history_wf` and the server's
`history_state_coh h_srv arr`: the filtered list (i) satisfies `batch_coh`
with floor `F := sv_ids sv` — a causal-past member `x` of any kept op is
either kept earlier (delivery order is causally consistent) or filtered (then
`clock x < sv[author x]`, i.e. `x ∈ sv_ids sv`); and (ii) is **complete**: a
requester whose delivered set ⊇ `sv_ids sv` reaches, after applying,
⊇ `delivered_ids h_srv` (frontier catch-up — the protocol's functional goal,
a safety-style statement about the post-state). *Difficulty: M.*
Implementation note: per-author clock order comes from the store's run lists;
the cross-author interleaving needs a causal linearization — either a pure
topological re-sort by origins + clocks (provably a causal linearization of a
delivered set; small extra lemma, no new mutable state — **recommended**) or a
Go-side apply-log slice. Decide at the in-process hub.

### 6.4 Local edits (client send path)

mint already produces `D ⊆ delivered_ids h` (via `history_broadcast`), i.e.
floor = the client's frontier = (server-prefix ∪ own-earlier) — exactly what
the stream-induction lemma's client→server case needs. The send path appends
`SyncUpdate(new ops)` to the outbound stream and `Send`s; no new proof content
beyond framing.

## 7. Go-side sketch (all new files)

| file | contents | goose? |
|---|---|---|
| `yjs/sync.go` | `syncMsg` union (decoded), `stateVector()`, `diffSince(sv)`, `filterBySV`, `handleSyncMsg` | yes (in-process hub) |
| `yjs/transport.go` | seq framing; in-process hub: in-process mailbox; Grove transport: `gokv/grove_ffi` Send/Receive loops | yes |
| `yjs/server.go` | Listen/Accept loop, per-conn handler, relay fan-out table | yes (Grove transport; in-process analog earlier) |
| `yjs/client.go` | Connect, handshake, local-edit → `SyncUpdate` hook | yes |
| `yjs/codec.go` (extend) | v1 update codec (#31) + lib0 sync-message framing | `!goose` until #31 |

Decoded-core / byte-edge split mirrors `applyUpdate` (#39): verified handlers
consume structs; bytes only in `transport.go`/`codec.go`. `go.mod` gains
`github.com/mit-pdos/gokv` at the Grove transport.

## 8. Milestones

Named, not numbered. Ordering: **Grove spike ∥ (#42, guard toolkit) →
in-process hub (needs the guard toolkit + two-replica demo, #40, #29) → Grove
transport (needs #31)**. The guard toolkit and two-replica demo are the
p2p-layer document's milestones and precede the in-process hub.

| milestone | contents | acceptance | risk |
|---|---|---|---|
| **Grove spike** (issue #45) | feasibility spike: a hello-world Go file importing `gokv/grove_ffi` through cert-yjs's goose pipeline; New WP wrappers (`wp_Send`/`wp_Receive`/`wp_Connect`/`wp_Listen`/`wp_Accept`); PR upstream (`new/manualproof/...`) | wrappers Qed; 20-line ping-pong verified end-to-end | new-goose trusted-package wiring unexercised upstream — may surface translator gaps; timebox and report |
| **In-process hub** | protocol core, decoded, in-process hub: `sync.go` + diff correctness + the stream-induction lemma's in-process analog + per-connection stream ghosts against the heap mailbox; end-to-end theorem: server + 2 clients in one process, quiescent exchange ⇒ both client docs equal the server's (via #40) | theorem Qed, axiom-clean; `go test` convergence through the real handler code | the stream-induction lemma is where surprises live; relay-obligation bookkeeping |
| **Grove transport** | framing + `is_inbox` + escrowed connection setup (§5.3) + the stream-induction lemma proper; byte payloads via the #31 codec relation; stretch: closed-system statement via grove adequacy | end-to-end theorem restated over grove; stretch: adequacy-style closed theorem | #31 is a hard dependency for bytes; escrow bookkeeping fiddly but standard |
| **Non-goals** | recorded non-goals: liveness/retransmission & fairness; reconnection spec; multi-room; awareness protocol (ephemeral, never touches the doc) | — | — |

## 9. Open questions for the maintainer

1. **Server replica id**: OK to give the server a `ClientId` (never minting)?
   The alternative — a history-less relay storing only update logs — cannot
   answer Step1 from a doc and diverges from y-websocket. Recommendation:
   server = full replica.
2. **Delivery-order recovery for `diffSince`** (§6.3): topological re-sort
   (pure lemma) vs Go-side apply-log. Recommendation: re-sort.
3. **Trust boundary**: accept trusted peers for the verified theorems
   (byzantine handling = future receiver-side validation)?
4. **Grove-spike upstream**: contribute the New grove wrapper file to
   Perennial, or vendor it in cert-yjs first? Recommendation: try upstream —
   it is exactly the `manualproof` file they stubbed.
