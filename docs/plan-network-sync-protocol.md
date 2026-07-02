# Design: the network layer — Grove send/recv and the Yjs sync protocol

Companion to `docs/plan-issue-42-ghost-history.md` (the ghost op-history design,
issue #42). That document builds the *logical* network — per-client event
histories, certificates, `history_wf` — with no physical network in sight. This
document specifies how a **real Yjs server and clients** (none of this code
exists yet) map onto **Perennial's distributed model (Grove)** and onto the
**Yjs sync protocol** (y-protocols/sync: SyncStep1 / SyncStep2 / Update), and
what the send/receive specs and invariants are.

Perennial citations are into `mit-pdos/perennial` (local checkout); protocol
references are y-protocols/sync as implemented by y-websocket and y-octo.

---

## 0. TL;DR

- **Physical send ≠ logical broadcast.** The #42 design already separates them:
  `EvBroadcast` is the *generation* of an op (author-only, guarded by the
  exclusive `own_client_history` token, ghost update G2); a network `Send` is
  unconstrained repetition of **certified** ops — `is_op_cert` is persistent
  and transferable, so *anyone* holding (or recovering) a certificate may
  transmit the op. A relay server never mints; it forwards certificates. This
  is the direct answer to "the server sends ops it did not generate".
- **Perennial's model is Grove**: one global `gmap endpoint (gset message)`;
  `Send` atomically adds to the receiver's mailbox set, `Receive`
  nondeterministically samples it. Duplication, reordering and loss are all
  possible; there is **no FIFO**. Specs are ordinary Hoare triples over a
  per-endpoint points-to `e c↦ ms` that you place in a shared invariant
  yourself. Status in Perennial **New**: the GooseLang code model of
  `gokv/grove_ffi` exists (`new/trusted_code/github_com/mit_pdos/gokv/grove_ffi.v`),
  but the New-style WP wrapper layer is a stub
  (`new/manualproof/.../grove_ffi.v` is 8 lines) and nothing upstream consumes
  it yet — building that wrapper file is milestone **N0** (upstream candidate).
- **The one real design problem**: Yjs `Update` messages carry **no causal
  floor** on the wire, so over an arbitrary topology a receiver cannot *decide*
  whether an op's causal past is covered — but `history_deliver_batch` (G3)
  requires exactly that (`batch_ok`). Resolution: **star topology + FIFO
  per-connection streams** (which is precisely the y-websocket deployment shape
  the project targets). A sequencer hub with FIFO links yields causal delivery
  *by construction*; FIFO over Grove's unordered mailboxes is restored by a
  small verified sequence-numbering layer whose ghost content is one
  `mono_list` per direction per connection. The general-topology alternative
  (weakening the model's delivery discipline to what raw Yjs actually needs) is
  recorded as research follow-up, not attempted now (§9).
- **Protocol mapping**: SyncStep1 (state vector) is *advisory* — it has no
  safety payload; a wrong sv only costs completeness. SyncStep2/Update carry
  certified batches. The receiver's guard is: process streams in order, drop
  already-delivered ops by state-vector comparison (exact under `history_wf`,
  lemma NL1), apply the rest via `wp_store__applyUpdate_certs`.

---

## 1. Scope, status, trust model

- **Status**: no network code exists in cert-yjs. `yjs/*.go` is single-process;
  the only "network" is the ghost history of #42. This document fixes the
  target so that #42/#40 land in a shape the network layer can consume
  unchanged.
- **Safety only.** Grove models an unreliable network and Perennial proofs over
  it are safety proofs. "Two replicas that delivered the same op set have equal
  documents" (#40) and "every applied op was validly generated" are in scope;
  "every op is eventually delivered" is not (no fairness assumptions; a lost
  message stalls a stream, it never corrupts state).
- **Trusted peers.** Sender-side validity (the whole point of #42) presupposes
  that peers run the verified code: the wire invariant asserts every in-flight
  message decodes and carries certificates, which an adversarial sender could
  not honor. Byzantine tolerance would need receiver-side re-validation (the
  retired `ValidReplay` route plus runtime checks that don't exist in the
  verified subset) — out of scope, §9.
- **Topology: star.** One server (hub), N clients, one connection each. This is
  the y-websocket deployment the project targets and it is load-bearing for
  causal delivery (§4.3). Multi-server/mesh/P2P: out of scope (§9).
- **One document (room).** One `γh` history instance, one root text (matching
  #42's scope). A multi-room server runs one instance of everything per room,
  keyed by the y-websocket room name — orthogonal plumbing, noted in §9.

---

## 2. Perennial's distributed model, precisely

### 2.1 The Grove FFI (semantics — shared by old goose and New)

`src/goose_lang/ffi/grove_ffi/impl.v`:

- Global network state: `grove_net : gmap endpoint (gset message)` with
  `Record message := Message { msg_sender : endpoint; msg_data : list u8 }`
  (`impl.v:67`). One mailbox **set** per endpoint (`endpoint` = `w64`).
- `SendOp` atomically inserts into the *receiver's* set; it may also fail
  early (nothing sent) or **fail late** (message inserted, error still
  reported) — i.e. at-most-once per call, and retries duplicate.
- `RecvOp` on a connection `(c_l, c_r)` nondeterministically returns either
  `err` or some `Message c_r data ∈ ms` from the receiver's own mailbox
  `c_l c↦ ms`, **without removing it**. Hence: duplication (same message
  sampled twice), reordering (any element any time), loss (never sampled).
  Receive is already filtered to the connection's peer `c_r`, so per-connection
  message streams are natural.

### 2.2 The spec layer (old goose — to be lifted to New in N0)

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
  per-message predicate for the inserted message. This is where "you may only
  send certified ops" becomes a proof obligation.
- `Receive` needs only your **own** `c↦`, returns the set unchanged → whatever
  the per-message predicate says can be extracted **persistently** (it must be
  a persistent predicate, since the message stays in the set and can be
  received again).
- `wp_ConnectOp` allocates the client's fresh mailbox `c_l c↦ ∅`;
  `wp_AcceptOp` gives the server *no* resources about the new peer — the
  logical handles for the reply direction must travel with the client's first
  message (§5.3).
- Initialization: `ffi_global_start` hands out `e c↦ ms` for every endpoint in
  the initial net map (`grove_ffi.v:67` region), and a grove adequacy theorem
  exists (`goose_lang/ffi/grove_ffi/adequacy.v`), so a **closed-system
  theorem** (server + clients, from initial state) is expressible (N2 stretch).

### 2.3 Status in Perennial New, and the Go side

- `new/trusted_code/github_com/mit_pdos/gokv/grove_ffi.v` defines the New code
  model of the **real Go package** `github.com/mit-pdos/gokv/grove_ffi`
  (`Listen/Connect/Accept/Send/Receive` as GooseLang `val`s over the same
  `ExternalOp`s; `Connection.t := loc`), re-exporting the old semantics
  (`Existing Instances grove_op grove_model`).
- `new/manualproof/github_com/mit_pdos/gokv/grove_ffi.v` — the New WP layer —
  is a **stub** (8 lines, just `Connection.t`). No file in perennial@HEAD
  imports the trusted code yet, so the goose-translation wiring for a Go file
  importing `gokv/grove_ffi` is **unexercised**. Milestone N0 validates the
  pipeline end-to-end and writes the wrapper WPs (`wp_Send`/`wp_Receive`/… in
  New style over `own_slice` bytes, delegating to the `wp_*Op` lifting lemmas
  above). Upstream candidate; small and mechanical (~150 lines by analogy with
  other manualproof files).
- Deployment story: `gokv/grove_ffi` is a real Go package (TCP underneath), so
  the verified binaries run unmodified — same trusted-translator status as the
  rest of goose. cert-yjs's proofs are already FFI-parametric
  (`Context {hG: heapGS Σ, !ffi_semantics _ _}`), so existing results transfer
  to the grove instantiation without change; only top-level closed theorems fix
  the FFI.

---

## 3. Broadcast ≠ Send: why the #42 design is already relay-shaped

The #42 ghost step G2 (`history_broadcast`) is the only authorship-gated
operation: it consumes the exclusive `own_client_history γh c h`, appends
`EvBroadcast op; EvDeliver op` to **c's own** history, and mints the persistent
certificate `is_op_cert γh op D`. Nothing in it mentions the network.

A physical `Send`, by contrast, is gated only on the **wire invariant**'s
per-message predicate (§5), which demands certificates for the ops carried —
not authorship. Since `is_op_cert` is persistent (hence duplicable and
logically transferable), any party that ever *received* an op can re-send it.
Concretely, the Yjs server:

- holds `own_client_history γh c_srv h_srv` for its **own replica id** `c_srv`
  (it delivers ops into its local doc to answer SyncStep1, so it is a replica
  in the ghost network) but never calls G2 — its `history_wf` obligations for
  broadcasts are vacuous, and no op ever carries `c_srv` as author;
- accumulates certificates for everything it delivers, and re-attaches them
  when forwarding.

**Amendment to #42 (§5.2 of that doc), for certificate recovery.** So that a
relay need not thread every certificate through its own state, add to
`history_inv` the persisted-fragment big-op:

```rocq
"Hcerts" ∷ [∗ map] id ↦ p ∈ ops, id ↪[γh.(hn_ops)]□ p
```

G2 already mints the `↪□` fragment, so re-establishing this conjunct is free;
opening `is_history` then lets *any* party copy the certificate of *any*
registered op id (persistent ⇒ duplicable out of the invariant). The server's
diff construction (§6.3) uses exactly this.

---

## 4. The Yjs sync protocol, mapped

### 4.1 Message grammar and what each message means logically

y-protocols/sync, over one bidirectional connection:

| wire message | payload | logical content |
|---|---|---|
| `SyncStep1(sv)` | state vector (per-client clock frontier) | **advisory**: "I claim to have delivered exactly `sv`". No safety payload — a wrong `sv` can only cause a wrong *diff* (superset ⇒ deduped on arrival; subset ⇒ missing ops = completeness loss, never corruption). Wire predicate: pure well-formedness only. |
| `SyncStep2(update)` | encoded batch = the diff against the peer's `sv` | certified op batch, causally self-contained **relative to the requester's own sv** (§4.2) |
| `Update(update)` | encoded batch (incremental) | certified op batch, self-contained relative to the sender's stream history (§4.3) |

Handshake (y-websocket): on connect each side sends `SyncStep1`; each answers
with `SyncStep2`; thereafter live `Update`s flow. The server additionally
**relays** every applied `Update` to all other connections, in apply order.

### 4.2 State vectors ↔ the ghost history

A state vector is `sv : gmap ClientId nat` — per author, the clock frontier
(`sv !! c = Some k` ⇔ "I have c's ops with clock < k"). Its meaning against the
#42 history:

```rocq
Definition sv_ids (sv : gmap ClientId nat) : gset YjsId := …  (* {(c,j) | j < sv!!c} *)
Definition state_vector (h : list Ev) : gmap ClientId nat := …  (* per-author max delivered clock + 1 *)
```

**NL1 (sv characterizes the delivered set — the exact-dedup lemma).** Under
`history_wf N` with `N !! c = Some h`:
`delivered_ids h = sv_ids (state_vector h)`.
*Why it holds*: (⊆) by definition of max. (⊇) needs per-author **prefix
closedness in clock order** — an author's ops are totally hb-ordered by its
local broadcast order (`hb_bb`), broadcast in strictly increasing clocks
(`hwf_unique_id` + immediate self-delivery), and causal delivery forces every
replica to deliver them in that order — plus **clock density** (an author's
clocks are consecutive), which holds for cert-yjs authors because G2 mints from
the store's counter, one unit per (single-char) op, single governed text.
Density is a property of the *minting discipline*, so record it as a
`history_wf` field (e.g. `hwf_dense_clocks : ∀ c, delivered clocks of author c
in any history form a downward-closed set of nats`) established by G2 and
consumed here. *Difficulty: M.* (Under trusted peers this is sound; a byzantine
author skipping clocks would make sv-dedup over-approximate and drop a genuine
op — a completeness, not safety, failure. §9.)

The Go side needs `stateVector()` — computable from the store's per-client run
lists (`store.items`, whose sorted-run invariant `is_item_map` says the last
element of each run carries the max clock). **Dependency**: `is_item_map` must
be back in `store_inv` (issue #29's AddNode/items-map re-threading) before
`stateVector()` is verifiable; alternatively derive the frontier from
`ts_arr`'s per-client maxima. Flag: #29 re-land is on the critical path for N1.

### 4.3 The causal-delivery gap, and why star + FIFO closes it

`history_deliver_batch` (G3) needs `batch_ok`: each incoming op's certified
causal past `D_i` is covered by the receiver's `delivered_ids ∪` earlier batch
ops. But a Yjs `Update` **does not carry `D_i`** or any floor — certificates
and `D` are ghost data. Over an arbitrary topology the receiver cannot decide
coverage (checking only *origins* is weaker than the model's happens-before,
which includes same-author order and deliver-before-broadcast edges; real Yjs
tolerates that because its integration commutes more broadly, but *our model's*
`causal_delivery` axiom does not — reproving iris-yjs under the weaker
discipline is the research alternative (B) of §9).

**Resolution (A): the star topology provides causal delivery by
construction.** With one hub and FIFO per-connection streams:

- *Client → server*: when the server processes client `u`'s op `y` (in stream
  order), `y`'s causal past is `P ∪ O` where `P` = the prefix of the
  **server's own outbound stream** that `u` had processed before minting `y`
  (the server delivered all of `P` before it even sent it), and `O` = `u`'s own
  earlier ops (arrived FIFO-before `y` on the same stream, already processed).
  Covered. ✓
- *Server → client*: the server's outbound stream to client `v` is
  `SyncStep2(diff vs sv_v)` followed by **every batch the server subsequently
  applies, in apply order** (the relay discipline). When `v` processes entry
  `n`, its delivered set contains the diff floor (`sv_v` was `v`'s own frontier
  — monotone since) plus all earlier entries; the server only ever forwards
  what it has itself delivered under this same argument, inductively. Covered. ✓
- The symmetric handshake is the base case: `v`'s `SyncStep2` to the server is
  self-contained relative to the server-prefix `v` had plus `v`'s own ops
  inside the same batch.

This is the classic "sequencer gives causal (indeed FIFO-total per hub) order
for free". It is exactly how y-websocket deployments behave (TCP = FIFO), and
it is the *reason* the protocol can omit floors from the wire.

**FIFO over Grove** is not primitive (mailboxes are sets) — restore it with a
small verified framing layer: every payload goes out as `(seq n, payload)`;
the receiver processes `n` only after `n−1` (buffering ahead-of-order arrivals,
ignoring duplicates). Ghost content per direction per connection: one
`mono_list` of payloads (§5.2). Loss ⇒ the stream stalls; safety unaffected.
No retransmission needed for safety (it would matter only for liveness).

---

## 5. Ghost architecture of the wire

Three new ghost pieces beside #42's `γh` (gnames bundled per connection in a
record `conn_names := { cn_c2s : gname; cn_s2c : gname }`):

### 5.1 Per-direction stream ghosts

For each connection, two `mono_list (leibnizO syncPayload)` instances
(Perennial wraps mono_list: `new/ghost/mono_list.v` — `mono_list_auth_own`,
`mono_list_lb_own`, `mono_list_idx_own`; the idx form is persistent, which is
exactly what a wire message needs):

- the **sender** holds `mono_list_auth_own γdir 1 sent` inside its lock
  invariant and appends (`mono_list_auth_own_update_app`) before each `Send`;
- each wire message `(n, payload)` is pinned by the persistent witness
  `mono_list_idx_own γdir n payload` — so two receives of "message n" must
  agree on the payload, and in-order processing is exactly-once by counter;
- the **receiver** holds a processed-counter `p` and (persistently) the lb of
  the prefix it has processed.

### 5.2 The per-message wire predicate

```rocq
(* Decoded-level payloads; bytes enter only at N2 via the codec relation. *)
Inductive syncPayload :=
  | SyncStep1 (sv : gmap ClientId nat)
  | SyncStep2 (inputs : list (IntegrateInput (A := A)))
  | SyncUpdate (inputs : list (IntegrateInput (A := A))).

(* What every batch-carrying payload must bring: certificates + a ghost floor. *)
Definition batch_coh (γh : history_names) (inputs : list _) : iProp Σ :=
  ∃ (Ds : list (gset YjsId)) (F : gset YjsId),
    ([∗ list] input;D ∈ inputs;Ds, is_op_cert γh (OpInsert input) D) ∗
    "%Hself" ∷ ⌜∀ i input D, inputs !! i = Some input → Ds !! i = Some D →
                  D ⊆ F ∪ list_to_set (in_id <$> take i inputs)⌝.
    (* F is existential GHOST data — never on the wire.  Which F a stream entry
       may use is constrained by stream_coh below, not here. *)

Definition payload_coh γh (p : syncPayload) : iProp Σ :=
  match p with
  | SyncStep1 sv => ⌜sv_wf sv⌝
  | SyncStep2 inputs | SyncUpdate inputs => batch_coh γh inputs
  end.

(* One mailbox invariant per endpoint.  msg_coh is persistent (certs + idx
   witnesses + pure), as Grove's set semantics requires (§2.2). *)
Definition msg_coh γh (dir : gname) (m : message) : iProp Σ :=
  ∃ n payload, ⌜frame_dec m.(msg_data) = Some (n, payload)⌝ ∗
               mono_list_idx_own dir n payload ∗ payload_coh γh payload.

Definition is_inbox γh (e : endpoint) (Φfirst : message → iProp Σ) : iProp Σ :=
  inv wireN (∃ ms, e c↦ ms ∗ [∗ set] m ∈ ms, (msg_coh γh (dir_of m) m ∨ Φfirst m)).
```

(`dir_of m`: the server's single inbox holds messages from many peers; the
per-sender direction gname is what `Φfirst` — the connection-establishment
predicate of §5.3 — introduces. In the concrete definition the invariant is
stated per known peer set with a fresh-peer disjunct; the sketch above elides
that bookkeeping.)

### 5.3 Connection establishment (handle escrow)

`wp_AcceptOp` yields no resources about the peer (§2.2), so logical handles
travel with the first message:

- The client, after `Connect` (which yields its fresh `c_l c↦ ∅`), allocates
  its own inbox invariant `is_inbox γh c_l …` and its `conn_names`, then sends
  its first frame (`SyncStep1`).
- The **server-inbox** predicate `Φfirst` for a first-contact message from
  endpoint `c` carries, persistently: `is_inbox γh c …` (so the server may
  later `Send` to `c`) and the `conn_names` idx-witness structure for both
  directions. The server's receive loop extracts these (persistent copies) and
  records them in its per-connection table.
- The **server's own** inbox invariant + `is_history γh` are allocated at
  system init (from `ffi_global_start`'s `e c↦ ∅` for the well-known server
  endpoint) and are part of the static configuration every client is verified
  against — the same role OpLib's "socket protocol for the server address"
  plays.

### 5.4 Stream coherence (where the star argument lives)

The lock invariants tie streams to histories:

- **Client `u`'s lock** (extends #42's `store_inv`): auth of its outbound
  stream `sent_u`; processed-counter `p_u` into the server's outbound stream;
  and the pure tie: `u`'s delivered history `h_u` = (initial Step2 floor) ∪
  (processed prefix of server-stream) ∪ (own minted ops), in stream order.
- **Server's lock**: per connected client — auth of the server-outbound stream
  (= `Step2(diff)` followed by *every batch the server applied since*, in apply
  order: the **relay obligation**, an equality between the stream tail and a
  suffix of the server's delivered order); processed-counter into that client's
  inbound stream; plus the server's own `own_client_history γh c_srv h_srv`.

**NL3 (stream induction ⇒ `batch_ok`).** With the §5.4 ties, when a receiver
processes stream entry `n` (in order), the entry's ghost floor `F` satisfies
`F ⊆ delivered_ids (its current history)` — by the two bullets of §4.3, made
precise per direction. Combined with sv-dedup (NL1/NL4) this discharges
`history_deliver_batch`'s `batch_ok` precondition with **no wire-level floor
and no undecidable receiver check**. *Difficulty: H — this is the network
layer's central lemma; it is where the star topology and the relay obligation
are consumed.*

---

## 6. Specs

### 6.1 Transport wrappers (N0/N2)

```rocq
(* New-style wrappers over wp_SendOp / wp_RecvOp (§2.2), bytes as own_slice. *)
Lemma wp_Send γh (c : Connection.t) (s : slice.t) (data : list w8) dir n payload :
  frame_dec data = Some (n, payload) →
  {{{ is_inbox γh (remote c) Φ ∗ s ↦* data ∗
      mono_list_idx_own dir n payload ∗ payload_coh γh payload }}}
    grove_ffi @ "Send" #c #s
  {{{ (err : bool), RET #err; s ↦* data }}}.
    (* err covers both early and late failure; on late failure the message IS
       in flight — the spec promises nothing either way, callers rely only on
       the invariant. *)

Lemma wp_Receive γh (c : Connection.t) :
  {{{ is_inbox γh (local c) Φ }}}
    grove_ffi @ "Receive" #c
  {{{ (err : bool) (s : slice.t) (data : list w8), RET (#err, #s);
      s ↦* data ∗ (⌜err⌝ ∨ ∃ n payload, ⌜frame_dec data = Some (n, payload)⌝ ∗
                    mono_list_idx_own (dir_of …) n payload ∗ payload_coh γh payload) }}}.
```

At N1 (in-process transport) the same two specs are stated against a
heap-mailbox module (a mutex-guarded queue of `syncMsg` structs) instead of
grove — deliberately the *same shape*, so N2 is a transport swap.

### 6.2 The receive/processing loop (per connection)

```
loop:
  (err, data) := Receive(conn); if err retry
  (n, payload) := decode frame                      // exactly-once via counter:
  if n ≠ processed_count: buffer/skip; continue     //   duplicates n < p dropped,
  lock store                                        //   gaps n > p buffered
  match payload:
    SyncStep1(sv)   => diff := diffSince(sv); reply SyncStep2(diff)          // §6.3
    SyncStep2(b) | SyncUpdate(b) =>
      fresh := filter b by local state_vector       // NL1: exact dedup
      applyUpdate(parent, fresh) via wp_store__applyUpdate_certs             // #42 §6.5
        -- batch_ok from NL3 (stream induction) + NL4 (filter soundness)
      (server only) append b to every other connection's outbound stream; Send
  processed_count++
  unlock; continue
```

Spec sketch for the core handler (decoded level, N1):

```rocq
Lemma wp_handleSyncMsg (srv? : bool) … :
  {{{ is_history γh ∗ is_conn … ∗ own_conn_state … ∗ payload_coh γh p ∗
      ⌜stream position facts⌝ }}}
    … @ "handleSyncMsg" #…
  {{{ RET #(); own_conn_state (advanced) }}}.
```

where `own_conn_state` packages the lock-protected per-connection ghost of
§5.4. The apply branch is a thin composition: NL4 ⇒ `batch_ok` for the filtered
suffix ⇒ `wp_store__applyUpdate_certs` (which already advances the history via
G3) ⇒ re-close `store_inv` with the grown `h`.

**NL4 (guard soundness).** If the receiver drops exactly the ops with
`clock < sv[author]` (its current sv) from a batch satisfying `batch_coh` with
floor covered (NL3), the remaining subsequence satisfies `batch_ok h · ·`:
dropped ops are delivered (NL1), so any later op's `D` that referenced them is
still covered by `delivered_ids h`; retained ops are fresh by NL1(⇒).
*Difficulty: M.*

### 6.3 Serving SyncStep1: the diff

```
func (s *store) diffSince(sv map[uint64]uint64) []updateItem   // under s.mu
```

reads the per-client run lists (`store.items`) and returns, **in the server's
delivery order**, every op with `clock ≥ sv[author]`, re-attaching certificates
recovered from `is_history` (§3 amendment).

**NL2 (diff correctness).** Under `history_wf` and the server's
`history_state_coh h_srv arr`: the filtered list (i) satisfies `batch_coh` with
floor `F := sv_ids sv` — an op's causal-past member `x` is either kept (appears
earlier: delivery order is causally consistent) or filtered (then
`clock x < sv[author x]`, i.e. `x ∈ sv_ids sv`); and (ii) is **complete**: a
requester whose delivered set contains `sv_ids sv` has, after applying the
diff, a delivered set ⊇ `delivered_ids h_srv` (frontier catch-up — the
protocol's functional goal, provable as a safety statement about the
post-state). *Difficulty: M, given #42's L-series.*
Implementation note: delivery order must be recoverable from the store — the
run lists give per-author clock order; the cross-author interleaving needs the
history `h_srv` (ghost). Either state NL2 against an order-oblivious
topological re-sort by origins + clocks (provably a causal linearization of the
delivered set — small extra lemma), or keep a Go-side apply-log slice (extra
code, no ghost). Decide at N1; the re-sort avoids new mutable state.

### 6.4 Local edits (client send path)

`Text.Insert` already mints certificates with `D ⊆ delivered_ids h` at mint
time (G2's postcondition) — i.e. floor = the client's own frontier, which is
(server-prefix ∪ own-earlier): exactly the self-containment NL3 needs. The send
path appends `SyncUpdate(new ops)` to the outbound stream and `Send`s; no new
proof content beyond framing.

---

## 7. New pure lemmas (network series)

| # | statement (sketch) | difficulty | home |
|---|---|---|---|
| NL1 | `history_wf N → N!!c = Some h → delivered_ids h = sv_ids (state_vector h)`; needs the new `hwf_dense_clocks` field (established by G2) | M | `yjs_network_model.v` |
| NL2 | diff vs `sv` is `batch_coh`-self-contained with floor `sv_ids sv` and frontier-complete (§6.3) | M | same |
| NL3 | stream induction: §5.4 ties ⇒ every in-order-processed entry's floor is covered by the receiver's current delivered set (star-topology causal delivery) | H | new `yjs_wire.v` (Iris; needs mono_list, not the store) |
| NL4 | sv-filter guard turns a floor-covered `batch_coh` batch into a `batch_ok` batch (§6.2) | M | `yjs_network_model.v` |

Plus the #42 amendment (certs big-op in `history_inv`, §3) and the
`hwf_dense_clocks` field (touches G2's proof: clocks minted consecutively —
already true, one more conjunct to carry).

---

## 8. Go-side sketch (all new files; nothing exists yet)

| file | contents | goose? |
|---|---|---|
| `yjs/sync.go` | `syncMsg` tagged union (decoded), `stateVector()`, `diffSince(sv)`, `filterBySV`, `handleSyncMsg` | yes (N1) |
| `yjs/transport.go` | seq framing; N1: in-process mailbox (mutex + slice queue); N2: `gokv/grove_ffi` Send/Receive loops | yes |
| `yjs/server.go` | Listen/Accept loop, per-conn handler goroutine, relay fan-out table | yes (N2; N1 has an in-process analog) |
| `yjs/client.go` | Connect, handshake, local-edit → `SyncUpdate` hook | yes |
| `yjs/codec.go` (extend) | v1 update codec (#31) + lib0 sync-message framing (msg type varint + payload) | `!goose` until #31, then translated |

The decoded-core / byte-edge split mirrors `applyUpdate` (#39): every verified
handler consumes structs; bytes appear only in `transport.go`/`codec.go`.
`go.mod` gains `github.com/mit-pdos/gokv` (grove_ffi package) at N2.

---

## 9. Milestones

Ordering: **N0 ∥ (#42 M1–M4) → N1 (needs #42, #40, #29) → N2 (needs #31)**.

| M | contents | acceptance | risk |
|---|---|---|---|
| **N0** | Feasibility spike: a hello-world Go file importing `gokv/grove_ffi` through cert-yjs's goose pipeline; write the New WP wrappers (`wp_Send`/`wp_Receive`/`wp_Connect`/`wp_Listen`/`wp_Accept`) against the old lifting lemmas; PR upstream to Perennial (`new/manualproof/...`) | wrappers Qed; a 20-line ping-pong program verified end-to-end | new-goose trusted-package wiring unexercised upstream — may surface translator gaps; timebox and report |
| **N1** | Decoded-level protocol core, in-process transport: `sync.go` + NL1/NL2/NL4 + `hwf_dense_clocks` + certs-big-op amendment; per-connection stream ghosts against the heap mailbox; end-to-end theorem: server + 2 clients in one process, after a quiescent exchange both client docs equal the server's (`is_Text`-level equality via #40) | theorem Qed, axiom-clean; `go test` convergence table test through the real handler code | depends on #40 (convergence consumption) and #29 re-land (`is_item_map` for `stateVector`); NL3's in-process analog is where surprises live |
| **N2** | Grove transport: framing layer + `is_inbox` invariants + escrowed connection setup (§5.3) + NL3 proper; byte payloads via the #31 codec relation; stretch: closed-system statement via grove adequacy | same end-to-end theorem restated over grove; stretch: adequacy-style closed theorem | #31 (codec) is a hard dependency for bytes; escrow bookkeeping is fiddly but standard |
| **N3** | non-goals recorded: liveness/retransmission & fairness; reconnection and session resumption (fresh Step1/Step2 re-handshake is *safe* by design — dedup — but its spec is future work); multi-room; awareness protocol (ephemeral, never touches the doc — out) | — | — |

**Research follow-up (B), explicitly not now**: general topologies (mesh,
offline peer-to-peer sync) require weakening the model's `causal_delivery` to
what Yjs integration actually needs (origins present + per-author clock
contiguity) and re-proving iris-yjs convergence under that discipline — a
substantial change to lean-yjs/iris-yjs (`effect_list_reorder`'s hypotheses),
tracked separately if ever needed. The star deployment does not need it.

## 10. Open questions for the maintainer

1. **Server replica id**: OK to give the server a `ClientId` (never minting)?
   The alternative — a history-less relay that only stores update logs and
   cannot answer Step1 from a doc — diverges from y-websocket (which keeps a
   doc) and from how `diffSince` wants to work. Recommendation: server = full
   replica, as specified.
2. **Delivery-order recovery for `diffSince`** (§6.3): topological re-sort
   (pure lemma, no new state) vs a Go-side apply-log. Recommendation: re-sort.
3. **Trust boundary**: accept the trusted-peers assumption for the verified
   theorems (byzantine handling = future receiver-side validation)?
4. **N0 upstream**: contribute the New grove wrapper file to Perennial (public
   PR) or keep it vendored in cert-yjs first? Recommendation: try upstream —
   it is exactly the `manualproof` file they stubbed.
