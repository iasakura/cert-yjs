# Spec design: the verified Yjs WebSocket server (issue #107, W3b)

W1 (the ws FFI) and W2 (the WebSocket realization + echo demo) are merged.
W3a (rooms, connection table, verbatim relay: `wsrelay/` + `ws_relay.v`) is
merged. The environment side (#114-#116) established that `ws_env_preserves`
is dischargeable for peers that carry a real Yjs protocol, up to a peer that
takes an operation in and then types without end (`ws_env_smoke.v`).

This document fixes the specification for the next step: the server that,
instead of relaying bytes verbatim, APPLIES each received update to a real
document and relays it, i.e. y-websocket's message loop for the
Step2/Update case. The handshake (Step1 answered by a Step2 diff) is W3c,
out of scope here; the design below is forward-compatible with it.

## 0. TL;DR

Four verified statements about the server, all in the repo's established
certificate style (persistent receipts, no full-state pinning):

- **S1 (safety / no-loss)**: for every update packet the server takes in,
  every input in it is `is_accepted` by the server's store: the server
  genuinely integrated the batch, and each input id is forever
  delivered-or-buffered in the server's document, never dropped. Per packet
  the server's ghost history visibly grows by the applied portion
  (`is_history_lb`). This is "the server extends its history according to
  the protocol" made enforceable.
- **S2 (input-log faithfulness)**: a per-room ghost log `L` (mono_list)
  records the sequence of Yjs protocol packets the room has processed, and
  the invariant ties `L` per connection to the wire: the entries from
  connection `u` are exactly the first `p_u` messages of `u`'s channel, in
  order, exactly once, no gaps. `L` IS the received-packet sequence as ghost
  state.
- **S3 (reply soundness)**: per connection `v`, the stream of messages the
  server has sent to `v` is an order-preserving subsequence of
  `relay_view v (drop j_v L)`: every reply is a relay of a logged packet
  from another connection, in log order, at most once, and nothing else is
  ever sent. (`j_v` = the log position at which `v` joined; subsequence, not
  equality, because `Send` may fail and y-websocket drops on error.)
- **S4 (wire certificate preservation)**: everything the server puts on the
  wire satisfies the deployment protocol `yjs_prot` (decodes to per-char
  certified inputs), so a client receiving a relay gets exactly the
  guarantee the server got. This is what the environment peers of
  `ws_env_smoke.v` consume off the wire.

No changes to the yjs / store / doc proof layers are required: the server
proof composes the existing `wp_Doc__ApplySyncUpdate` with new room-level
ghost state. Two small optional amendments are listed in section 7.

## 1. Scope

One room, one document, one `γh`; the server is a full replica with its own
`ClientId` that only delivers, never mints (plan-network-yjs-protocol.md
section 9, question 1, resolved as "server = full replica"). Peers are the
environment: nothing is assumed about who connects beyond
`ws_env_preserves`, the one standing assumption of the ws layer
(peer conformance is a hypothesis, issue #107's decision list). Byzantine
input, liveness, retransmission, and relay completeness (a gone peer misses
messages) are non-goals; the handshake and multi-room are follow-ons
(sections 8 and 9).

Since #40 (total applyUpdate) there is no covered-batch or floor
obligation anywhere: the old star + FIFO argument of
plan-network-yjs-protocol.md section 4 is not needed for safety, and the
FIFO half of it is native to the ws FFI (receive cursors). What remains of
that document's design is the protocol mapping and the relay discipline,
which reappear here as S2/S3.

## 2. The deployment protocol `yjs_prot`

`ws_prot` is the per-message predicate every wire message satisfies
(sending owes it, receiving is owed it). The deployment instantiates it
with what `wp_Doc__ApplySyncUpdate` needs of a batch, and nothing more:

```rocq
(* the abstract codec: a parameter of the whole deployment, as in
   ws_env_smoke.v. The Go-level codec value is related to it by a Hoare
   hypothesis (section 4); the env instances construct messages with a
   matching encode. *)
Context (decode : list u8 -> option (list Input)).

Definition update_wf (inputs : list Input) : Prop :=
  (forall x, x ∈ inputs ->
     (Z.of_nat (clock (in_id x.2)) + Z.of_nat (length (in_content x.2)) < 2^64)%Z) /\
  (forall x, x ∈ inputs -> pending_item_rooted_pure x).

Definition yjs_prot (γh : history_names) (d : list u8) : iProp Σ :=
  ∃ inputs, ⌜decode d = Some inputs⌝ ∗ ⌜update_wf inputs⌝ ∗
            is_pending_certified γh (expand_inputs inputs).
```

This is `ws_env_smoke.v`'s `smoke_prot` plus the two pure honesty facts the
apply path needs (`update_wf`): the 2^64 no-wrap seam and rootedness of
head structs. Both are facts about an honest peer's output, so they belong
in the protocol, not in the server's hypotheses. Notes:

- `pending_item_rooted` (store/heap.v) is already pure; it takes a `γs`
  only for signature stability. Hoist a `γs`-free alias
  (`pending_item_rooted_pure`) so the protocol does not name a store.
- Adopting `yjs_prot` costs the smoke instances their arbitrary `t : TId`:
  their inserts have no origins, so their type must be a `RootId nm`.
  A parameter change in `ws_env_smoke.v`, nothing structural.
- Every message on the wire satisfies it, so a received message always
  decodes; the Go decode-failure branch is provably dead under the model
  (Byzantine bytes are outside it, by the standing assumption).

## 3. Go changes (`wsrelay/`, `yjs/`)

```go
// yjs (new, goose-included file): the codec as an opaque exported type.
// Constructible only inside package yjs ([]updateItem is unexported);
// codec.go (!goose) provides the real one, tests and demos use it.
type Codec = func(data []byte) (ok bool, structs []updateItem)

// Applies one encoded update under the store's write lock.
func (d *Doc) ApplyEncodedUpdate(decode Codec, data []byte) {
    ok, structs := decode(data)
    if !ok {
        return // dead under the model: wire messages satisfy yjs_prot
    }
    d.ApplySyncUpdate(structs)
}
```

```go
// wsrelay: the room gains the document and the codec.
type Room struct {
    mu     sync.Mutex
    conns  []wsnet.Connection
    doc    *yjs.Doc
    decode yjs.Codec
}

func NewRoom(doc *yjs.Doc, decode yjs.Codec) *Room

// process handles ONE received message: apply, then fan out, under ONE
// room.mu critical section (section 5 explains why the section spans
// both). store.mu nests inside room.mu (ApplyEncodedUpdate takes it);
// nothing takes them in the other order.
func (r *Room) process(self wsnet.Connection, data []byte) {
    r.mu.Lock()
    r.doc.ApplyEncodedUpdate(r.decode, data)
    for _, c := range r.conns {
        if c != self {
            wsnet.Send(c, data) // errors ignored, as in y-websocket
        }
    }
    r.mu.Unlock()
}

func (r *Room) Serve(c wsnet.Connection) {
    for {
        err, data := wsnet.Receive(c)
        if err {
            return
        }
        r.process(c, data)
    }
}
```

- The relay stays verbatim (the received bytes), as in y-websocket, so S4
  is discharged by the persistent `ws_prot` the receive handed over,
  exactly as in today's `wp_Room__Serve`.
- `Broadcast` as a public self-locking method disappears into `process`
  (or stays as a `broadcastLocked` helper); `Join` is unchanged.
- Divergence note to carry as a code comment: y-websocket's
  `updateHandler` sends to ALL connections including the origin (the
  origin dedups); we skip `self`, as W3a already does. Safe either way,
  since delivery is idempotent per certificate.
- Risk to spike early: goose translation of a func-typed struct field and
  a call through it (`r.decode(data)`). Fallback if it fails: pass the
  codec as an explicit argument to `Serve`/`process` instead of a field
  (parameters are plain values; the call form is the same).

## 4. The codec seam

The server is verified against the abstract `decode`; the Go codec value
enters as a specification hypothesis, not a trusted axiom in the proof
repo:

```rocq
Definition codec_spec (f : func.t) : iProp Σ :=
  □ ∀ (s : slice.t) dq (data : list u8),
      {{{ s ↦*{dq} data }}} #f #s
      {{{ (ok : bool) (sl : slice.t) inputs, RET (#ok, #sl);
          s ↦*{dq} data ∗
          if ok then ⌜decode data = Some inputs⌝ ∗ own_update_structs sl (DfracOwn 1) inputs
          else ⌜decode data = None⌝ }}}.
```

`is_Room` carries `codec_spec` for the stored codec value. The top-level
theorem is then "for any codec meeting `codec_spec` against `decode`":
the real #31 codec is claimed (not proved) to meet it, which is the same
trust boundary the repo already draws at codec.go, now stated instead of
implicit. When #31 becomes goose-translatable, discharging `codec_spec`
for it closes the seam with no change above.

## 5. Ghost architecture

### 5.1 The room log

```rocq
Record relay_entry := RelayEntry {
  re_src  : chan_id;   (* the source connection's RECEIVE channel *)
  re_idx  : nat;       (* its index in that channel's stream *)
  re_data : list u8;
}.

(* auth in room_inv, appended by process; lbs are persistent *)
own_room_log γlog L      is_room_log_lb γlog L0

(* what the server may send to v: data of entries from other connections *)
Definition relay_view (rc_v : chan_id) (L : list relay_entry) : list (list u8) :=
  re_data <$> filter (λ e, e.(re_src) ≠ rc_v) L.
```

Plus a per-source position ghost map `γpos : ghost_map chan_id nat`: the
auth lives in `room_inv` and equals the per-source entry counts of `L`;
each connection's `Serve` goroutine owns its fragment `rc ↪[γpos] n`.
The fragment is the exclusive "I am the one logging for this source"
token, and it is what makes S2's density provable: `Serve` holds both the
FFI receive cursor and the position fragment, so cursor position and log
position advance in lockstep.

### 5.2 The room invariant

`room_inv` (the body of `room.mu`) becomes:

```rocq
Definition own_conn_send (γlog : gname) (L : list relay_entry) (c : loc) : iProp Σ :=
  ∃ (sc rc : chan_id) (sent : list (list u8)) (j : nat),
    is_Connection c sc rc ∗
    own_send_cursor sc (length sent) ∗
    ([∗ list] i ↦ d ∈ sent, is_chan_msg sc i d) ∗      (* sent IS the wire *)
    ⌜sent `sublist_of` relay_view rc (drop j L)⌝.       (* S3 *)

Definition entry_receipts (γs : store_names) (γh : history_names)
    (e : relay_entry) : iProp Σ :=
  ∃ inputs, ⌜decode e.(re_data) = Some inputs⌝ ∗
    ([∗ list] x ∈ inputs, is_accepted γs (in_id x.2)) ∗              (* S1 *)
    (∃ c h applied, is_history_lb γh c (h ++ (deliver_ev <$> expand_inputs applied))).

Definition room_inv (r : loc) (γ : room_names) : iProp Σ :=
  ∃ sl cs (L : list relay_entry),
    "Hconnsf"  ∷ (r .[Room, "conns"]) ↦ sl ∗ "Hconns" ∷ sl ↦* cs ∗ "Hcap" ∷ … ∗
    "Hlog"     ∷ own_room_log γ.(rn_log) L ∗
    "Hpos"     ∷ ghost_map_auth γ.(rn_pos) 1 (log_positions L) ∗
    "#Hlogmsgs" ∷ ([∗ list] e ∈ L, is_chan_msg e.(re_src) e.(re_idx) e.(re_data)) ∗
    "%Hlogwf"  ∷ ⌜log_wf L⌝ ∗            (* per-source indices are 0,1,2,… in order *)
    "#Hrcpts"  ∷ ([∗ list] e ∈ L, entry_receipts γs γh e) ∗
    "Hsends"   ∷ ([∗ list] c ∈ cs, own_conn_send γ.(rn_log) L c).
```

`is_Room` additionally carries (persistently) the document handle
`is_Doc dv s_loc γs γh`, `is_history γh`, and `codec_spec` for the stored
codec.

The pieces already fit:

- `Hlogmsgs + Hlogwf + γpos` give S2: the log's restriction to source `u`
  is message `0..p_u` of `u`'s channel verbatim (`is_chan_msg` agreement
  pins each entry to the wire).
- `own_conn_send` is W3a's predicate strengthened from "a cursor at some
  point" to "a cursor at the end of THIS sent list, which embeds into the
  relay view": S3. The sublist claim is monotone under log append and
  under `drop j` (a sublist of a prefix's view is a sublist of the
  extended view), which is what lets `Join` set `j := length L` and lets
  `process` extend `L` first and then send.
- `entry_receipts` is S1. `is_accepted` receipts are the enforceable form
  (accepted-set soundness, `own_store_accepted_sound`): a discarding
  server could not mint them. The `is_history_lb` conjunct shows the
  applied portion entered the delivered history in processing order; `c`
  stays existential unless amendment 7b is taken.

### 5.3 Why one critical section spans apply and fan-out

`process` holds `room.mu` across both the apply and the sends. Two
processings of one room therefore serialize completely, which is exactly
y-websocket's semantics (a Node process runs the doc's message handlers
on one thread), so nothing real is lost. What it buys:

- S3 as stated. With concurrent sections, two goroutines could apply in
  one order and fan out in the other, and `sent_v` would only be a
  sub-MULTISET of the relay view with per-entry at-most-once tokens, a
  strictly weaker and uglier statement.
- The log order is simultaneously the apply order and the relay order,
  so one `L` serves S1, S2 and S3.

`store.mu` nests inside `room.mu` and nothing takes them in the other
order, so the nesting is deadlock-free.

## 6. Specs

```rocq
Lemma wp_NewRoom (dv s_loc : loc) γs γh (f : func.t) :
  {{{ is_Doc dv s_loc γs γh ∗ is_history γh ∗ codec_spec f }}}
    @! wsrelay.NewRoom #dv #f
  {{{ (r : loc) γ, RET #r; is_Room r γ }}}.

(* Join hands over the send side, recording the join point: relays reach
   this connection from here on. *)
Lemma wp_Room__Join r γ c sc rc :
  {{{ is_Room r γ ∗ is_Connection c sc rc ∗ own_send_cursor sc 0 }}}
    r @! "Join" #c
  {{{ RET #(); True }}}.

(* One message: apply + fan out. The position fragment is the caller's
   exclusive right to log for this source, and comes back advanced. *)
Lemma wp_Room__process r γ c sc rc (n : nat) s dq (data : list u8) :
  {{{ is_Room r γ ∗ is_Connection c sc rc ∗ s ↦*{dq} data ∗
      is_chan_msg rc n data ∗ ws_prot data ∗ rc ↪[γ.(rn_pos)] n }}}
    r @! "process" #c #s
  {{{ RET #(); s ↦*{dq} data ∗ rc ↪[γ.(rn_pos)] (S n) ∗
      (∃ L0, is_room_log_lb γ.(rn_log) (L0 ++ [RelayEntry rc n data])) ∗
      entry_receipts γs γh (RelayEntry rc n data) }}}.

(* The receive loop: from a fresh connection (cursor 0, position 0),
   process every message in stream order until the peer goes away. *)
Lemma wp_Room__Serve r γ c sc rc :
  {{{ is_Room r γ ∗ ws_env_preserves ⊤ ∗ is_Connection c sc rc ∗
      own_recv_cursor rc 0 ∗ rc ↪[γ.(rn_pos)] 0 }}}
    r @! "Serve" #c
  {{{ RET #(); ∃ n, own_recv_cursor rc n ∗ rc ↪[γ.(rn_pos)] n }}}.
```

`wp_Room__process`'s proof shape: lock `room.mu`; run `codec_spec` (the
`ok = false` branch is closed by `ws_prot`'s decode fact); run
`wp_Doc__ApplySyncUpdate` (its `update_wf` premises come out of `ws_prot`,
its certificates likewise; `store.mu` is taken inside); mint the entry's
receipts from its postcondition; append to the log and advance `γpos`;
fan out exactly as W3a's `Broadcast` proof does, except each success also
extends that connection's `sent` list (the new entry is last in `L`, so
the sublist tie extends); unlock.

The full-run statements (S1-S4 over a whole execution) live in the room
invariant, exported at the top level (M4) through
`ws_dist_adequacy_prot`'s `φinv`: for every reachable global state there
is a log `L` such that the pure shadows of S2/S3 hold of the physical
wire, every server-sent message equals the payload of an earlier logged
entry (wire-level relay soundness), and every wire message decodes.
Non-vacuity of the environment side is already on file
(`ws_env_smoke.v`'s peers; their `may`/`coh` constrain only their own
channels, so they compose with a server run unchanged).

## 7. Optional small amendments (ask before taking)

- **7a `pending_item_rooted_pure`**: the `γs`-free alias of
  `pending_item_rooted` (store/heap.v), so `yjs_prot` does not name a
  store. Pure refactor, signature-compatible.
- **7b `is_store_client`**: a tiny persistent witness pinning a store's
  `ClientId` (the field is set once at `newStore` and never written), so
  `wp_Doc__ApplySyncUpdate` can return `is_history_lb γh c_srv …` with
  `c_srv` fixed instead of existential, and S1's receipts read "THE
  server's history grew". Touches `store_names`/`own_store` by one
  persistent clause and the `ApplySyncUpdate` postcondition; no other
  spec changes.

## 8. Explicitly out of scope, and why the design survives them

- **W3c, the handshake**: Step1 in, Step2 diff out. Slots in as a second
  entry kind in `relay_entry` (a reply-generating entry rather than a
  relay-generating one); S3's `relay_view` becomes a function over tagged
  entries; the diff itself needs the #51-style sender-side
  (`computeStateVector` / `computeDiff`), which is not in this tree.
- **Full functional determinism** ("the server's `(h, m, pend)` equals a
  pure replay of `L`"): strictly stronger than S1 and not needed for any
  of the asked properties. It requires colocating the store's exclusive
  history element with the log under one invariant, i.e. either a
  server-specific store lock invariant (a parallel `tie_body`, section
  store/heap.v) or a dfrac-agree pin threaded through every store write
  spec. Recorded as a possible later strengthening; recommendation: not
  now.
- **Multi-room**: `ws_prot` is global to the network and sees only bytes,
  but certificates are per-`γh` (per room), so a multi-room deployment
  needs the protocol to see the channel: `ws_prot : chan_id -> list u8 ->
  iProp` (the state interpretation's big_sepM is keyed by `(chan, n)`, so
  the generalization is mechanical). File as a W-issue; single-room until
  then.

## 9. Milestones

| milestone | contents | acceptance |
|---|---|---|
| M1 | Go changes (section 3) + goose; `yjs_prot` file (+ smoke `RootId` adjustment); codec-field translation spike | `./build.sh` green; `go test` end-to-end: two real WebSocket clients through the server converge (real codec, normal build) |
| M2 | room log + position ghosts; `wp_Room__process` / `wp_Room__Serve` with S1 receipts and S2 log ties | lemmas Qed, axiom-clean |
| M3 | strengthened `own_conn_send`, S3 sublist tie through `Join`/`process` | lemmas Qed, axiom-clean |
| M4 | closed-system theorem: wire-level relay soundness + protocol totality; env non-vacuity cited from `ws_env_smoke.v` | theorem Qed, axiom-clean |

M2 and M3 can land as one PR if review size permits; M1 is a natural
first PR (Go + protocol definition, no new proofs beyond re-basing W3a's
relay lemmas onto the new code shape).

Status note (2026-08-08): M1, M2 and M3 are implemented, plus `wp_Run`
(the accept loop: every accepted connection joined and served, so every
message flows through the S1/S2/S3-carrying `process`). Two findings
recorded while implementing M4's remaining half:

- The room ghosts live under the room's mutex, so log-based facts export
  through specs and receipts, not through an arbitrary-state `φinv` (a
  lock body is inaccessible while held). The closed theorem's exports are
  therefore the FFI-level ones: every wire message satisfies `yjs_prot`
  (protocol totality), i.e. decodes to a certified honest batch.
- `ws_dist_adequacy_prot` fixes `prot` before any ghost allocation, but
  `yjs_prot` needs the `γh` that `history_alloc` returns. The closed
  theorem therefore needs a variant whose protocol is chosen INSIDE the
  initial fancy update (allocate `γh`, then hand
  `prot := yjs_prot decode γh` to `ws_global_init_prot`); mechanically
  the same proof as `ws_dist_adequacy_prot` with the allocation
  inserted. Together with `wp_NewDoc` (assembling `is_Store` from
  `init_RWMutex` + `store_inv_init`, with the real lock-layer names
  instead of `store_inv_init`'s dummies) these are the two remaining
  pieces of M4.

## 10. Decisions requested

1. Scope W3b as sections 1-3 (update apply + relay; no handshake): OK?
2. Codec seam as a specification hypothesis over an opaque `yjs.Codec`
   (section 4), rather than a trusted-package axiom: OK?
3. One `room.mu` section across apply + fan-out (section 5.3), matching
   y-websocket's serialized handler: OK?
4. Amendments 7a/7b: take, or keep signatures untouched (existential `c`)?
5. Multi-room per-channel `ws_prot` generalization: file as an issue now,
   work later: OK?
