# Design: the verified Go sync client (issue #131) and the multi-node closed theorem (issue #132, part 2)

The verified server (`wsrelay/`, `src/proof/ws_relay.v`) and its closed
theorem `ws_server_dist_adequate` (`src/proof/demo/ws_server.v`) are merged,
with the report trace of issue #239: after every applied update the server
writes the report of its root text to the run's trace, and the closed theorem
exports `reports_converge` over that trace.

That theorem is open in two places, both of them Iris-level hypotheses rather
than facts about the initial state:

- `ws_env_preserves`, the assumption that the peers the theorem does not run
  put only protocol-conforming messages on the wire (`src/goose_lang/ffi/ws_ffi/ws_ffi.v`,
  `ws_env_preserves`); `src/proof/ws_env_smoke.v` shows it is dischargeable,
  but no deployed code discharges it;
- `codec_spec`, the assumption that the Go decoder value meets the abstract
  `decode` the wire protocol `yjs_prot` is defined over (`src/proof/yjs_prot.v`).

This document fixes the design of the piece that removes the first one: a
verified Go client that connects to the server, applies what it receives
through the verified total apply path, encodes and sends its own local edits,
and traces its root's report. With it, a closed theorem over a server node and
client nodes needs no environment at all. The second hypothesis stays: the
byte codec remains the trusted seam, on the encoding side as it already is on
the decoding side.

## 0. TL;DR

- **Go, package `yjs`.** A transaction can hand back the structs it
  integrated, as decoded update items read from the store
  (`Transaction.insertedStructs`, the verified-subset counterpart of Yjs
  v14's `writeStructsFromTransaction`, which writes exactly the transaction's
  `insertSet`). The name of a struct's root is found by scanning the store's
  registry (`store.rootName`, Yjs v14's `findRootTypeKey`). The encoding half of the codec becomes a value next to the
  decoding half: `type Encoder = func(structs []updateItem) []byte`, with
  `WireEncoder()` in `codec.go` (`!goose`, trusted) as the deployment's.
- **Go, package `wsclient`.** `Client`: a connection, a document, the root
  text, the two codec values. `Connect` creates it; `Insert` is one local
  edit (insert inside a transaction, read the transaction's structs, encode,
  send, trace the root's report); `Serve` is the receive loop (apply, trace
  the root's report). `Run` is the scripted client the closed theorem boots:
  connect, serve on a goroutine, type a script one code unit at a time at
  the end of the text.
- **Specs.** `wp_Transaction__insertedStructs` returns `own_update_structs`
  whose inputs are the transaction's inserted items as the model holds them;
  `encoder_spec encode g` is `codec_spec`'s mirror image; the two abstract
  halves are tied by the pure hypothesis `codec_roundtrip decode encode`:
  what `decode` reads back from `encode inputs` is made of wire structs of
  `inputs`, for batches without surrogate code units (section 4.2). The
  wire protocol `yjs_prot` changes with it: a decoded struct with an origin
  is not required to carry the type it is certified under.
  The client's specs are the server's turned around: `is_Client` persistent,
  `Insert` consumes a send cursor and produces `yjs_prot` for what it sent
  (the certificates come from `wp_Text__InsertIn`), `Serve` consumes a
  receive cursor.
- **Closed theorem** `ws_system_dist_adequate` (new, `src/proof/demo/ws_system.v`):
  one server node and client nodes, each a `node_init_cfg`, over an initial
  global state with no environment channels and a send relation that permits
  nothing. Hypotheses: the initial state, `codec_spec`, `encoder_spec`,
  `codec_roundtrip`, and scripts without surrogate code units. No `ws_env_preserves`: it is proved inside the theorem
  from the send relation. Conclusion: wire totality and `reports_converge`
  over a trace that now holds every node's reports.

## 1. Scope

In scope: local inserts on one root text; the receive loop with the report
trace; the scripted client; the two-node closed theorem, then N clients.

Out of scope, recorded with what the design does about them:

- **Deletes from the client.** `yjs_prot` says nothing about deletes (they
  are state, not operations, `docs/plan-delete-set.md`), so a client's
  `Delete` needs only an encoder that writes a delete set. The `Encoder`
  value takes structs only for now; the delete-set half is a second value
  when `Delete` lands, so that neither spec changes.
- **The Step1/Step2 handshake (W3c).** A client that connects after edits
  were made never receives them (the server relays only what it applies after
  the join, `wsrelay.Join`). `reports_converge` is conditional on two reports
  holding the same ids, so it stays true; the quiescent convergence of issue
  #132 part 3 needs either the handshake or clients that start together,
  and is not claimed here.
- **A `doc.on('update')` observer registry.** y-websocket's provider sends
  from a document-level update handler (y-websocket v2.1.0 `src/y-websocket.js:353-361`).
  The client here reads the transaction's structs at the end of its own
  transaction closure instead; the data and the moment are the same, the
  registry is not built. The text observers of issue #198 show how one
  would be added later without touching the client's specs.
- **Liveness.** As in the server's theorem: nothing says a message is ever
  delivered.

## 2. References, and the three-way differences met

- **The update of a transaction.** Yjs v14.0.0-rc.18 emits, at transaction
  cleanup, the structs of the transaction's insert set read back from the
  struct store (`src/utils/Transaction.js:297-301`,
  `writeUpdateMessageFromTransaction` in `src/utils/encoding-helpers.js:103`,
  `writeStructsFromTransaction` at `:96`, which is
  `writeStructsFromIdSet(encoder, store, transaction.insertSet)`). yrs 0.27.2
  encodes the blocks whose clocks are at or beyond the transaction's
  `before_state` (`src/transaction.rs:597-627`, `encode_update_v1` via
  `store.write_blocks_from(before_state)`). y-octo 0.1.0 has no transaction;
  `DocStore::encode_with_state_vector` plays the yrs role. The Go follows
  Yjs: `Transaction.insertedStructs` walks `tr.insertSet`, the field the
  transaction already keeps (issue #198), and reads each span's items from
  the store's per-client lists. For a transaction of local edits the two
  readings coincide (every struct created since the transaction began is in
  its insert set); the insert-set reading is what the existing transaction
  record supports.
- **The name of a root type.** yrs's `Branch` carries `name: Option<Arc<str>>`
  ("for root-level types, this is a name of a branch", `src/branch.rs:201`);
  y-octo's `YType` carries `root_name: Option<String>`
  (`src/doc/types/mod.rs:39`). Yjs v14 keeps no name on the type and scans
  `doc.share` for the key when it writes a struct's parent
  (`findRootTypeKey`, `src/utils/ID.js:79`). The Go follows Yjs:
  `store.rootName` scans `store.types` for the key bound to the type. The
  first version of this document chose the field, expecting it to be the
  cheaper proof. It is not: `own_ytype` (`src/proof/ytype/heap.v`) hides the
  struct value under an existential, so stating that a type's `name` field
  is the key it is registered under means a new parameter on `own_ytype`
  (65 uses) or on `own_type_pool` (77 uses), or a field in `type_model`
  (219 constructions). The scan needs none of that: the store's registry
  coherence `pool_registry_coh` (`src/proof/store/value_cells.v`) already
  says that every registered type has exactly one name, and the functions
  that read the registry are store methods with the whole store at hand.
- **The wire parent.** All three write a struct's parent only when it has
  no left and no right origin (Yjs v14.0.0-rc.18 `Item.write`,
  `src/structs/Item.js:455-469`; yrs 0.27.2 `Item::encode`,
  `src/block.rs:780-797`; y-octo 0.1.0 `Item::write`,
  `src/doc/codec/item.rs:256`). `insertedStructs` fills `parentName` under the
  same rule; `is_update_item` already states it (`Hborrow`,
  `src/proof/store/heap.v`).
- **Sending.** y-websocket's provider sends every local update as soon as
  the transaction that made it ends; so does `Client.Insert`. The server's
  relay skips the origin (`wsrelay.process`, a recorded divergence from
  y-websocket), so the client never receives its own edits back; nothing in
  the client depends on that.

## 3. Go changes

### 3.1 `yjs/store.go`: the store's half

`store.rootName(parent *yType) string` scans `s.types` for the key bound to
`parent` (no early exit: one match, by the registry's coherence; it ranges
over the keys and looks each value up, because goose mistranslates a range
that binds key and value). `store.updateItemOfNode(it, start, stop)` is the
decoded struct of the code units `[start, stop)` of one node, and
`store.appendSpanStructs(structs, span)` appends the structs of the nodes
covering one recorded span, the first and the last cut to the span as Yjs's
`writeStructs` does. They are store methods because they read the store's
run lists and registry; `yType` is untouched.

### 3.2 `yjs/transaction.go`: `insertedStructs`

```go
// insertedStructs reads the structs this transaction integrated back from
// the store as decoded update items, in insert-set order: for each span of
// tr.insertSet, the items of that client's list from the span's first clock
// up to its end (Yjs v14.0.0-rc.18 writeStructsFromTransaction,
// src/utils/encoding-helpers.js:96, which writes the transaction's
// insertSet from the struct store; an item split after it was recorded is
// written as its parts, like Yjs's). A struct names its parent only when it
// has no origin on either side (Item.write).
func (tr *Transaction) insertedStructs() []updateItem
```

Per item: `id`, `originLeftId`, `originRightId`, `parentName` (a fresh cell
holding `s.rootName(it.parent)` when both origins are nil, else nil), `content` (the item's units; the
content slice is never written after creation, `content.go`, so the struct
shares it). The walk uses `getNodeIndex` on `s.items[client]` and the items'
`Len()`, as `writeStructsFromIdSet` walks `findIndexSS` from the span's
clock to its end.

Unexported: only `Client.Insert` calls it, inside its transaction closure.
Spelled `insertedStructs` and not `encodeUpdate` because it produces decoded
structs; the bytes are the trusted encoder's.

### 3.3 `yjs/doc.go`, `yjs/codec.go`: the encoder seam

```go
// Encoder is the encoding half of the update codec: the bytes that stand
// for a batch of insert structs (and an empty delete set). Like Codec it
// is a value verified code takes as a parameter and the client's proofs
// assume only its specification (encoder_spec, src/proof/yjs_prot.v)
// against the abstract encode; the real encoder is trusted to meet it.
type Encoder = func(structs []updateItem) []byte
```

`WireEncoder() Encoder` in `codec.go` (`!goose`): the v1 encoding of the
given structs grouped by client and sorted by clock, a clock gap written as
a Skip struct (Yjs v14 `writeStructs`), structs that continue each other
joined into one wire struct (so a surrogate pair typed in one insert leaves
as one code point), followed by an empty delete set. Go tests: `decodeUpdateItems(WireEncoder()(structs))` gives back the
structs; a two-replica test through `insertedStructs` + `WireEncoder` +
`ApplyUpdate`.

### 3.4 `wsclient/wsclient.go` (new package)

```go
// Client is one y-websocket client: its connection, its document, the root
// text it edits and reports on, and the deployment's codec values.
type Client struct {
	conn   wsnet.Connection
	doc    *yjs.Doc
	text   *yjs.Text
	name   string
	decode yjs.Codec
	encode yjs.Encoder
}

// Connect dials host at path, creates the document as client, and returns
// the client around them; the error flag is Connect's.
func Connect(host wsnet.Address, path string, client yjs.Client,
	decode yjs.Codec, encode yjs.Encoder, name string) (bool, *Client)

// Insert is one local edit: insert content at the visible index inside one
// transaction, read the structs that transaction integrated, encode them,
// send them, and write the report of the root to the trace. Returns Send's
// error flag. Not safe to call concurrently with itself (the connection's
// send side is the caller's), as Yjs documents are not thread-safe.
func (c *Client) Insert(index uint64, content []uint16) bool

// Serve is the receive loop until the peer goes away: apply every received
// update through the verified total apply path, and after each applied one
// write the report of the root to the trace.
func (c *Client) Serve()

// Run is the scripted client the closed theorem boots: connect, serve on a
// goroutine, and type script at the end of the text one code unit at a
// time. A real client calls Insert from its user interface instead.
func Run(host wsnet.Address, path string, client yjs.Client,
	decode yjs.Codec, encode yjs.Encoder, name string, script []uint16)
```

The transaction that makes the edit also reads the structs back, through a
closure that captures the result:

```go
var structs []updateItem
transact(t.store, func(tr *Transaction) {
	t.InsertIn(tr, index, content)
	structs = tr.insertedStructs()
})
return encode(structs)
```

### 3.5 Where the closure lives

`updateItem` and `insertedStructs` are unexported, so the transaction
closure that inserts and reads the structs back has to be in package `yjs`.
Two placements, decided in section 8:

- (a) `func (t *Text) InsertEncoded(index uint64, content []uint16, encode Encoder) []byte`
  in `yjs/text.go`: one transaction, insert, read the structs, encode, return
  the bytes. The client calls it and sends. The transaction and the encoder
  call are then inside `yjs`, with one proof (`wp_Text__InsertEncoded`)
  composing `wp_Doc__Transact`, `wp_Text__InsertIn`,
  `wp_Transaction__insertedStructs` and `encoder_spec`.
- (b) export the pieces (`UpdateItem`, `Transaction.InsertedStructs`) and
  keep the closure in `wsclient`.

Recommendation: (a). It keeps the update items internal, as `Codec`'s
return type is, and gives the client one call with one spec.

## 4. Specs

### 4.1 `wp_Transaction__insertedStructs` (`src/proof/transaction/insertedStructs.v`)

As verified (the first version of this section stated it per struct, which
does not survive a multi-character node):

```
{{{ is_pkg_init yjs ∗ own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed }}}
  tr @! (go.PointerType yjs.Transaction) @! "insertedStructs" #()
{{{ (structs_slice : slice.t) (structs : list Input), RET #structs_slice;
    own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed ∗
    own_update_structs structs_slice (DfracOwn 1) structs ∗
    ⌜∀ op, op ∈ expand_inputs structs ->
       ∃ name it, it ∈ doc_model_get m (RootId name) ∧
                  op = (RootId name, input_of_item it) ∧ item_id it ∈ inserted⌝ }}}
```

Per character, through `expand_inputs`: a struct may carry several
characters, the model and the certificates are per character. The store
half is `wp_store__appendSpanStructs` (over `own_store`), with
`wp_store__updateItemOfNode` and `wp_store__rootName` under it.

### 4.2 The wire protocol, `encoder_spec` and `codec_roundtrip` (`src/proof/yjs_prot.v`)

Three things turned out differently from the first version of this section.

**The protocol.** The bytes of a struct with an origin do not carry its
root, so no `decode` can report the type such a struct is certified under.
`yjs_prot` therefore relates what `decode` returns to the certified batch by
`same_wire_struct` (equal structs, and equal types unless the struct has an
origin), pointwise:

```
Definition yjs_prot γh d : iProp Σ :=
  ∃ decoded inputs,
    ⌜decode d = Some decoded⌝ ∗ ⌜Forall2 same_wire_struct decoded inputs⌝ ∗
    ⌜update_wf inputs⌝ ∗ is_pending_certified γh (expand_inputs inputs).
```

A receiver turns the decoder's slice into the certified batch with
`own_update_structs_same_wire_struct`, which needs `is_update_item` to say
that a decoded struct has a parent name exactly when it has no origin.

**The encoder's spec** is `codec_spec`'s mirror image, as planned:

```
Definition encoder_spec encode encoder : iProp Σ :=
  □ (∀ structs_slice dq structs,
      {{{ own_update_structs structs_slice dq structs }}}
        #encoder #structs_slice
      {{{ (bytes_slice : slice.t), RET #bytes_slice;
          own_update_structs structs_slice dq structs ∗
          bytes_slice ↦* encode structs ∗ own_slice_cap w8 bytes_slice (DfracOwn 1) }}}).
```

**The contract between the halves** is not
`decode (encode structs) = Some (expand_inputs structs)`. The real encoder
reorders (clients descending, clocks ascending), leaves out a struct that
repeats clocks already written, and writes a lone surrogate code unit as
U+FFFD (issue #233). The contract the real pair meets, and all a sender's
safety needs, is an inclusion over batches with no surrogate code unit:

```
Definition codec_roundtrip encode : Prop :=
  ∀ structs, structs_surrogate_free structs ->
    ∃ decoded, decode (encode structs) = Some decoded ∧
      ∀ decoded_struct, decoded_struct ∈ decoded ->
        ∃ sent_struct, sent_struct ∈ expand_inputs structs ∧
          same_wire_struct decoded_struct sent_struct.
```

`yjs_prot_encode` is the sender's lemma: from `codec_roundtrip`, a
surrogate-free batch whose expansion is well formed and certified,
`yjs_prot γh (encode structs)`. The consequence for the client: its inserts
must be free of surrogate code units, a precondition of `wp_Client__Insert`
and a hypothesis on the scripts of the closed theorem.

### 4.3 `wp_Text__InsertEncoded` (`src/proof/text/InsertEncoded.v`)

As verified:

```
{{{ is_pkg_init yjs ∗ is_Text t γs γh name L deleted_ids ∗ cs ↦*{dq} units ∗
    encoder_spec encode encoder }}}
  t @! (go.PointerType yjs.Text) @! "InsertEncoded" #idx #cs #encoder
{{{ (bytes_slice : slice.t) (L' ins : list (YjsItem A)) (client k0 : nat)
    (originLeft originRight : YjsPtr A) (structs : list Input), RET #bytes_slice;
    is_Text t γs γh name L' deleted_ids ∗ cs ↦*{dq} units ∗
    ⌜inserted_run L L' ins units client k0 originLeft originRight⌝ ∗
    ([∗ list] it ∈ ins, is_op_cert γh (RootId name, OpInsert (input_of_item it))) ∗
    bytes_slice ↦* encode structs ∗ own_slice_cap w8 bytes_slice (DfracOwn 1) ∗
    ⌜∀ op, op ∈ expand_inputs structs -> ∃ it, it ∈ ins ∧ op = (RootId name, input_of_item it)⌝ }}}
```

`wp_Text__Insert`'s postcondition with the bytes and their meaning added.
From it the client derives `yjs_prot decode γh (encode structs)` by
`yjs_prot_encode`: the certificates of `ins` cover every character of
`structs`, `update_wf` follows from `inserted_run` (one unit per item,
a head item names `name`), and surrogate-freeness from the caller's
content.

### 4.4 The client (`src/proof/ws_client.v`)

```
Definition is_Client (cl : loc) (γs : store_names) (γh : history_names) (c : ClientId)
    (sc rc : chan_id) (name : go_string) : iProp Σ :=
  "#Hconn"    ∷ is_Connection conn sc rc ∗
  "#Hdoc"     ∷ is_Doc dv s_loc γs γh ∗
  "#Htext"    ∷ is_Text t γs γh name [] ∅ ∗
  "#Hhist"    ∷ is_history γh ∗
  "#Hpin"     ∷ is_store_client γs c ∗
  "#Hcodec"   ∷ codec_spec decode fdec ∗
  "#Hencoder" ∷ encoder_spec encode fenc ∗
  "%Hdeploy"  ∷ ⌜deployment_protocols γh⌝
```

(with the struct's fields `conn`, `doc`, `text`, `name`, `decode`, `encode`
pinned to `conn`, `dv`, `t`, `name`, `fdec`, `fenc` under one read-only
points-to, as `is_Room` does). `deployment_protocols` moves from
`ws_relay.v` to `yjs_prot.v`, where both the server and the client can
`Require` it; `is_report` lives in `report/heap.v`, which `yjs_prot.v` does
not import, so the trace equation's right-hand side is stated over a
parameter there, or `deployment_protocols` goes to a small shared file
(`src/proof/deployment.v`) importing both. Settled when written.

```
Lemma wp_Client__Insert cl γs γh c sc rc name (n : nat) (idx : w64) (cs : slice.t) dq units :
  {{{ is_pkg_init wsclient ∗ is_Client cl γs γh c sc rc name ∗
      own_send_cursor sc n ∗ own_read_cap γs ∗ cs ↦*{dq} units }}}
    cl @! (go.PointerType wsclient.Client) @! "Insert" #idx #cs
  {{{ (err : bool), RET #err;
      cs ↦*{dq} units ∗ own_read_cap γs ∗
      ((⌜err = true⌝ ∗ own_send_cursor sc n) ∨
       (∃ data, own_send_cursor sc (S n) ∗ is_chan_msg sc n data)) }}}.
```

What was sent satisfies `ws_prot`, which the state interpretation records;
the postcondition does not repeat it (as `wp_Room__process` does not). The
read capability is what `Text.Snapshot` takes the read lock with, for the
trace.

```
Lemma wp_Client__Serve cl γs γh c sc rc name :
  {{{ is_pkg_init wsclient ∗ is_Client cl γs γh c sc rc name ∗
      own_recv_cursor rc 0 ∗ own_read_cap γs ∗ ws_env_preserves ⊤ }}}
    cl @! (go.PointerType wsclient.Client) @! "Serve" #()
  {{{ RET #(); ∃ n : nat, own_recv_cursor rc n ∗ own_read_cap γs }}}.
```

`ws_env_preserves` is `wp_Receive`'s precondition and stays in the lemma;
in the closed theorem it is proved once from the send relation.

```
Lemma wp_Connect host path (client : w64) fdec fenc name γh :
  deployment_protocols γh ->
  {{{ is_pkg_init wsclient ∗ is_history γh ∗
      own_client_history γh (uint.nat client) [] ∗
      codec_spec decode fdec ∗ encoder_spec encode fenc }}}
    @! wsclient.Connect #host #path #client #fdec #fenc #name
  {{{ (err : bool) (cl : loc), RET (#err, #cl);
      if err then True
      else ∃ γs sc rc, is_Client cl γs (uint.nat client) sc rc name ∗
             own_send_cursor sc 0 ∗ own_recv_cursor rc 0 ∗
             [∗] replicate (Z.to_nat rwmutex.actualMaxReaders) (own_read_cap γs) }}}.
```

On `err` the client's history element is consumed for nothing (the document
was created before the dial failed, or never); the scripted `Run` returns
on error. `wp_Run` composes the three; `client_boot` and `wpr_client_boot`
mirror `server_boot` and `wpr_server_boot` (`halt` on restart: a crashed
client has lost its document, like the server).

### 4.5 The closed theorem `ws_system_dist_adequate` (`src/proof/demo/ws_system.v`)

Nodes: `server_boot host server_client fdec name` and, per script in a list,
`client_boot host path client_i fdec fenc name script_i`. Initial global
state: `ws_msgs = ∅`, `ws_trace = []`, `ws_ext = ∅`, `ws_backlog = ∅`,
`ws_env_may = λ _ _ _, False`, `ws_wf`. Hypotheses beyond the initial
state and the RA plumbing: `codec_spec decode fdec`, `encoder_spec encode fenc`,
`codec_roundtrip decode encode`, distinct client ids, scripts without
surrogate code units (section 4.2). No `coh0`, no
`ws_env_preserves`: with `ws_may = λ _ _ _, False` the obligation's first
premise is `False`, so it is proved inside the theorem for
`ws_env_coh := λ _, True`.

Conclusion, for every reachable global state: every message on the wire
decodes to a well-formed batch, and `reports_converge ws_trace`. The trace
now interleaves the server's reports and every client's, so the conclusion
compares replicas: any two reports, from any two nodes, that hold the same
ids show the same text. That is issue #132 part 2 (the verified population
needs no conformance assumption) and the safety half of part 3 for the
states where the id sets agree.

The history is allocated for the set of all node ids
(`history_alloc {[server; c_1; …]}`), and each node's `wpr` lemma takes its
own `own_client_history`. `ws_wpd` is a `big_sepL` over the node list; the
server's conjunct is `wpr_server_boot` as today, each client's is
`wpr_client_boot`.

## 5. Ghost architecture

No new ghost state. The certificates the client sends are the ones
`wp_Text__InsertIn` already mints through `history_broadcast`; the
certificates the client consumes are the ones `yjs_prot` carries; the trace
protocol is `is_report`. The client has no lock: its send cursor stays with
the goroutine that calls `Insert`, its receive cursor with `Serve`, and the
document's own lock serializes the two against each other. The read
capabilities (`own_read_cap`) are exclusive tokens from `wp_NewDoc`; `Insert`
and `Serve` each hold one.

## 6. Milestones

| milestone | contents | acceptance |
|---|---|---|
| **C0** | this document | reviewed |
| **C1** Go | `store.rootName`, `store.appendSpanStructs`; `Transaction.insertedStructs`; `Encoder`, `WireEncoder`; `Text.InsertEncoded`; Go tests (encoder round trip through the real decoder; two documents converge through `InsertEncoded` + `ApplyUpdate`) | `./build.sh go`, `go test ./yjs/`, goose translates |
| **C2** proofs of C1 | the protocol change (`same_wire_struct`, `yjs_prot`, `encoder_spec`, `codec_roundtrip`), then `wp_store__appendSpanStructs`, `wp_Transaction__insertedStructs`, `wp_Text__InsertEncoded`; two pull requests | `./build.sh make` |
| **C3** Go client | `wsclient/`: `Client`, `Connect`, `Insert`, `Serve`, `Run`; tests against `wsrelay` (two clients converge through the server by the new send path; a report per edit on the trace) | `go test ./wsclient/`, goose translates |
| **C4** proofs of C3 | `is_Client`, `wp_Connect`, `wp_Client__Insert`, `wp_Client__Serve`, `wp_Run`, `client_boot`, `wpr_client_boot` | `./build.sh make` |
| **C5** closed theorem | `ws_system_dist_adequate`, server + one scripted client, then the list of clients | theorem Qed, `Print Assumptions` clean under a `.vo` build |

C1 and C3 are Go and tests; C2 and C4 are their proofs; each is one PR. C1
changes no verified function: it only adds new ones (`Text` gains
`InsertEncoded`).

## 7. Risks

- `insertedStructs` reads item fields through the store's heap predicates
  from the transaction layer (`own_transaction` holds `own_store`); the
  per-node predicate `own_item_node` pins the origin cells and the content
  (`src/proof/item/heap.v`), and `wp_store__GetNode` locates a node by id,
  so the pieces exist, but the walk over a span's items is new proof.
- Matching the returned structs against `wp_Text__InsertIn`'s `ins` needs
  uniqueness of ids within a root's model list; `inserted_run` gives the
  ids, `YjsArrInvariant` the uniqueness, and the lemma is pure.
- `codec_roundtrip` is a statement about the real codec that only tests
  check (as `codec_spec` is). The two-document Go test is that check.
- The multi-node theorem's `ws_wpd` over a list of heterogeneous nodes
  (one server lemma, N client lemmas) is bookkeeping in the style of
  `ws_server_dist_adequate`'s proof; the `wsGS`/`invGS` instance plumbing
  there (`goose_wsGS`, `iris_invGS`) is the part most likely to cost time.

## 8. Decisions requested

1. A registry scan (Yjs) over `yType.name` (yrs, y-octo): recommended, for
   the proof-cost reason in section 2. (The first version recommended the
   field; section 2 says what changed.)
2. `Text.InsertEncoded` in `yjs` (section 3.5 (a)) over exporting the update
   items: recommended.
3. The encoder seam as a value with `codec_roundtrip`, an inclusion over
   surrogate-free batches (section 4.2), as the closed theorem's pure
   hypothesis: recommended; the alternative is verifying the
   byte codec, a separate issue.
4. Scope: inserts only, no handshake, a report after every local insert and
   every applied update: recommended.
5. The closed theorem first over one scripted client, then over a list:
   recommended; the list version is the deliverable.
