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
  connect, serve on a goroutine, type a script at the end of the text, one
  byte of the script as one code unit.
- **Specs.** The three functions that read structs back from the store say
  exactly which characters the returned batch carries
  (`structs_expand_to_items`, an equivalence): the store's items with an id
  of the span, the items the transaction inserted, the items one insert
  created. `encoder_spec encode g` is `codec_spec`'s mirror image; the two
  abstract halves are tied by the pure hypothesis
  `codec_roundtrip decode encode`: the encoding of a well-formed batch
  without surrogate code units decodes to characters of the batch (section
  4.2). The wire protocol `yjs_prot` changes with it: the bytes decode to
  the certified batch up to the types the wire does not carry
  (`decodes_to`). The client's specs follow the server's: `is_Client`
  persistent, and two bundles of tokens, the send side for the goroutine
  that calls `Insert` and the receive side for the one that runs `Serve`.
- **Closed theorem** `ws_system_dist_adequate` (`src/proof/demo/ws_system.v`):
  one server node and a list of client nodes, over an initial global state
  whose send relation permits nothing. Hypotheses: the initial state,
  distinct client ids, `codec_spec`, `encoder_spec`, `codec_roundtrip`. No
  `ws_env_preserves` (it is proved inside the theorem from the send
  relation) and no condition on the scripts (a script is bytes, and a byte
  is never a surrogate code unit). Conclusion: wire totality and
  `reports_converge` over a trace that now holds every node's reports.

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

## 2. References, and the differences between them met

- **The update of a transaction.** Yjs v14.0.0-rc.18 emits, at transaction
  cleanup, the structs of the transaction's insert set read back from the
  struct store (`src/utils/Transaction.js:297-301`,
  `writeUpdateMessageFromTransaction` in `src/utils/encoding-helpers.js:103`,
  `writeStructsFromTransaction` at `:96`, which is
  `writeStructsFromIdSet(encoder, store, transaction.insertSet)`). yrs 0.27.2
  encodes the blocks whose clocks are at or beyond the transaction's
  `before_state` (`src/transaction.rs:597-627`, `encode_update_v1` via
  `store.write_blocks_from(before_state)`). The Go follows
  Yjs: `Transaction.insertedStructs` walks `tr.insertSet`, the field the
  transaction already keeps (issue #198), and reads each span's items from
  the store's per-client lists. For a transaction of local edits the two
  readings coincide (every struct created since the transaction began is in
  its insert set); the insert-set reading is what the existing transaction
  record supports.
- **The name of a root type.** yrs's `Branch` carries `name: Option<Arc<str>>`
  ("for root-level types, this is a name of a branch", `src/branch.rs:201`).
  Yjs v14 keeps no name on the type and scans
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
- **The wire parent.** Both write a struct's parent only when it has
  no left and no right origin (Yjs v14.0.0-rc.18 `Item.write`,
  `src/structs/Item.js:455-469`; yrs 0.27.2 `Item::encode`,
  `src/block.rs:780-797`). `insertedStructs` fills `parentName` under the
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
// goroutine, and type script at the end of the text one byte at a time,
// each byte as one code unit (an ASCII script types its text). A byte is
// never a surrogate code unit, so the script needs no side condition. A
// real client calls Insert from its user interface instead.
func Run(host wsnet.Address, path string, client yjs.Client,
	decode yjs.Codec, encode yjs.Encoder, name string, script string)
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

As verified. Where a statement differs from the first version of this
document, the difference and its reason are given.

### 4.1 The structs a store, a transaction and an insert hand back

One pure predicate states what all three functions promise about the batch
they return (`src/proof/store/model.v`):

```
Definition structs_expand_to_items structs (holds : go_string -> YjsItem A -> Prop) : Prop :=
  ∀ input, input ∈ expand_inputs structs <->
    ∃ name item, holds name item ∧ input = (RootId name, input_of_item item).
```

The characters of the batch (its per-character expansion `expand_inputs`)
are exactly the items `holds` names, each under the name of its root. Per
character, because a struct may carry several characters while the model and
the certificates are per character. An equivalence, so that the spec says
what the function returns and not only a bound on it: every such item is in
the batch, and nothing else is.

```
wp_store__appendSpanStructs (public for the store, over own_store):
  ... own_update_structs result_slice (DfracOwn 1) (structs ++ appended) ∗
  ⌜structs_expand_to_items appended (λ name item,
     registry_has_item (ss_bind state) (ss_pool state) name item ∧ item_id item ∈ span_ids span)⌝

wp_Transaction__insertedStructs:
  ... own_update_structs structs_slice (DfracOwn 1) structs ∗
  ⌜structs_expand_to_items structs (λ name item,
     item ∈ doc_model_get m (RootId name) ∧ item_id item ∈ inserted)⌝
```

The walk's completeness (every id of the span that the store holds is
appended) rests on invariants the store already has: a client's node list
is sorted with disjoint clock ranges, it holds every node of that client,
and a client's clocks are gap-free (`pool_clocks_contiguous`), so a span
whose first clock the store does not hold has no later clock in it either.

### 4.2 The wire protocol, `encoder_spec` and `codec_roundtrip` (`src/proof/yjs_prot.v`)

Three things turned out differently from the first version of this section.

**The protocol.** The bytes of a struct with an origin do not carry its
root, so no `decode` can report the type such a struct is certified under.
The protocol therefore says that the bytes decode to the certified batch up
to those types:

```
Definition decodes_to d inputs : Prop :=
  ∃ decoded, decode d = Some decoded ∧ Forall2 same_wire_struct decoded inputs.

Definition yjs_prot γh d : iProp Σ :=
  ∃ inputs, ⌜decodes_to d inputs⌝ ∗ ⌜update_wf inputs⌝ ∗
            is_pending_certified γh (expand_inputs inputs).
```

`same_wire_struct` is equal structs, and equal types unless the struct has
an origin. A receiver turns the decoder's slice into the certified batch
with `own_update_structs_same_wire_struct`, which needs `is_update_item` to
say that a decoded struct has a parent name exactly when it has no origin.

An alternative that was weighed and not taken: give `decode` a wire-level
codomain, `list (option TypeId * IntegrateInput)`, with the type present
only on structs without an origin, so that the protocol is an equation
`decode d = Some (wire_struct <$> inputs)`. It is the more honest model of
the bytes, and it would remove the made-up types from
`wp_Doc__ApplyEncodedUpdate`'s postcondition and from the closed theorems'
conclusions. It changes the type of `decode` in every merged file of the
server, so it is left as a follow-up; `decodes_to` confines the difference
to one definition in the meantime.

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
U+FFFD (issue #233); and the real decoder counts a struct's clocks in
machine words, so a struct whose clocks would pass 2^64 does not come back
as its characters. The contract the real pair meets, and all a sender's
safety needs, is an inclusion over well-formed batches with no surrogate
code unit:

```
Definition codec_roundtrip encode : Prop :=
  ∀ structs, structs_surrogate_free structs -> update_wf (expand_inputs structs) ->
    ∃ inputs, decodes_to (encode structs) inputs ∧ inputs ⊆ expand_inputs structs.
```

It is a trusted hypothesis, so it assumes no more than the proofs use; the
verified functions of section 4.1 are the ones that say exactly what they
return. `yjs_prot_encode` is the sender's lemma: from `codec_roundtrip`, a
surrogate-free batch whose expansion is well formed and certified,
`yjs_prot γh (encode structs)`.

### 4.3 `wp_Text__InsertEncoded` (`src/proof/text/InsertEncoded.v`)

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
    ⌜structs_expand_to_items structs (λ root item, root = name ∧ item ∈ ins)⌝ }}}
```

`wp_Text__Insert`'s postcondition with the bytes and their meaning added:
the bytes are the encoding of a batch that is, character by character,
exactly the inserted items. For a sender to put them on the wire it also
needs the inserted ids to fit machine words, which `inserted_run` did not
say; it gains that bound (`k0 + length ins < 2^64`, what `Text.Insert`'s
overflow guard establishes). With it, `yjs_prot_encode_inserted_run`
(`yjs_prot.v`) turns this postcondition, for code units free of surrogates,
into `yjs_prot decode γh (encode structs)`.

### 4.4 The client (`src/proof/ws_client.v`)

```
is_Client cl γs γh c sc rc name     (persistent)
own_Client_send_side γs sc    := ∃ n, own_send_cursor sc n ∗ own_read_cap γs
own_Client_receive_side γs rc := ∃ n, own_recv_cursor rc n ∗ own_read_cap γs
```

`is_Client` holds the struct read-only (every field is written once, by
`Connect`), the connection's, the document's and the root text's handles,
the history handle, the client pin with the empty history lower bound (what
a report's snapshot is certified against), the two codec specifications
with `codec_roundtrip`, and `deployment_protocols`. The two sides are
bundles of tokens keyed by ghost names, as the server's `own_processed` is:
a cursor of the connection and one read capability of the store (`report`
snapshots the root under the read lock).

```
wp_Connect: codec_roundtrip decode encode -> deployment_protocols decode γh ->
  {{{ is_history γh ∗ own_client_history γh (uint.nat client) [] ∗
      codec_spec decode decoder ∗ encoder_spec encode encoder }}}
    Connect #host #path #client #decoder #encoder #name
  {{{ err cl, RET (#err, #cl);
      if err then own_client_history γh (uint.nat client) []
      else ∃ γs sc rc, is_Client cl γs γh (uint.nat client) sc rc name ∗
             own_Client_send_side γs sc ∗ own_Client_receive_side γs rc }}}

wp_Client__Insert: units_surrogate_free units ->
  {{{ is_Client cl γs γh c sc rc name ∗ own_Client_send_side γs sc ∗ cs ↦*{dq} units }}}
    cl.Insert #index #cs
  {{{ err, RET #err; own_Client_send_side γs sc ∗ cs ↦*{dq} units }}}

wp_Client__Serve:
  {{{ is_Client cl γs γh c sc rc name ∗ own_Client_receive_side γs rc ∗ ws_env_preserves ⊤ }}}
    cl.Serve #()
  {{{ RET #(); own_Client_receive_side γs rc }}}

wp_Run: codec_roundtrip decode encode -> deployment_protocols decode γh ->
  {{{ is_history γh ∗ own_client_history γh (uint.nat client) [] ∗
      codec_spec decode decoder ∗ encoder_spec encode encoder ∗ ws_env_preserves ⊤ }}}
    Run #host #path #client #decoder #encoder #name #script
  {{{ RET #(); True }}}
```

What `Insert` sent satisfies `ws_prot`, which the state interpretation
records; the postcondition does not repeat it. A failed dial hands the
history element back: the document is created after the dial.
`ws_env_preserves` is `wp_Receive`'s precondition and stays in `Serve`'s
spec; in the closed theorem it is proved once from the send relation.

`deployment_protocols` moves from `ws_relay.v` to `src/proof/deployment.v`,
which both the server and the client `Require`, together with the package
initialization of the two packages both import.

### 4.5 The closed theorem `ws_system_dist_adequate` (`src/proof/demo/ws_system.v`)

Nodes: `server_boot host server_client decoder name` and, per entry of a
list of `client_config` (path, client id, script),
`client_boot host path client decoder encoder name script`
(`wsclient.initialize'` then `wsclient.Run`). Hypotheses beyond the initial
state and the RA plumbing: the initial world's send relation permits
nothing (`∀ messages channel data, ¬ ws_env_may messages channel data`),
the client ids are distinct, `codec_spec decode decoder`,
`encoder_spec encode encoder`, `codec_roundtrip decode encode`. No `coh0`
and no `ws_env_preserves`: with a send relation that permits nothing the
obligation's first premise is false (`ws_env_preserves_silent`), for the
coherence `λ _, True`. No condition on the scripts: `Run` types a script
byte by byte, and a byte is below the surrogate range.

Conclusion, for every reachable global state: every message on the wire
decodes to a well-formed batch, and `reports_converge ws_trace`. The trace
now interleaves the server's reports and every client's, so the conclusion
compares replicas: any two reports, from any two nodes, that hold the same
ids show the same text. That is issue #132 part 2 (the verified population
needs no conformance assumption) and the safety half of part 3 for the
states where the id sets agree.

The history is allocated for the set of all node ids, and each node's `wpr`
lemma takes its own `own_client_history`. `ws_wpd` is a `big_sepL` over the
node list; the server's conjunct is `wpr_server_boot` as before, each
client's is `wpr_client_boot`.

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
| **C5** closed theorem | `ws_system_dist_adequate`, server + a list of scripted clients | theorem Qed, `Print Assumptions` clean under a `.vo` build |

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

1. A registry scan (Yjs) over `yType.name` (yrs): recommended, for
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
