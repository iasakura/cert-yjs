# cert-yjs

cert-yjs implements the text type of [Yjs][yjs] in Go, with a machine-checked
proof that the Go code places every character exactly where Yjs's algorithm
places it. The proof is written with [Perennial][perennial], a framework for
verifying concurrent and distributed Go programs, in the [Rocq][rocq] proof
assistant (formerly Coq). It is about the Go source itself, translated into
Rocq by goose, Perennial's translator for Go, not about a model of the code
written by hand.

Yjs is a library for collaborative editing. Each user edits a local copy of a
shared document, called a replica. Replicas send each other their edits as
updates, and receive updates in whatever order the network delivers them.
Replicas that have received the same edits must nevertheless end up with the
same document. This property is called convergence. The difficult case is two
users inserting at the same place at the same time: every replica has to put
the two insertions in the same order, whichever it received first. Yjs's
algorithm, YATA ([Nicolai, Jahns et al., GROUP 2016][yata]), decides where each
new character goes. It has been proven to converge, for the algorithm written
as functions on lists, in [lean-yjs][lean-yjs] and in its Rocq port
[rocq-yjs][rocq-yjs]. cert-yjs builds on rocq-yjs: its proofs show that the Go
code, which is built the way the real implementations are, computes what the
algorithm computes. The remaining step, convergence of the Go replicas
themselves, is not proven yet, for a reason given under
[What is proven](#what-is-proven).

The repository also has a WebSocket server that relays updates between
clients, with a theorem about every run of the complete server program.
[Limitations](#limitations) lists what is not implemented yet.

## Why verify an implementation

The proofs in rocq-yjs are about insertion written as a function from a list
of characters to a new list. They say nothing about code built the way real
implementations are, and the Go here is built that way, after [Yjs][yjs] and
its Rust ports [yrs][yrs] and [y-octo][y-octo]. A text is a doubly linked
list of items. Each item holds a character, pointers to its current
neighbours, and the ids of the two characters it was inserted between. To find
an item by its id, the code searches one sorted array per replica, by binary
search. The implementation also does what the algorithm leaves out: it buffers
insertions that arrive before the characters they depend on, computes each
change as a delta for the application, and lets several goroutines use a
document at once under a read-write lock.

Code of this kind can be wrong while the algorithm is right. Porting y-octo for
this project turned up three such bugs in it, each of which made replicas that
had applied the same edits show different text. One, in how it chose a new
character's neighbours, is fixed upstream ([y-octo#53][y-octo-53]). Fixes for
the other two, in how it handled items holding several characters, are
proposed in [y-octo#60][y-octo-60] and [y-octo#61][y-octo-61].

## What is proven

Each item below restates in plain language what the specifications in
`src/proof/` guarantee. They hold for every ASCII input and every interleaving
of goroutines, not only in the cases a test runs. They are safety properties:
they constrain everything the code does, but do not promise that a call
returns or that a message arrives. In Perennial's model of Go, a panic (an
index out of range, for example) and a data race are errors that every proof
has to rule out, so the verified code does neither when its callers meet the
specifications.

- **Every replica computes what the algorithm computes.** A replica keeps a
  text as a list of characters in which deleted characters stay in place,
  marked as deleted. This list is always the list the algorithm computes by
  applying, in order, the insertions the replica has applied, its own and
  those received from other replicas.
- **Local edits follow the algorithm.** `Insert(i, s)` inserts either nothing
  or one new character per byte of `s`, with fresh ids, placed the way the
  algorithm places them. Its specification does not yet say that it inserts
  anything, even for an index inside the text, or that the new characters
  land at index `i` ([#21][i21]). `Delete` only ever adds
  deletion marks, and which characters it marks is not specified yet
  ([#37][i37]). `String` returns a text that includes every insertion the
  caller has made or has seen applied, and none of the characters the caller
  has deleted. `Len` returns the length of such a text. Both run in parallel
  with other readers under the read lock.
- **Insertions from other replicas are never dropped.** Once an update's bytes
  are decoded, applying it never fails, and updates may arrive in any order.
  Each insertion in the update is either applied or, when a character it
  depends on has not arrived yet, kept in a buffer that later updates retry.
  That a buffered insertion is applied once what it depends on has arrived is
  not proven yet ([#102][i102]). The code also applies the deletions an update
  carries, but their effect is not specified yet ([#133][i133]).
- **Change deltas are exact.** An application can follow a text through its
  changes, which it gets as Yjs text deltas (retain n characters, insert a
  string, delete n characters). Applying a delta to the text the application
  saw last gives the current text. `observeapp/` is a small application that
  keeps a string copy of a text this way, and its proof shows that the copy
  equals the text.
- **The server forwards only what it has processed, in order.** `wsrelay/`
  accepts WebSocket connections, applies each update a client sends to the
  server's own replica, and forwards the update to the other clients. Its
  proof shows that it handles the messages each connection delivers in order,
  each once, and that it sends a client only updates from other clients that
  it has processed (applied, or buffered until what they depend on arrives),
  in the order it processed them. A send that fails is not retried, as in
  y-websocket, Yjs's reference WebSocket server. On top of this, a theorem
  about every run of the whole program from start-up states that, provided the
  clients follow the protocol, every message on the network decodes to a batch
  of insertions and none of the server's goroutines fails.

Convergence of the Go replicas is not proven yet. rocq-yjs proves that the
algorithm converges when every replica applies each insertion after everything
its author had seen when making it (causal order). The Go, like y-octo, applies
an insertion as soon as the two characters it was inserted between and its
author's previous insertion are present, which allows more orders than that.
Yjs and yrs also apply insertions in such orders. Extending the theorem to
these orders is outlined in section 5 of
[docs/plan-issue-40-pending.md][plan-40], and a theorem stating convergence for
a running system of several replicas is [#132][i132]. That replicas agree on
which characters are deleted needs the specification of remote deletions
([#133][i133]).

The specifications are in `src/proof/`: the text functions in `text/`,
applying updates in `doc/ApplySyncUpdate.v` and `doc/ApplyEncodedUpdate.v`,
the replicas' history in `history.v` and `network_model.v`, the example
application in `demo/observe_app.v`, and the server in `ws_relay.v` and
`demo/ws_server.v`.

## Limitations

- **Text only.** A document holds any number of named texts. Yjs's other
  shared types (Map, Array, the XML types, and types nested in other types) and
  rich-text formatting are not implemented.
- **ASCII only.** Each byte counts as one character, in positions and in ids,
  where Yjs counts UTF-16 code units. Worse, the Go turns each byte of inserted
  text into a string with `string(b)`, which Go reads as a code point, so a
  byte from 0x80 up becomes two bytes: inserting `"é"` stores `"Ã©"`. goose
  models this conversion as the byte itself, so the proofs do not see the
  difference and hold for ASCII text only.
- **One item per character.** Yjs keeps a run of characters typed together as
  one item and merges neighbouring items. Here every character is its own item,
  which costs memory. Runs in incoming updates are split into single
  characters.
- **Interoperability with Yjs is untested.** Updates are encoded in Yjs's v1
  format, but no test exchanges updates with the JavaScript Yjs library.
- **No garbage collection, undo or storage.** Deleted characters are never
  garbage-collected ([#82][i82]), there is no undo ([#75][i75]), and a document
  lives only in memory, with no storage or recovery after a crash
  ([#128][i128]).
- **A minimal server.** The server does not yet send the current document to a
  client that joins (Yjs's sync step 1 and step 2, [#129][i129]), and it serves
  a single room ([#117][i117]). It exchanges bare Yjs updates rather than
  y-websocket's protocol messages, so it is not a drop-in y-websocket server.

## How the proof works

The proofs in this repository connect the Go code to Yjs's algorithm. The
algorithm and its convergence theorem come from rocq-yjs:

```
Go source                         in yjs/
   │  goose translates it, on every build
   ▼
Rocq model of the Go program      generated into src/code/
   │  computes what the algorithm computes (proofs in src/proof/)
   ▼
Yjs's algorithm on lists          in rocq-yjs, proven there to converge
                                  under causal delivery
```

[goose][goose], Perennial's translator, turns the Go source into a model of
what the program does, written in GooseLang, a language defined in Rocq.
`./build.sh` regenerates this model from the source every time, so the proofs
are always about the current code.

The proofs in `src/proof/` give the translated Go functions specifications and
prove that the functions meet them. Specifications are written in
[Iris][iris], a separation logic for programs with pointers and concurrency, on
which Perennial is built. A specification says which value of rocq-yjs's model
the Go data structures stand for (for a text, which list of items its linked
list represents), and how a call changes that value. The central one is about
Yjs's integrate, the function that decides where a new character goes among
concurrent insertions at the same position: the Go version produces the same
list as rocq-yjs's integrate function (`wp_store__Integrate` in
`src/proof/store/Integrate.v`). A document's state lives in the invariant of
its read-write lock, and every write re-establishes that invariant before it
releases the lock.

To relate a replica to the algorithm, the proof keeps a history that exists
only in the proof (ghost state, in Iris terms): for every replica, the
insertions it has created and applied, in order. The proof of each write
re-establishes two facts about this history. First, every replica has applied
only insertions that some replica created, each once, and each only after the
characters it was inserted between and its author's previous insertion.
Second, each replica's list of characters, deleted ones included, is the list
its history computes. rocq-yjs's convergence theorem asks for causal delivery
where the first fact gives only the weaker order described under
[What is proven](#what-is-proven), so the theorem does not yet apply to the Go
replicas.

The server's theorem, `ws_server_dist_adequate` in
`src/proof/demo/ws_server.v`, is derived from the specifications of the
server's functions but speaks about every run of the whole program. It needs a
model of the network, which this project adds to GooseLang: a connection is two
ordered, exactly-once message channels (`src/goose_lang/ffi/ws_ffi/`). `wsnet/`
implements that model with WebSocket.

## What is trusted

The theorems rely on the following, which are not proven here.

- Rocq, and goose's translation. The proofs are about the GooseLang program
  that goose produces from the Go source, so the translation must be faithful,
  and Perennial's semantics of Go and of its `sync` package must match what the
  Go compiler and runtime do. One known mismatch is the conversion of a byte to
  a string (see ASCII only, above). The Perennial pinned here is a fork,
  [iasakura/perennial][perennial-fork], whose only change makes goose translate
  calls into `wsnet/` and `grovenet/` as calls into their network models.
- The model of WebSocket connections, and its implementation in `wsnet/` on top
  of [coder/websocket][coder-websocket].
- The encoding of updates as bytes, Yjs's v1 update format (`yjs/codec.go`,
  with `refs.go` and `delete.go`), which goose does not translate
  ([#31][i31]). This includes the byte-level `Doc.EncodeUpdate` and
  `Doc.ApplyUpdate`, which the Go tests use. The verified way to apply an
  encoded update is `Doc.ApplyEncodedUpdate`, which the server uses. Its
  specification and the server's theorem assume that decoding meets a
  specification (`codec_spec` in `src/proof/yjs_prot.v`).
- That other replicas follow the protocol. Yjs has no defence against a
  replica that sends fabricated updates, so this is a hypothesis of the
  theorems.

No proof in this repository or in rocq-yjs is admitted. The only axioms beyond
those Perennial itself relies on are the declarations goose generates for the
untranslated network packages `wsnet/` and `grovenet/`.

## Repository layout

| path | contents |
|---|---|
| `yjs/` | the library: documents, texts, transactions, observers, the update encoding |
| `wsrelay/` | the WebSocket update server |
| `observeapp/` | the example application that keeps a copy of a text |
| `wsnet/`, `wsecho/` | the WebSocket connections the server is written against, and an echo server |
| `grovenet/`, `pingpong/` | an earlier network layer over Perennial's Grove model of TCP, and a ping-pong demo |
| `src/proof/` | the proofs: one directory per Go type (`store/`, `text/`, `doc/`, ...), the history, the network model and the server's rooms (`ws_relay.v`) at the top level, and the proofs of the server and the demo programs in `demo/` |
| `src/goose_lang/ffi/ws_ffi/`, `src/trusted_code/`, `src/manualproof/` | the model of WebSocket connections, and the trusted interfaces of `wsnet/` and `grovenet/` |
| `docs/` | the design documents of the larger changes (`plan-*.md`), a survey of related work, and `proof-engineering.md`, the proof technique reference |

## Building and checking

```sh
./build.sh                          # go build, goose translation, proof check
GOTOOLCHAIN=go1.26.0 go test ./...  # Go tests
```

`./build.sh` needs an opam switch with the pinned Perennial and rocq-yjs.
[WORKFLOW.md](WORKFLOW.md) describes the one-time setup and the day-to-day
loop, including `JOBS=N`, which caps how many proof files are checked in
parallel and so the memory the check uses. CI runs the same script on every
push. [docs/proof-engineering.md](docs/proof-engineering.md) collects proof
techniques.

## Acknowledgements

The data structures and the integrate algorithm in `yjs/` are a port of
[y-octo][y-octo], by the Toeverything / AFFiNE team. The transaction and the
text observer follow [Yjs][yjs]. The comments in `yjs/` cite the y-octo code
each part is ported from. The newer code also cites Yjs and yrs, and says which
one it follows where they differ.

## License

cert-yjs is released under the [MIT License](LICENSE). It includes software
derived from y-octo and Yjs (both MIT); see [NOTICE](NOTICE) for the required
third-party copyright and license notices.

[yjs]: https://github.com/yjs/yjs
[yrs]: https://github.com/y-crdt/y-crdt
[y-octo]: https://github.com/y-crdt/y-octo
[y-octo-53]: https://github.com/y-crdt/y-octo/pull/53
[y-octo-60]: https://github.com/y-crdt/y-octo/pull/60
[y-octo-61]: https://github.com/y-crdt/y-octo/pull/61
[yata]: https://www.researchgate.net/publication/310212186_Near_Real-Time_Peer-to-Peer_Shared_Editing_on_Extensible_Data_Types
[rocq]: https://rocq-prover.org
[perennial]: https://github.com/mit-pdos/perennial
[perennial-fork]: https://github.com/iasakura/perennial
[goose]: https://github.com/mit-pdos/perennial/tree/master/goose
[iris]: https://iris-project.org
[lean-yjs]: https://github.com/iasakura/lean-yjs
[rocq-yjs]: https://github.com/iasakura/rocq-yjs
[coder-websocket]: https://github.com/coder/websocket
[plan-40]: docs/plan-issue-40-pending.md
[i21]: https://github.com/iasakura/cert-yjs/issues/21
[i31]: https://github.com/iasakura/cert-yjs/issues/31
[i37]: https://github.com/iasakura/cert-yjs/issues/37
[i75]: https://github.com/iasakura/cert-yjs/issues/75
[i82]: https://github.com/iasakura/cert-yjs/issues/82
[i102]: https://github.com/iasakura/cert-yjs/issues/102
[i117]: https://github.com/iasakura/cert-yjs/issues/117
[i128]: https://github.com/iasakura/cert-yjs/issues/128
[i129]: https://github.com/iasakura/cert-yjs/issues/129
[i132]: https://github.com/iasakura/cert-yjs/issues/132
[i133]: https://github.com/iasakura/cert-yjs/issues/133
