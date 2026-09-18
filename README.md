# cert-yjs

A Yjs-style text CRDT written in Go and verified in
[Perennial](https://github.com/mit-pdos/perennial) (Iris in Rocq). The Go
source is translated to a Rocq model with
[goose](https://github.com/mit-pdos/perennial/tree/master/goose), and the
proofs relate the running code to the pure Yjs algorithm: the integration
step, the document API, the sync protocol over a WebSocket server, and the
application that observes the text and patches its own copy.

The Go is written after three implementations of the Yjs CRDT:
[Yjs](https://github.com/yjs/yjs) (the original, v14),
[yrs](https://github.com/y-crdt/y-crdt) and
[y-octo](https://github.com/y-crdt/y-octo) (the Rust ports). The goal is a
verified implementation with the shape of a real one, not a toy.

## What is verified

Every theorem below is about the Go code as goose translates it, and
`./build.sh` checks all of them (CI runs the same script). No proof is
admitted; `Print Assumptions` shows only the goose and Perennial framework
axioms. The names are the Rocq lemmas.

- **Integration (YATA).** `wp_store__Integrate` (`src/proof/store/Integrate.v`):
  the Go integrate refines the pure `setintegrate` of
  [rocq-yjs](https://github.com/iasakura/rocq-yjs) and preserves the document
  invariant, so ordering and convergence follow from rocq-yjs's theory
  (`setintegrate_eq_integrate`, `integrate_commutative`) instead of a second
  proof.
- **Text API.** `wp_Text__Insert`, `wp_Text__Delete` (any valid document, any
  visible index), `wp_Text__String`, `wp_Text__Len` (`src/proof/text/`): the
  public API against a pure model (`is_Text`), under the store's `RWMutex`;
  readers run concurrently under the read lock.
- **Remote updates.** `wp_Doc__ApplySyncUpdate` (`src/proof/doc/`): applying
  a batch of remote structs is total (a struct whose dependencies have not
  arrived is buffered and drained by a later apply) and loses nothing (every
  received struct is delivered or buffered, `is_accepted`), against a ghost op
  history (`is_history_lb`) that records what each replica delivered.
- **Convergence.** `doc_strong_convergence` and
  `DocOperationNetwork_converge_final` (`src/proof/doc/model.v`): two nodes of
  a document network that delivered the same set of ops reach the same
  document, over rocq-yjs's causal-order theory.
- **Network.** `ws_server_dist_adequate` (`src/proof/demo/ws_server.v`): a
  closed-system theorem for the y-websocket style update server in `wsrelay/`
  over the ws FFI (`src/goose_lang/ffi/ws_ffi/`): in every reachable state of
  every execution, every message on the wire decodes to an honest batch. The
  FFI has a WebSocket realization (`wsnet/`) and an echo demo (`wsecho/`).
- **Observing the text.** `wp_TextObserver__Poll`, `wp_ApplyDelta`
  (`src/proof/textobserver/`) and the application theorem `wp_Mirror__Sync`
  (`src/proof/demo/observe_app.v`): the observer returns exactly Yjs's
  `YTextEvent.delta` between the snapshot it observed last and the current
  one, and patching the application's copy with it gives the current visible
  text (the observe / diff / patch pattern of issue #198).

## How it works

```
yjs/*.go  --goose-->  src/code/ (Rocq model of the Go)  <--checked against--  src/proof/
```

The model is regenerated from the Go on every build, so the proofs are always
about the code that runs. The proofs stack four levels.

1. **rocq-yjs**: the pure Yjs algorithm (integrate, the YATA order, strong
   convergence), ported from [lean-yjs](https://github.com/iasakura/lean-yjs).
2. **Document and network model** (`src/proof/doc/model.v`,
   `src/proof/network_model.v`, `src/proof/history.v`): a document over
   several root types, the global op history as ghost state, and the network
   of replicas, with the convergence theorems.
3. **Per-type proofs** (`src/proof/<type>/`), four layers each: `model.v` (the
   pure model of the type), `value.v` (what the Go values denote), `heap.v`
   (Iris representation predicates and invariants: the store lock invariant,
   ghost item sets, the delete set, the history), and one `wp_` file per
   method.
4. **Closed and application theorems** (`src/proof/demo/`), composed from the
   layers below.

Specs follow one shape: `is_X` is persistent knowledge, `own_X` is ownership,
a method takes the whole receiver's predicate and gives it back, and every
fact a spec states goes through a model parameter (see `CLAUDE.md`, "Specs
and invariants").

**Trusted base.** Rocq, Iris, Perennial and goose (the translation is
trusted); the ws FFI semantics and its Go realization (`wsnet/`); the v1 byte
codec (`yjs/codec.go`, unverified: verified code takes it as a value
satisfying `codec_spec`); and the assumption that peers speak the protocol
honestly (no Byzantine tolerance, as in Yjs).

## Scope and known gaps

- One root type, text, with single-byte content. Map, Array and XML types:
  #23 to #27.
- Every item is one character: no multi-element runs and no merge pass (#93,
  #94, #95); a remote struct is integrated only when its head id is new
  (#207).
- Remote deletes are applied by the verified path, but their effect on the
  visible text is not yet in the spec (#133). No garbage collection of
  tombstones (#82), no undo (#75).
- The wire codec is unverified (#31); the sync handshake (step 1 / step 2)
  is not implemented (#51, #129); the server protocol is one room per server
  (#117).
- Next: transactions (#206) and the synchronous observer callback on top of
  them; the references become Yjs v14, yrs and y-octo (#208).

## Repository layout

| path | contents |
|---|---|
| `yjs/` | the CRDT: store, integrate, text, doc, sync, observer (hand-written Go) |
| `observeapp/` | the observe / diff / patch application demo (a string mirror) |
| `wsrelay/` | the verified WebSocket update server (rooms, relay) |
| `wsnet/`, `wsecho/` | the ws FFI realization (WebSocket) and its echo demo |
| `grovenet/`, `pingpong/` | the Grove FFI realization (TCP) and its demo |
| `src/proof/` | the proofs, one directory per Go type, plus `doc/`, `demo/` and the top-level model files |
| `src/goose_lang/ffi/ws_ffi/`, `src/trusted_code/`, `src/manualproof/` | the ws FFI semantics and the trusted FFI models with their WP wrappers |
| `src/code/`, `src/generatedproof/` | goose / proofgen output (generated, gitignored) |
| `docs/` | design documents (`plan-*.md`) and the proof technique reference (`proof-engineering.md`) |

## Build and test

```sh
./build.sh                                  # go build -> goose -> make (proof check)
GOTOOLCHAIN=go1.26.0 go test ./yjs/ ./observeapp/ ./wsrelay/ ./wsecho/ ./pingpong/
```

One-time setup (an opam switch with the pinned Perennial fork and rocq-yjs)
and the day-to-day loop are in [WORKFLOW.md](WORKFLOW.md); the proof
technique reference is [docs/proof-engineering.md](docs/proof-engineering.md);
each milestone has a design document under `docs/`.

## References

- Yjs: Kevin Jahns, [yjs/yjs](https://github.com/yjs/yjs); the algorithm is
  YATA (Nicolai, Jahns et al., "Near Real-Time Peer-to-Peer Shared Editing on
  Extensible Data Types", GROUP 2016).
- yrs: [y-crdt/y-crdt](https://github.com/y-crdt/y-crdt); y-octo:
  [y-crdt/y-octo](https://github.com/y-crdt/y-octo).
- Perennial and goose: [mit-pdos/perennial](https://github.com/mit-pdos/perennial).
- The pure model: [iasakura/rocq-yjs](https://github.com/iasakura/rocq-yjs),
  ported from [iasakura/lean-yjs](https://github.com/iasakura/lean-yjs).

## Acknowledgements

The Go in `yjs/` is written after three implementations of the Yjs CRDT:
[Yjs](https://github.com/yjs/yjs), the original, and the Rust ports
[yrs](https://github.com/y-crdt/y-crdt) and
[y-octo](https://github.com/y-crdt/y-octo). Its data structures and integrate
algorithm are a port of y-octo (by the Toeverything / AFFiNE team); the text
observer follows Yjs's `YTextEvent.delta`.

## License

cert-yjs is released under the [MIT License](LICENSE). It includes software
derived from y-octo and Yjs (both MIT); see [NOTICE](NOTICE) for the required
third-party copyright and license notices.
