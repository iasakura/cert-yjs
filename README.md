# Cert-Yjs

## Overview

Cert-Yjs is a project to build a realistic, [Yjs][yjs]-compatible
implementation in Go and to formally verify all of its features. Besides the
basic CRDT operations of [inserting and deleting][yjs-text], the features
include more advanced ones: [applying updates from other replicas and
exporting local updates][yjs-updates], [transactions][yjs-transactions],
[update observers][yjs-observe], and [undo and redo][yjs-undo].
[Current status](#current-status) says which of them are done.

Cert-Yjs is verified with [Perennial][perennial] in [Rocq][rocq], which
reasons about the Go source itself through its translation into Rocq by goose.
At its core, the verification shows that the Go code follows the pure model
of Yjs formalized in [Rocq-Yjs][rocq-yjs], in which basic properties such as
convergence are proven. Beyond that, it uses Iris's ghost state and invariants
to verify deeper specifications, such as the global protocol that every
replica must follow.

## Current status

### Verified

These are safety properties. They hold for every interleaving of goroutines
and every ASCII input, but do not promise that a call returns. The verified
code never panics and has no data races.

- **Every replica follows the pure model.** A replica keeps each text as a
  list of characters in which deleted characters stay in place, marked as
  deleted. This list is always the list Rocq-Yjs's algorithm computes from the
  insertions the replica has applied. In particular, the Go function that
  decides where a new character goes among concurrent insertions at the same
  place (Yjs's integrate) produces exactly the list Rocq-Yjs's integrate
  produces.
- **The global protocol.** A ghost history shared by all replicas records the
  insertions each replica has created and applied. The proofs maintain that
  every replica applies only insertions some replica created, each once and
  only after the two characters it was inserted between and its author's
  previous insertion, and that each replica's text is what its history
  computes.
- **Insertion and deletion.** `Insert` adds characters with fresh ids and
  places them as the algorithm does. `Delete` only ever marks characters as
  deleted. `String` and `Len` return a text that contains every insertion the
  caller has made or has seen applied and none of the characters the caller
  has deleted, and several of them run in parallel under the read lock.
- **Applying updates from other replicas.** Applying a decoded update never
  fails, and updates may arrive in any order. Each insertion in an update is
  either applied or, when a character it depends on has not arrived yet, kept
  in a buffer that later updates retry. No insertion is dropped.
- **Transactions.** `Doc.Transact` runs a group of writes (`InsertIn`,
  `DeleteIn`) as one transaction, as Yjs's `doc.transact` does. No other
  goroutine can write until the transaction ends, and `StringIn` returns the
  document's exact current text. `Insert`, `Delete` and applying an update are
  each one transaction.
- **Update observers.** An application can observe a text and receive its
  changes as Yjs text deltas (retain n characters, insert a string, delete n
  characters). Applying a delta to the text the application saw last gives
  exactly the current text. `observeapp/` is an example application that keeps
  a string copy of a text this way, and its proof shows that the copy equals
  the text.

### Remaining

- **Types other than Text.** Map, Array, the XML types, types nested in other
  types, and rich-text formatting are not implemented.
- **UTF-16.** Text is handled as bytes, one byte per character, so only ASCII
  text is supported. Yjs counts positions in UTF-16 code units.
- **Creating and merging runs.** Yjs keeps a run of characters typed together
  as one item and merges neighbouring items. Items here can hold runs too, and
  the verified code integrates a run as one item and splits an item when an
  edit lands inside it. What is missing is creating and merging them: `Insert`
  creates one item per character, the decoder of updates splits every received
  run into single characters before applying it, and neighbouring items are
  never merged.
- **Garbage collection, undo and redo** are not implemented.
- **Encoding updates as bytes.** Exporting local updates and reading received
  ones use Yjs's v1 update format, but this encoding is not verified. The
  verified code takes an update after it has been decoded.
- **Stronger specifications.** The specifications do not yet say that
  `Insert` inserts the new characters at the requested index, which characters
  `Delete` marks, what the deletions carried by an update from another replica
  do, or that a buffered insertion is applied once what it depends on has
  arrived.
- **Convergence of the Go replicas.** Rocq-Yjs proves convergence for replicas
  that apply insertions in causal order. The Go, like Yjs, applies an insertion
  as soon as the characters it depends on are present, which allows more
  orders, and the theorem has not been extended to them yet.
- **Compatibility with Yjs** is not tested: no test exchanges updates with the
  JavaScript Yjs library.

## Acknowledgements

The data structures and the integrate algorithm in `yjs/` are a port of
[y-octo][y-octo], by the Toeverything / AFFiNE team. The transaction and the
text observer follow [Yjs][yjs]. The comments in `yjs/` cite the y-octo code
each part is ported from. The newer code also cites Yjs and [yrs][yrs], and
says which one it follows where they differ.

## License

Cert-Yjs is released under the [MIT License](LICENSE). It includes software
derived from y-octo and Yjs (both MIT); see [NOTICE](NOTICE) for the required
third-party copyright and license notices.

[yjs]: https://github.com/yjs/yjs
[yjs-text]: https://docs.yjs.dev/api/shared-types/y.text#api
[yjs-updates]: https://docs.yjs.dev/api/document-updates#update-api
[yjs-transactions]: https://docs.yjs.dev/getting-started/working-with-shared-types#transactions
[yjs-observe]: https://docs.yjs.dev/api/shared-types/y.text#observing-changes-y.textevent
[yjs-undo]: https://docs.yjs.dev/api/undo-manager
[yrs]: https://github.com/y-crdt/y-crdt
[y-octo]: https://github.com/y-crdt/y-octo
[rocq]: https://rocq-prover.org
[perennial]: https://github.com/mit-pdos/perennial
[rocq-yjs]: https://github.com/iasakura/rocq-yjs
