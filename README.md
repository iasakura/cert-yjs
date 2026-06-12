# cert-yjs

A Yjs-style CRDT implemented in Go and verified with
[Perennial](https://github.com/mit-pdos/perennial) (Iris/Rocq), using
[goose](https://github.com/mit-pdos/perennial/tree/master/goose) to translate
Go into a Rocq model.

- `yjs/` — the Go implementation
- `src/proof/` — hand-written correctness proofs
- See [WORKFLOW.md](WORKFLOW.md) for the build/proof loop and one-time setup.
