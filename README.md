# cert-yjs

A Yjs-style CRDT implemented in Go and verified with
[Perennial](https://github.com/mit-pdos/perennial) (Iris/Rocq), using
[goose](https://github.com/mit-pdos/perennial/tree/master/goose) to translate
Go into a Rocq model.

- `yjs/` — the Go implementation
- `src/proof/` — hand-written correctness proofs
- See [WORKFLOW.md](WORKFLOW.md) for the build/proof loop and one-time setup.

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
