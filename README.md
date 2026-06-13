# cert-yjs

A Yjs-style CRDT implemented in Go and verified with
[Perennial](https://github.com/mit-pdos/perennial) (Iris/Rocq), using
[goose](https://github.com/mit-pdos/perennial/tree/master/goose) to translate
Go into a Rocq model.

- `yjs/` — the Go implementation
- `src/proof/` — hand-written correctness proofs
- See [WORKFLOW.md](WORKFLOW.md) for the build/proof loop and one-time setup.

## Acknowledgements

The Go data structures and the integrate algorithm in `yjs/` are a port of
[y-octo](https://github.com/y-crdt/y-octo), the Rust Yjs implementation by the
Toeverything / AFFiNE team.

## License

cert-yjs is released under the [MIT License](LICENSE). It includes software
derived from y-octo (also MIT); see [NOTICE](NOTICE) for the required
third-party copyright and license notices.
