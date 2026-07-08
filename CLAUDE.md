# CLAUDE.md

Guidance for Claude Code (claude.ai/code) when working in this repository.

## Purpose

A formally verified Yjs. A Yjs-style CRDT is hand-written in Go (`yjs/`),
translated to a Rocq model with
[goose](https://github.com/mit-pdos/perennial/tree/master/goose), and verified
in Iris concurrent separation logic with
[Perennial](https://github.com/mit-pdos/perennial) (`src/proof/`). The Go is a
faithful port of [y-octo](https://github.com/y-crdt/y-octo) (Rust Yjs) — each
method cites its y-octo source in a comment — so the goal is formal
verification of a *realistic* Yjs implementation, not a toy.

## Rules

- **Predicate naming**: `is_X` = persistent handles / read-only facts
  (`is_Store`, `is_Text`, `is_text_lb`, `is_origin_id`, …); `own_X` =
  ownership, `dfrac`-parameterized when it is plain heap state (`own_ytype`,
  `own_dll`, `own_id_set`, `own_item_map`, …; `own_fresh_item` is exclusive and
  consumed by Integrate).
- **Public specs**: one `.v` proof file per Go file. Specs of public functions
  must not mention internal data (heap cells, node locations, flags) — state
  them over the public `is_X` / `own_X` predicates and their model parameters:
  `{{{ own_X o dq m ∗ ⌜Pre m⌝ }}} … {{{ own_X o dq m' ∗ ⌜Post m m' ret⌝ }}}`,
  with persistent `is_X` handles as duplicable hypotheses carrying monotone
  knowledge (e.g. `is_Text`'s grow-only `L`).
- **Report unrequested changes**: any change to the implementation
  (`yjs/*.go` behavior), a public function's spec/signature, or a proof-layer
  contract (rep predicates, invariants, WP specs) that was not explicitly
  asked for must be reported. In particular, any simplification that diverges
  from y-octo must carry a clear code comment **and** be reported. Mirror
  y-octo's containers faithfully (HashSet/HashMap → Go map, Vec → slice);
  don't downgrade a set to a slice for proof convenience.
- **Library bugs**: apparent bugs in the toolchain (Rocq, Iris, Perennial,
  goose, …) may be worked around to keep moving, but report them afterwards.
- **No unsolicited upstream activity**: never open pull requests, issues, or
  comments on repositories not owned by `iasakura` without explicit approval.
- **Reuse the rocq-yjs model — don't invent independent proofs**: state WP
  specs as refinements of the pure model and compose with its lemmas
  (`YjsArrInvariant_integrate`, `setintegrate_eq_integrate`,
  `integrate_commutative`, `yjs_strong_convergence`, …). Extract algorithmic
  cores into their own Go functions (e.g. `scanConflicts` /
  `findIntegrationLeft`) so hard loops are provable in isolation.
- **Writing style**: do not use em-dashes or en-dashes (the "—" / "–" long
  dashes) in prose, code comments, commit messages, PR text, or docs; they
  read as machine-written. Use commas, parentheses, colons, or a fresh
  sentence instead. Ordinary hyphens in compound words (`hand-written`,
  `goose-only`) are fine.

## Workflow

Write Go → translate with goose → prove, driven by `build.sh`:

```sh
./build.sh          # everything: go build → goose → make (proof check)
./build.sh go       # Go type check only (run first after editing Go)
./build.sh goose    # Go → Rocq translation (also runs go build)
./build.sh make     # proof check only (compile .v → .vo)
```

- **After editing any `yjs/*.go`, re-run goose** — `make` alone checks the
  stale translation and the Go change silently has no effect.
- Go tests (CRDT convergence tables): `GOTOOLCHAIN=go1.26.0 go test ./yjs/`
- Iterate on proofs with the rocq-mcp session (`rocq_start` once, then
  `rocq_check` / `rocq_step_multi`). coq-lsp tolerates errors and forward
  references, so **always finish with a strict `./build.sh make`**.
- Compile a single proof file (bypasses make's dep graph; `-o` must match the
  source basename):

  ```sh
  ARGS=$(sed -E -e '/^#/d' -e "s/'([^']*)'/\1/g" -e 's/-arg //g' _RocqProject)
  rocq compile $ARGS src/proof/yjs_store.v -o src/proof/yjs_store.vo
  ```

Environment: Go 1.26 (`build.sh` exports `GOTOOLCHAIN=go1.26.0`); a local
Perennial checkout for goose (default
`/home/ia/ghq/github.com/mit-pdos/perennial`, override with `PERENNIAL=…`, at
the commit pinned in `cert-yjs.opam`); an opam switch with Perennial installed
— all deps pinned by SHA in `cert-yjs.opam`'s `pin-depends` (including
`rocq-yjs`). One-time setup: see `WORKFLOW.md`. CI runs the same `build.sh`.

## Architecture

| path | contents | edit? |
|---|---|---|
| `yjs/*.go` | hand-written Go (port of y-octo) | yes |
| `src/proof/*.v` | hand-written proofs, one per Go file | yes |
| `src/code/`, `src/generatedproof/` | goose / proofgen output | **no — generated, gitignored** |

Never hand-edit generated files; change the Go and re-run goose. Proof files
`Require` each other in order `core → common (∥ network_model) → id → item →
ytype → history → store → text` and reopen the same `Section` boilerplate:

- `yjs_core.v` — re-exports the `rocq-yjs` / `iris-yjs` library (pure
  `integrate` / `setintegrate` model and its order theory).
- `yjs_common.v` — shared base: scalar abstractions (`toYjsId` / `toContent`),
  `item_cell` / `node_loc`, `own_id_set`, the package-init instances
  (declared once here, inherited via `Require`).
- `yjs_network_model.v` — the Iris-free bridge to the rocq-yjs *network*
  model (issue #42): `history_wf` over a raw `gmap ClientId (list Event)`,
  the packaging `to_network : … → YjsOperationNetwork`, `history_state_coh`,
  happens-before append-stability, freshness, receiver clock safety, the
  broadcast/deliver steps, `ValidReplay`, and `certs_ValidReplay`. No goose —
  iterate on it standalone.
- `yjs_id.v` — the `id` type: arithmetic round-trip, injectivity, equality
  specs.
- `yjs_item.v` — the `item` type: method specs, the DLL spine `own_dll` and
  its structural lemmas, `cell_repr` / `cells_repr`, the deletion-flag layer
  (`num_visible`, `flip_cell`, …).
- `yjs_ytype.v` — the `yType` container: public `own_ytype parent dq m`
  (model = items with tombstone bits) over cells-level `own_ytype_cells`,
  and `wp_yType__findPos`.
- `yjs_history.v` — the ghost op history (issue #42): the global invariant
  `is_history γh` (two `ghost_map`s + `history_wf`/`ops_coh`), the exclusive
  per-replica `own_client_history`, the persistent op certificate
  `is_op_cert`, and the fupd API `history_alloc` / `history_broadcast` /
  `history_deliver_batch` (+ a two-client smoke test).
- `yjs_store.v` — the `store` proofs: conflict scan refining `setfii_loop`,
  the item-set layer `own_item_map`, the lock layer (`store_inv` /
  `is_Store`, now carrying the client's ghost history tied to the governed
  text), and the Integrate stack up to `wp_Store__Integrate` /
  `wp_store__applyUpdate` / the certificate-based
  `wp_store__applyUpdate_certs`.
- `yjs_text.v` — the `Text` handle `is_Text t γh L` and the top-level
  `wp_Text__Insert` (which mints one op certificate per inserted item) /
  `wp_Text__Delete`.

## Notes

- `docs/proof-engineering.md` — the working technique reference (Rocq +
  ssreflect, Iris proof mode, Perennial/goose WP, rocq-mcp, cert-yjs
  gotchas). Read it before nontrivial proof work.
- `WORKFLOW.md` — build loop plus one-time environment setup.
