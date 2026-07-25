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
./build.sh make     # proof check only (parallel vos/vok; JOBS=N to cap -j)
./build.sh vo       # plain .vo full build (escape hatch; only if you need .vo)
```

`make` runs the proof check as Rocq's vos/vok split: a fast `-vos` pass
elaborates every file and emits its interface (skipping Qed bodies, follows the
dependency chain, ~30s), then a `-vok` pass checks the opaque proofs. Every
`.vok` needs only the `.vos` interfaces, so proof checking runs fully in
parallel across cores instead of one file at a time down the store → text
chain. vos + vok gives the same assurance as a `.vo` build (a broken Qed is
rejected in vok, verified), roughly 3x faster on this repo. It leaves `.vos` /
`.vok`, not `.vo`; use `./build.sh vo` when you actually need `.vo` files.

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
`rocq-yjs`). The pinned Perennial is a fork of `mit-pdos/perennial` carrying one
goose-only patch that maps the `grovenet` package to the grove FFI, required for
the network packages (issue #45). One-time setup: see `WORKFLOW.md`. CI runs the
same `build.sh`.

## Architecture

| path | contents | edit? |
|---|---|---|
| `yjs/*.go` | hand-written Go (port of y-octo) | yes |
| `grovenet/*.go`, `pingpong/*.go` | hand-written Go: the Grove network FFI realization (TCP) + its N0 feasibility demo (issue #45) | yes |
| `src/proof/*.v` | hand-written proofs, one per Go file | yes |
| `src/trusted_code/.../*.v`, `src/manualproof/.../*.v` | hand-written trusted FFI models + their WP wrappers (grovenet ⇒ grove FFI) | yes |
| `src/code/.../*.v.toml` | hand-written goose declfilter configs (per-package translate/trusted/imports) | yes |
| `src/code/`, `src/generatedproof/` | goose / proofgen output | **no — generated, gitignored** |

Never hand-edit generated files; change the Go and re-run goose. Proof files
`Require` each other in order `core → common (∥ network_model) → id → item →
ytype → history → store → text` (both `store` and `text` are `Require Export`
facades: `store` over `store_base → store_integrate → store_node → store_split
→ store_repair → store_update`, `text` over `text_base → {text_insert,
text_delete}`; downstream files import only the facade) and reopen the same
`Section` boilerplate. The files are split this fine so the proof check
parallelizes: each split file's `.vok` is an independent job (see the vos/vok
Workflow note), so no single heavy proof (splitNode, Insert, ...) serializes
the build:

- `yjs_core.v` — re-exports the `rocq-yjs` library (pure
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
- `yjs_store.v` — facade over the `store` proofs (one Go file, six
  internal proof files split for build-time parallelism; downstream files
  import only this):
  - `yjs_store_base.v` — ghost names and RAs, the item-set layer
    `own_item_map`, the lock body (`store_inv_ro` / `store_inv_excl` /
    `store_inv`, carrying the client's ghost history), the cohesive
    store-state predicate `own_store` over the model `(client, history,
    doc)`, the persistent witnesses `is_Store` / `is_type_lb` / `is_root`
    / `is_root_lb`, the RWMutex lock wrappers, and `store_inv_init`.
  - `yjs_store_integrate.v` — the integration stack: id-lookup helpers,
    the conflict scan refining `setfii_loop`, and `wp_Store__Integrate`
    (cells-level and model-level, with the item-map maintenance).
  - `yjs_store_node.v` — the node lookup path: `wp_getNodeIndex` /
    `wp_store__GetNode` and the applyUpdate input-expansion helpers
    (`expand_inputs_*`, `ValidReplay_chunk_extract`, the `types_*`
    accessors).
  - `yjs_store_split.v` — `wp_store__splitNode` and the
    `splitAtAndGetLeft/Right` range and invariant lemmas, plus the
    split-pool bookkeeping (`pool_invs`, `split_step_facts`, the
    `split_pool_*` / `split_cells_*` lemmas). The heaviest single proof.
  - `yjs_store_repair.v` — `getOrCreateYType`, `store.repair`
    (`wp_store__repair_split`), `integrateDecoded`, `depsArrived`, the
    `wire_*` drain machinery, and the `store_inv ⊣⊢ ∃ model, own_store`
    bridge (`store_inv_own_store`).
  - `yjs_store_update.v` — the top of the update path: the applyUpdate
    stack up to the `own_store`-level certificate spec
    `wp_store__applyUpdate_certs` (delivered content comes back as
    `is_root_lb` fragments). Requires node / split / repair.
- `yjs_text.v` — facade over the `Text` handle proofs (three files split
  for build-time parallelism; downstream imports only this):
  - `yjs_text_base.v` — the `Text` handle `is_Text t γh L`, its
    `is_Text_root` / `is_Text_root_lb` projections, and the
    `insert_item_valid` / `insert_maximalId` / `sorted_subseteq_*` helpers.
  - `yjs_text_insert.v` — the top-level `wp_Text__Insert` (mints one op
    certificate per inserted item).
  - `yjs_text_delete.v` — `wp_Text__Delete` and the read-path
    `wp_Text__Len`.

## Notes

- `docs/proof-engineering.md` — the working technique reference (Rocq +
  ssreflect, Iris proof mode, Perennial/goose WP, rocq-mcp, cert-yjs
  gotchas). Read it before nontrivial proof work.
- `WORKFLOW.md` — build loop plus one-time environment setup.
