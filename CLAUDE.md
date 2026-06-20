# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Yjs-style CRDT written in Go (`yjs/`), translated to a Rocq model with
[goose](https://github.com/mit-pdos/perennial/tree/master/goose), and proved
correct with [Perennial](https://github.com/mit-pdos/perennial) (Iris/Rocq) in
`src/proof/`. The Go data structures and the `integrate` algorithm are a faithful
port of [y-octo](https://github.com/y-crdt/y-octo) (Rust Yjs); each Go method
cites its y-octo source in a comment.

## Build / proof loop

The cycle is **write Go → translate to Rocq with goose → prove**. Driven by `build.sh`:

```sh
./build.sh          # everything: go build → goose → make (proof check)
./build.sh go       # Go type check only (run first after editing Go)
./build.sh goose    # translate Go → Rocq (also runs go build)
./build.sh make     # proof check only (compile .v → .vo)
```

**After editing any `yjs/*.go`, you must re-run goose** (`./build.sh goose` or
plain `./build.sh`). Running `make` alone keeps the stale translation and your Go
change silently has no effect.

Go tests (the integrate algorithm has table tests that check CRDT convergence):

```sh
GOTOOLCHAIN=go1.26.0 go test ./yjs/
GOTOOLCHAIN=go1.26.0 go test ./yjs/ -run TestConcurrentMiddleInsertConverges
```

### Iterating on proofs

For day-to-day proof work, prefer the rocq-mcp interactive session
(`rocq_start` once, then `rocq_check` / `rocq_step_multi`) over recompiling.
coq-lsp/Fleche tolerates errors and forward references, so **always finish with a
strict `./build.sh make`** — some errors only surface under `coqc`.

To compile a single proof file (fast, bypasses make's dep graph):

```sh
ARGS=$(sed -E -e '/^#/d' -e "s/'([^']*)'/\1/g" -e 's/-arg //g' _RocqProject)
rocq compile $ARGS src/proof/yjs_proof.v -o src/proof/yjs_proof.vo
```

The `-o` output name must match the source basename or Rocq errors with
"Source and target file names must coincide".

## Directory layout

| path | contents | edit? |
|---|---|---|
| `yjs/*.go` | hand-written Go (port of y-octo) | yes |
| `src/proof/*.v` | hand-written proofs | yes |
| `src/code/.../*.v` | goose output (GooseLang model) | **no — generated, gitignored** |
| `src/generatedproof/.../*.v` | proofgen output (struct points-to lemmas) | **no — generated, gitignored** |

Only `yjs/` and `src/proof/` are committed. Never hand-edit `src/code` or
`src/generatedproof`; change the Go and re-run goose instead.

## Proof architecture

The project is organized in phases (the Go has Phase 1 data structures and a
Phase 2 `integrate`). The proof is split into files that mirror the Go package
layout; each `Require`s its predecessors and reopens the same `Section`
boilerplate (`Context`, `Set Default Proof Using "Type*"`,
`Notation A := go_string`). The dependency order is `core → common → {item,
proof}`, then `item → store → text`:

- **`src/proof/yjs_core.v`** — re-exports the installed `rocq-yjs` / `iris-yjs`
  library (the pure `integrate` / `setintegrate` model and its order theory).
- **`src/proof/yjs_common.v`** — shared base imported by every other module:
  scalar abstractions `toYjsId` / `toContent`, the heap-node record `item_cell`
  and cursor `node_loc`, the persistent `is_origin_id`, item-pointer helpers
  `oid_of` / `item_or_null`, the id-slice abstraction `is_id_set`, and the
  `gset YjsId` rewrite lemmas. The goose package-init instances (`IsPkgInit` /
  `GetIsPkgInitWf`) are declared here **once** and inherited via `Require`.
- **`src/proof/yjs_item.v`** — the heap representation of the `item` sequence:
  the doubly-linked spine `is_dll` and its structural lemmas (split / join /
  accessor / insert), the cellwise isomorphism `resolve_*` / `cell_repr` /
  `cells_repr`, and the `yText` container `is_ytext` / `is_valid_ytext` relating
  a heap sequence to a `YjsArrInvariant` model list. (`is_ytext` lives here, not
  in `yjs_text`, because `yjs_store` depends on it.)
- **`src/proof/yjs_proof.v`** — basic per-method WP lemmas for the leaf `id` /
  `item` ops: Id arithmetic / equality, `itemPtrEqual`, node accessors
  (`gcNode` projections, item `Indexable` / `Len` / `Deleted`).
- **`src/proof/yjs_store.v`** — the `store` WP proofs: `findById`, the conflict
  scan (`scanConflicts` / `findIntegrationLeft`) refining `setfii_loop`, the
  item-validity / insertion helper lemmas, and top-level `wp_Store__Integrate`.
- **`src/proof/yjs_text.v`** — the `Text` / `yText` WP proofs: `findPos`,
  `insert_item_valid` / `insert_maximalId`, and top-level `wp_Text__Insert`
  (with `own_insert_doc`).

**Core principle: reuse the rocq-yjs model — do not invent independent proofs.**
State cert-yjs WP specs as *refinements* of the pure model and compose with
rocq-yjs's lemmas (`YjsArrInvariant_integrate`, `setintegrate_eq_integrate`,
`integrate_commutative`, `yjs_strong_convergence`, …). The Go is set-based
(y-octo, HashSet) while the verified loop in iris-yjs is scanning-based, so the
refinement needs a bridge between the two formulations.

**Extract algorithmic cores to their own Go functions** so the hard WP loop is
provable in isolation, separate from pointer surgery. The integrate conflict
scan lives in `scanConflicts` / `findIntegrationLeft` for exactly this reason.

**Faithfulness to the source**: mirror y-octo's containers — a Rust `HashSet`/
`HashMap` becomes a Go `map`, a `Vec` a slice. Perennial New has full `map`
support, so do not downgrade a set to a `[]slice` for proof convenience.

## Detailed technique reference

`docs/proof-engineering.md` is the working reference for this stack (Rocq +
ssreflect, Iris proof mode, Perennial New / goose WP, the rocq-mcp workflow, and
cert-yjs specifics). Read it before doing nontrivial proof work — it records the
non-obvious gotchas (e.g. `set_solver` hangs inside large WP proofs; goose
method-call stepping with `wp_method_call` / `wp_call` / `wp_func_call`;
RecordSet field-update reduction).

`WORKFLOW.md` covers the same build loop plus one-time environment setup.

## Environment

- **Go 1.26** is required (Perennial pins it); `build.sh` exports
  `GOTOOLCHAIN=go1.26.0`. Run Go commands with that toolchain set.
- A **local Perennial checkout** is needed for its bundled goose (not registered
  as a go.mod tool, so make's automatic goose does not run). `build.sh` defaults
  to `/home/ia/ghq/github.com/mit-pdos/perennial`; override with
  `env PERENNIAL=/path/to/perennial ./build.sh`. It must be at the commit pinned
  in `cert-yjs.opam`.
- An **opam switch with Perennial installed** (`New`/`Perennial` in user-contrib).
  All dependency versions are pinned by git SHA in `cert-yjs.opam`'s `pin-depends`
  (including `rocq-yjs` from iris-yjs). Either `opam switch link <existing>` or
  `opam switch create . ocaml-base-compiler.5.2.0 --no-install` then
  `opam install ./cert-yjs.opam --deps-only` (multi-hour first build).
- CI (`.github/workflows/ci.yml`) runs the same `build.sh` pipeline; all actions
  and dependencies are pinned by SHA.
