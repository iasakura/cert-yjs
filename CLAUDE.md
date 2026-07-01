# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Yjs-style CRDT written in Go (`yjs/`), translated to a Rocq model with
[goose](https://github.com/mit-pdos/perennial/tree/master/goose), and proved
correct with [Perennial](https://github.com/mit-pdos/perennial) (Iris/Rocq) in
`src/proof/`. The Go data structures and the `integrate` algorithm are a faithful
port of [y-octo](https://github.com/y-crdt/y-octo) (Rust Yjs); each Go method
cites its y-octo source in a comment.

## Stop and ask before changing implementation or public contracts

Pause and confirm with the maintainer **before**:

- changing the implementation (any `yjs/*.go` behavior, not just refactoring);
- changing the spec, signature, or documented behavior of a public function or
  type;
- changing a WP spec, a representation predicate, or an invariant in
  `src/proof/*.v` (e.g. `store_inv`, `is_Text`, `cell_repr`, the loop invariants).

These ripple through the Go→goose→proof chain and the y-octo faithfulness
contract, so they are decisions to make together, not unilaterally. Proving an
existing spec, fixing a broken proof without weakening its statement, or other
work that leaves the implementation and all public contracts unchanged does not
need a check first.

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
`Notation A := go_string`). The dependency order is
`core → common → id → item → ytype → store → text`:

- **`src/proof/yjs_core.v`** — re-exports the installed `rocq-yjs` / `iris-yjs`
  library (the pure `integrate` / `setintegrate` model and its order theory).
- **`src/proof/yjs_common.v`** — shared base imported by every other module:
  scalar abstractions `toYjsId` / `toContent`, the heap-node record `item_cell`
  and cursor `node_loc`, the persistent `is_origin_id`, item-pointer helpers
  `oid_of` / `item_or_null`, and the id-slice abstraction `is_id_set`. The goose
  package-init instances (`IsPkgInit` / `GetIsPkgInitWf`) are declared here
  **once** and inherited via `Require`.
- **`src/proof/yjs_id.v`** — the `id` type: `newId` / `Id.Add` / `Id.Sub` and
  their round-trip, the `toYjsId` injectivity / `bool_decide` bridge, and the
  equality specs `Id.Equal` / `idOptEqual`.
- **`src/proof/yjs_item.v`** — the `item` type: per-node method specs
  (`Indexable` / `Len` / `Deleted`, `itemPtrEqual`), the doubly-linked spine
  `is_dll` and its structural lemmas (split / join / accessor / insert /
  `is_dll_update_gen` — the in-place node update used by `Delete`), the cellwise
  isomorphism `cell_repr` / `cells_repr` (`arr = ic_item <$> cells`, plus
  `cells_repr_update`), and the deletion layer (`is_deleted_flag` /
  `is_countable_flag` / `num_visible`; `set_deleted` / `flip_cell` /
  `cell_repr_flip` / `num_visible_*` and the flag readers `flags_if_deleted` /
  `flags_if_countable`).
- **`src/proof/yjs_ytype.v`** — the `yType` container (y-octo's lock-guarded inner
  sequence type; the `Text` handle is its unlocked wrapper): the heap predicate
  `is_ytype` / `is_valid_ytype` relating a heap `yType`'s DLL to a
  `YjsArrInvariant` model list (`len = num_visible cells`), and the tombstone-aware
  visible-index navigation `wp_yType__findPos` (returns an existential list
  position `p`). (This sits below `yjs_store` because `yjs_store` states
  `Store.Integrate` against `is_ytype`.)
- **`src/proof/yjs_store.v`** — the `store` WP proofs: `findById`, `containsId`,
  the conflict scan (`scanConflicts` / `findIntegrationLeft`) refining
  `setfii_loop` (with its top-level `gset` rewrite lemmas), the item-validity /
  insertion helper lemmas, the lock layer (`text_state` / `store_inv` /
  `is_Store` / `is_text_lb`), and top-level `wp_Store__Integrate`.
- **`src/proof/yjs_text.v`** — the `Text`-handle WP proofs: `insert_item_valid` /
  `insert_maximalId`, the lock-based handle `is_Text t L`, and the top-level
  `wp_Text__Insert` and `wp_Text__Delete`.

**Verified so far**: `Store.Integrate` preserves the document invariant
(`wp_Store__Integrate`); `Text.Insert(index, content)` grows the persistent handle
`is_Text t L` and exposes the inserted run (`wp_Text__Insert`); and
`Text.Delete(index, length)` preserves `is_Text t L` UNCHANGED (`wp_Text__Delete`):
tombstoning a run keeps every item in the list and never reorders the document, so
the model item list `ts_arr` — hence `YjsArrInvariant` and the known-content lower
bound `L` — is untouched; only the cells' `ic_deleted` bits and `yType.len` (the
visible count) change. All three are axiom-clean (`Print Assumptions` shows only
the goose/Perennial framework axioms). The document invariant tracks just the item
list: `is_ytype parent cells arr` ties the heap DLL to a `YjsArrInvariant` `arr`
with `cells_repr arr cells arr` = `arr = ic_item <$> cells`; the Deleted bit is
promoted onto the abstract cell as `ic_deleted` (the source of truth for
visibility), with `is_dll` pinning each node's heap flags to it and
`yType.len = num_visible cells`. The v1 byte codec stays behind `//go:build
!goose`; its DeleteSet is regenerated from the item flags at encode time
(`generateDeleteSet`, y-octo's `generate_delete_set`), so the verified `Delete`
only flips flags and shrinks the visible length. `cell_repr` pins `Len() = 1`; see
its `TODO` for relaxing that to add multi-clock items.

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
