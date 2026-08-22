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
- **Predicates carry their meaning**: a predicate must be understandable from
  its name alone. When the name cannot carry it, the comment above the
  definition owes the reader BOTH the meaning and the places it is used. A
  qualifier that encodes which proof step produces or consumes the predicate
  (`apply_live_refine`, `integrate_live_refine`) is not self-explanatory, so
  name the call sites in the comment; restating the formula in prose adds
  nothing the `Definition` line does not already say. Names are spelled out,
  never contracted (`delete_set`, not `ds`).
- **Spec shape, for every function (exported or not)**: a WP spec is
  `{{{ own_X o dq m ∗ ⌜Pre m⌝ }}} … {{{ own_X o dq m' ∗ ⌜Post m m' ret⌝ }}}`,
  with persistent `is_X o m` handles as duplicable hypotheses carrying
  monotone knowledge (e.g. `is_Text`'s grow-only `L`). Everything the spec
  says about a value goes through a predicate's model parameter. Forbidden
  in a spec: struct field points-tos (`s .[store, "items"] ↦ …`), raw
  slices or maps of internal records, goose struct values and their fields
  (`yjs.item.t`, `itemVal.(left')`, `idv.(clock')`), flag bytes (`W8 2`),
  and `w64` / `uint.Z` arithmetic where the model already has the fact
  (`cell_covers`, `cell_fits`). Public predicates have the public model
  (`YjsItem` lists, `DocModel`, `gset YjsId`); store-internal helpers have
  the cell model (`item_cell` / `type_state`), and a node pointer appears
  only as the `ic_loc` / `node_loc` of a model cell. The return value is
  related to the model the same way (`RET #(f m)` or `⌜ret = f m⌝`).
- **Specs stay intuitive**: the developer's idea of a function is a few
  sentences, so its spec is a few conjuncts, never ten. Conditions are
  grouped by the data structure or the semantic unit they are about into one
  named predicate (`pool_invs`, `doc_registry_coh`, `cell_covers`, …), not
  listed as loose clauses. When a proof needs a new fact, first find the
  predicate it belongs to and add it there; a new top-level conjunct is the
  last resort, for a fact no existing predicate is about.
- **No over-specification**: a postcondition states each fact once (not
  `setintegrate input arr = Some arr'` next to its unfolding
  `arr' = take midx arr ++ …`) and states only what the function means. A
  fact that follows from the others, or that a caller merely finds
  convenient, is a lemma over the model or the predicates in the layer
  file, not a conjunct.
- **One spec per function**: a second spec exists only if it is used and
  cannot be derived from the first. Specs that are unused, or that are a
  stepping stone of one proof, are deleted or made `#[local]` in that
  proof's file.
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
  rocq compile $ARGS src/proof/store/heap.v -o src/proof/store/heap.vo
  ```

Environment: Go 1.26 (`build.sh` exports `GOTOOLCHAIN=go1.26.0`); a dedicated
`cert-yjs` opam switch with Perennial installed (dedicated because a switch has
one pin and this one is the fork, not upstream; see `WORKFLOW.md`), all deps
pinned by SHA in `cert-yjs.opam`'s `pin-depends` (including `rocq-yjs`). goose
runs from `$OPAM_SWITCH_PREFIX/.opam-switch/sources/perennial`, the pinned
source opam kept, so it is the pinned commit by construction; `PERENNIAL=…`
overrides it and `build.sh` refuses a goose whose `ffiMapping` lacks the
grovenet / wsnet entries, since translating with the wrong goose fails silently.
The pinned Perennial is a fork of `mit-pdos/perennial` carrying two
goose-only patches that map the `grovenet` package to the grove FFI (issue #45)
and the `wsnet` package to the ws FFI; both are required for the network
packages, since without the mapping the generated `Assumptions` class cannot fix
its `ffi_syntax` parameter. One-time setup: see `WORKFLOW.md`. CI runs the same
`build.sh`.

## Architecture

| path | contents | edit? |
|---|---|---|
| `yjs/*.go` | hand-written Go (port of y-octo) | yes |
| `grovenet/*.go`, `pingpong/*.go` | hand-written Go: the Grove network FFI realization (TCP) + its N0 feasibility demo (issue #45) | yes |
| `wsnet/*.go`, `wsecho/*.go` | hand-written Go: the ws (connection-oriented) network FFI realization (WebSocket) + its echo demo | yes |
| `src/goose_lang/ffi/ws_ffi/*.v` | hand-written ws FFI: operational semantics, Iris lifting lemmas, adequacy | yes |
| `src/proof/<type>/*.v` | hand-written proofs, one directory per Go type | yes |
| `src/trusted_code/.../*.v`, `src/manualproof/.../*.v` | hand-written trusted FFI models + their WP wrappers (grovenet ⇒ grove FFI, wsnet ⇒ ws FFI) | yes |
| `src/code/.../*.v.toml` | hand-written goose declfilter configs (per-package translate/trusted/imports) | yes |
| `src/code/`, `src/generatedproof/` | goose / proofgen output | **no — generated, gitignored** |

Never hand-edit generated files; change the Go and re-run goose.

`src/proof/` is one directory per Go type; inside a type the proofs are four
layers, each depending only on the ones below it.

| layer | file | holds | may mention |
|---|---|---|---|
| model | `model.v` | the pure model and its theory | rocq-yjs only |
| value | `value.v` | Go-level values and what they denote | + `yjs.*`, `loc`, `w64` |
| heap | `heap.v` | representation predicates, invariants, ghost state | + Iris |
| wp | `<Method>.v`, `wp_private.v` | the WP proofs | + the code |

```
src/proof/
  core.v  prelude.v  algebra.v  network_model.v  history.v
  ws_prelude.v  ws_relay.v
  id/     value.v  heap.v  wp_private.v  Add.v  Sub.v  Equal.v       id.v
  item/   model.v  run_theory.v  value.v  heap.v  wp_private.v
          Indexable.v  Len.v  Deleted.v                              item.v
  ytype/  model.v  value.v  heap.v  newYType.v  findPos.v            ytype.v
  store/  model.v  value.v  heap.v  wp_private.v
          Integrate.v GetNode.v splitNode.v repair.v applyUpdate.v   store.v
  text/   heap.v  Insert.v  Delete.v  Len.v                          text.v
  doc/    model.v  heap.v  ApplySyncUpdate.v                         doc.v
  demo/   pingpong.v  ws_echo.v
```

- **Files.** `<Method>.v` is one exported Go method's `wp_`; `wp_private.v` the
  unexported helpers' specs; `<type>.v` a `Require Export` facade, the only
  name downstream files Require. A layer a type does not need is absent (`id`
  has no model of its own; `Text` is a handle over a store type, so it starts
  at `heap.v`). Type-less files stay at the top level: `core.v` (rocq-yjs
  re-export + `YjsItem_countable`), `prelude.v` (the goose package-init
  instances, no definitions), `algebra.v` (generic Iris RA laws),
  `network_model.v` (pure op-history model), `history.v` (its ghost layer),
  `ws_prelude.v` (staged for perennial's `new/proof/`) and `ws_relay.v` (the
  WebSocket server's connection management, issue #107; left flat while that
  work is in flight).
- **Shape.** Section boilerplate first, then every definition, then every
  lemma, under `(* ===== definitions ===== *)` / `(* ===== lemmas ===== *)`.
  Never declare a `Context` mid-section: under `Set Default Proof Using "Type*"`
  it silently changes what the lemmas below are generalized over. Never
  annotate a `Require` line with a comment.
- **Definitions** live in `model.v` / `value.v` / `heap.v`, never in a WP file.
- **Lemmas.** A layer holds only what a caller must know: laws of its
  predicates, relations between predicates (coherence, projection,
  observation), state-transition laws. Everything else belongs in the WP file
  that needs it; "the WP proof uses it" is not a reason. A fact mentioning no
  cert-yjs definition goes to `algebra.v`.
- **Headers.** Each layer file opens with its API: the definitions it
  introduces and its laws, one line each. A lemma that does not earn that line
  does not belong in the layer. Read the header, not this file, for what is in
  a given file.

Require order is `core -> prelude -> algebra -> id -> item -> ytype ->
doc/model -> network_model -> history -> store -> text -> doc`. The pure layers
form their own sub-DAG below the Iris one, and each file's `.vok` is an
independent job (see the vos/vok Workflow note), so no single heavy proof
(splitNode, Insert, ...) serializes the build.

## Notes

- `docs/proof-engineering.md` — the working technique reference (Rocq +
  ssreflect, Iris proof mode, Perennial/goose WP, rocq-mcp, cert-yjs
  gotchas). Read it before nontrivial proof work.
- `WORKFLOW.md` — build loop plus one-time environment setup.
