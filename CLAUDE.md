# CLAUDE.md

## Project

A formally verified Yjs. A Yjs-style CRDT is hand-written in Go (`yjs/`),
translated to a Rocq model with
[goose](https://github.com/mit-pdos/perennial/tree/master/goose), and verified
in Iris concurrent separation logic with
[Perennial](https://github.com/mit-pdos/perennial) (`src/proof/`). The Go is a
faithful port of [y-octo](https://github.com/y-crdt/y-octo) (Rust Yjs), each
method citing its y-octo source in a comment, so the goal is formal
verification of a *realistic* Yjs implementation, not a toy.

Reviews of this repo are reviews of the specs and the invariants; the rules
below are mostly about those.

## Build and test

```sh
./build.sh          # everything: go build -> goose -> make (proof check)
./build.sh go       # Go type check only (run first after editing Go)
./build.sh goose    # Go -> Rocq translation (also runs go build)
./build.sh make     # proof check only (parallel vos/vok; JOBS=N to cap -j)
./build.sh vo       # plain .vo full build (escape hatch; only if you need .vo)
```

- **After editing any `yjs/*.go`, re-run goose.** `make` alone checks the stale
  translation and the Go change silently has no effect.
- **Run the build through the `cert-yjs` opam switch**
  (`opam exec --switch=cert-yjs -- ./build.sh`). Its perennial pin is the
  `iasakura` fork, whose goose carries the grovenet / wsnet `ffiMapping`;
  translating with a goose that lacks it fails silently and only shows up much
  later as undefined evars.
- `make` is Rocq's vos/vok split: a `-vos` interface pass (skips Qed bodies,
  ~30s), then a `-vok` pass that checks the opaque proofs fully in parallel.
  Same assurance as `.vo`, roughly 3x faster, but it leaves no `.vo` files.
- Go tests (CRDT convergence tables): `GOTOOLCHAIN=go1.26.0 go test ./yjs/`
- Iterate on proofs with the rocq-mcp session (`rocq_start` once, then
  `rocq_check` / `rocq_step_multi`). coq-lsp tolerates errors and forward
  references, so **always finish with a strict `./build.sh make`**.

`WORKFLOW.md` has the day-to-day loop, the single-file compile recipe, the
gotchas `build.sh` absorbs, and one-time environment setup. CI runs the same
`build.sh`.

## Specs and invariants

- **Spell every identifier out.** No cryptic abbreviations, in predicates,
  lemmas, binders and Go names alike: `key_pair` not `kp`, `state` not `st`,
  `leftNode` not `lft`, `delete_set` not `ds`. A reader should not have to
  reconstruct what a name stands for. The conventional short binders of the
  Iris and Perennial idiom (`dq`, `m`, `l`, `n`) stay.
- **`is_X` / `own_X`**: `is_X` is persistent, duplicable knowledge (`is_Store`,
  `is_Text`, `is_text_lb`, `is_origin_id`); `own_X` is ownership,
  `dfrac`-parameterized when it is plain heap state (`own_ytype`, `own_dll`,
  `own_item_map`; `own_fresh_item` is exclusive and consumed by Integrate).
- **A predicate's name must carry its meaning.** When it cannot, the comment
  above the definition owes the reader BOTH the meaning and the places it is
  used: a qualifier naming the proof step that produces or consumes it
  (`apply_live_refine`) is not self-explanatory. Restating the formula in prose
  adds nothing the `Definition` line does not say.
- **Spec shape, for every function, exported or not**:
  `{{{ own_X o dq m ∗ ⌜Pre m⌝ }}} … {{{ own_X o dq m' ∗ ⌜Post m m' ret⌝ }}}`,
  with persistent `is_X o m` handles as duplicable hypotheses carrying monotone
  knowledge (`is_Text`'s grow-only `L`). The return value is related to the
  model the same way (`RET #(f m)` or `⌜ret = f m⌝`).
- **The footprint is the whole receiver.** `own_X` / `is_X` is THE predicate of
  the receiver's type `X`, the one that owns every field of an `X`, not any
  predicate with an `own_` name: `s.Method()` takes `own_X s` whole and gives
  `own_X s` back, never a selection of its fields
  (`own_store_items s types ∗ own_type_pool dq types`) or a part borrowed out
  of it. If a proof only needs a part, the Go must say so (`s.fld.Method()`,
  `Method(s.fld, …)`), so the footprint is visible in the program and not only
  deep in the spec. Re-establishing `X`'s invariant is the callee's job, not
  something a postcondition hands to the caller.
  - An unexported method that is only an internal step of one public method,
    called while the receiver is open, cannot take `own_X` whole. First narrow
    the Go footprint so it can (a free function over the fields it touches, as
    `addNode` / `deleteNode`). If a lemma must still be stated while `X`'s
    invariant is broken, it is `#[local]` and goes through a RELAXED
    representation predicate (`own_X_<relaxation>`, defined in `heap.v` next to
    `own_X`, its extra model parameters tracking the pure state of the
    suspended invariant, with fold/unfold laws to `own_X`), never through a
    bare list of call-site resources; no such lemma currently exists. A helper
    with standalone meaning still takes `own_X` whole.
- **Everything a spec says about a value goes through a model parameter.**
  Forbidden in a spec: struct field points-tos (`s .[store, "items"] ↦ …`), raw
  slices or maps of internal records, goose struct values and their fields
  (`yjs.item.t`, `itemVal.(left')`, `idv.(clock')`), flag bytes (`W8 2`), and
  `w64` / `uint.Z` arithmetic where the model already has the fact
  (`cell_covers`, `cell_fits`). Public predicates have the public model
  (`YjsItem` lists, `DocModel`, `gset YjsId`); store-internal helpers have the
  cell model (`item_cell` / `type_state`), and a node pointer appears only as
  the `ic_loc` / `node_loc` of a model cell.
- **Specs stay intuitive.** The developer's idea of a function is a few
  sentences, so its spec is a few conjuncts, never ten. Conditions are grouped
  by the data structure or semantic unit they are about into one named
  predicate (`pool_invs`, `doc_registry_coh`, `cell_covers`), not listed as
  loose clauses. When a proof needs a new fact, first find the predicate it
  belongs to and add it there; a new top-level conjunct is the last resort, for
  a fact no existing predicate is about.
- **No over-specification.** A postcondition states each fact once (not
  `setintegrate input arr = Some arr'` next to its unfolding
  `arr' = take midx arr ++ …`) and states only what the function means. A fact
  that follows from the others, or that a caller merely finds convenient, is a
  lemma over the model or the predicates in the layer file, not a conjunct.
- **One spec per function.** A second spec exists only if it is used and cannot
  be derived from the first. Specs that are unused, or that are a stepping
  stone of one proof, are deleted or made `#[local]` in that proof's file:
  Integrate's stepping stone is folded into `wp_Store__Integrate`.
- **Reuse the rocq-yjs model, don't invent independent proofs.** State WP specs
  as refinements of the pure model and compose with its lemmas
  (`YjsArrInvariant_integrate`, `setintegrate_eq_integrate`,
  `integrate_commutative`, `yjs_strong_convergence`). Extract algorithmic cores
  into their own Go functions (`scanConflicts`, `findIntegrationLeft`) so hard
  loops are provable in isolation.

## Proof layout

| path | contents | edit? |
|---|---|---|
| `yjs/*.go` | the CRDT, hand-written port of y-octo | yes |
| `grovenet/`, `pingpong/`, `wsnet/`, `wsecho/` | Go network FFI realizations (TCP grove, WebSocket ws) and their demos | yes |
| `src/goose_lang/ffi/ws_ffi/`, `src/trusted_code/`, `src/manualproof/` | the ws FFI (semantics, lifting, adequacy) and the trusted FFI models with their WP wrappers | yes |
| `src/proof/<type>/*.v` | the proofs, one directory per Go type | yes |
| `src/code/**/*.v.toml` | goose declfilter configs | yes |
| `src/code/`, `src/generatedproof/` | goose / proofgen output | no: generated, gitignored |

Never hand-edit generated files; change the Go and re-run goose.

Inside a type the proofs are four layers, each depending only on the ones below
it.

| layer | file | holds | may mention |
|---|---|---|---|
| model | `model.v` | the pure model and its theory | rocq-yjs only |
| value | `value.v` | Go-level values and what they denote | + `yjs.*`, `loc`, `w64` |
| heap | `heap.v` | representation predicates, invariants, ghost state | + Iris |
| wp | `<Method>.v`, `wp_private.v` | the WP proofs | + the code |

- **Files.** `<Method>.v` is one exported Go method's `wp_`; `wp_private.v` the
  unexported helpers' specs; `<type>.v` a `Require Export` facade, the only
  name downstream files Require. A layer a type does not need is absent (`id`
  has no model of its own; `Text` is a handle over a store type, so it starts
  at `heap.v`). Type-less files stay at the top level: `core.v` (rocq-yjs
  re-export), `prelude.v` (goose package-init instances), `algebra.v` (generic
  Iris RA laws), `network_model.v` and `history.v` (the pure op-history model
  and its ghost layer), `ws_prelude.v` and `ws_relay.v` (WebSocket, issue #107).
- **Definitions** live in `model.v` / `value.v` / `heap.v`, never in a WP file.
- **Lemmas.** A layer holds only what a caller must know: laws of its
  predicates, relations between predicates (coherence, projection,
  observation), state-transition laws. Everything else belongs in the WP file
  that needs it; "the WP proof uses it" is not a reason. A fact mentioning no
  cert-yjs definition goes to `algebra.v`.
- **Shape.** Section boilerplate first, then every definition, then every
  lemma, under `(* ===== definitions ===== *)` / `(* ===== lemmas ===== *)`.
  Never declare a `Context` mid-section: under `Set Default Proof Using "Type*"`
  it silently changes what the lemmas below are generalized over. Never
  annotate a `Require` line with a comment.
- **Headers.** Each layer file opens with its API: the definitions it
  introduces and its laws, one line each. A lemma that does not earn that line
  does not belong in the layer. Read the header, not this file, for what is in
  a given file.

Require order is `core -> prelude -> algebra -> id -> item -> ytype ->
doc/model -> network_model -> history -> store -> text -> doc`. The pure layers
form their own sub-DAG below the Iris one, and each file's `.vok` is an
independent job, so no single heavy proof serializes the build.

## Reporting

- **Spec and invariant changes belong in the PR description.** A PR that
  changes a WP spec, a representation predicate, or an invariant says which one
  and how, before and after, and why; that is what the review is about. A PR
  that changes none says so. So: "`wp_Store__Integrate` takes
  `own_store_struct` whole where it took `own_store_items ∗ own_type_pool`, so
  that re-establishing the invariant is the callee's job", not "rethreaded the
  Integrate proof".
- **Report unrequested changes** in the conversation as well: any change to
  `yjs/*.go` behavior, to a public function's spec or signature, or to a
  proof-layer contract that was not explicitly asked for. Any simplification
  that diverges from y-octo must carry a clear code comment too. Mirror
  y-octo's containers faithfully (HashSet/HashMap to Go map, Vec to slice);
  don't downgrade a set to a slice for proof convenience.
- **Library bugs**: apparent bugs in the toolchain (Rocq, Iris, Perennial,
  goose) may be worked around to keep moving, but report them afterwards.
- **No unsolicited upstream activity**: never open pull requests, issues, or
  comments on repositories not owned by `iasakura` without explicit approval.
- **Writing style**: do not use em-dashes or en-dashes (the "—" / "–" long
  dashes) in prose, code comments, commit messages, PR text, or docs; they read
  as machine-written. Use commas, parentheses, colons, or a fresh sentence
  instead. Ordinary hyphens in compound words (`hand-written`) are fine.

## Reference

- `docs/proof-engineering.md`: the working technique reference (Rocq +
  ssreflect, Iris proof mode, Perennial/goose WP, rocq-mcp, cert-yjs gotchas).
  Read it before nontrivial proof work.
- `WORKFLOW.md`: build loop plus one-time environment setup.
