# CLAUDE.md

## Project

A formally verified Yjs. A Yjs-style CRDT is hand-written in Go (`yjs/`),
translated to a Rocq model with
[goose](https://github.com/mit-pdos/perennial/tree/master/goose), and verified
in Iris concurrent separation logic with
[Perennial](https://github.com/mit-pdos/perennial) (`src/proof/`). The Go is
written after the three Yjs implementations: [Yjs](https://github.com/yjs/yjs)
(v14, the primary reference for structure and naming),
[yrs](https://github.com/y-crdt/y-crdt) and
[y-octo](https://github.com/y-crdt/y-octo) (the Rust ports, the reference for
the typed rendering: containers, ownership), so the goal is formal verification
of a *realistic* Yjs implementation, not a toy. Where the three differ, the
difference is reported (see Reporting).

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

## Naming and specs

- **Spell every identifier out.** No cryptic abbreviations, in predicates,
  lemmas, binders and Go names alike: `key_pair` not `kp`, `state` not `st`,
  `leftNode` not `lft`, `delete_set` not `ds`. A reader should not have to
  reconstruct what a name stands for. Inside a proof script short forms are
  fine, where the name lives a few lines and the goal is in view; a name in a
  definition, a spec or the Go is spelled out.
- **Specs, predicates and invariants follow the `spec-shape` skill.** Load
  it before writing or changing a WP spec, a representation predicate, an
  invariant, or a definition in `model.v` / `value.v` / `heap.v`, and run its
  fresh-context review before pushing such a change.

## Proof layout

| path | contents | edit? |
|---|---|---|
| `yjs/*.go` | the CRDT, hand-written after Yjs / yrs / y-octo | yes |
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
| model | `model.v` | the pure model and its theory | Rocq-Yjs only |
| value | `value.v` | Go-level values and what they denote | + `yjs.*`, `loc`, `w64` |
| heap | `heap.v` | representation predicates, invariants, ghost state | + Iris |
| wp | `<Method>.v`, `wp_private.v` | the WP proofs | + the code |

- **Files.** `<Method>.v` is one exported Go method's `wp_`; `wp_private.v` the
  unexported helpers' specs; `<type>.v` a `Require Export` facade, the only
  name downstream files Require. A layer a type does not need is absent (`id`
  has no model of its own; `Text` is a handle over a store type, so it starts
  at `heap.v`). Type-less files stay at the top level of `src/proof/`.
- **Definitions** live in `model.v` / `value.v` / `heap.v`, never in a WP file.
- **Lemmas.** A layer holds only what a caller must know: laws of its
  predicates, relations between predicates (coherence, projection,
  observation), state-transition laws. Everything else belongs in the WP file
  that needs it; "the WP proof uses it" is not a reason. A fact mentioning no
  Cert-Yjs definition goes to `algebra.v`.
- **Shape.** Section boilerplate first, then every definition, then every
  lemma, under `(* ===== definitions ===== *)` / `(* ===== lemmas ===== *)`.
  Never declare a `Context` mid-section: under `Set Default Proof Using "Type*"`
  it silently changes what the lemmas below are generalized over. Never
  annotate a `Require` line with a comment.
- **Headers.** Each layer file opens with its API: the definitions it
  introduces and its laws, one line each. A lemma that does not earn that line
  does not belong in the layer. Read the header, not this file, for what is in
  a given file.

## Reporting

- **Spec and invariant changes belong in the PR description**, which is
  written for a reader who has not opened the diff. A PR that changes a WP
  spec, a representation predicate, or an invariant says which one, before
  and after, and why, in full sentences, every project term explained at first
  use; a PR that changes none says so. So: "`wp_Store__Integrate` takes
  `own_store_struct` whole where it took `own_store_items ∗ own_type_pool`, so
  that re-establishing the invariant is the callee's job", not "rethreaded the
  Integrate proof". The `pr-description` skill has the layout and the rest.
- **Report unrequested changes** in the conversation as well: any change to
  `yjs/*.go` behavior, to a public function's spec or signature, or to a
  proof-layer contract that was not explicitly asked for. Any simplification
  that diverges from the references must carry a clear code comment too.
  Mirror the references' containers faithfully (HashSet/HashMap to Go map,
  Vec to slice); don't downgrade a set to a slice for proof convenience.
- **Report every three-way difference.** The references are Yjs v14, yrs and
  y-octo. Each place where they differ is reported every time it is met: the
  PR description says which one the Go follows and why, and a code comment at
  the divergence says the same. A citation names the implementation and its
  version (`Yjs v14.0.0-rc.18 src/utils/Transaction.js:…`, `yrs 0.x src/…`,
  `y-octo src/doc/store.rs:…`).
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
  ssreflect, Iris proof mode, Perennial/goose WP, rocq-mcp, Cert-Yjs gotchas).
  Read it before nontrivial proof work.
- `WORKFLOW.md`: build loop plus one-time environment setup.
