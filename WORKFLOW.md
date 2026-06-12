# Development workflow

Write Go → translate to Rocq → prove. Three steps.

## TL;DR

    ./build.sh        # go build -> goose translation -> make (proof check)

Step by step when something breaks:

    ./build.sh go      # Go type check only (run first after editing Go)
    ./build.sh goose   # translate to Rocq (also runs go build)
    ./build.sh make    # compile = type check + proof check

## Day-to-day loop

1. Edit Go (yjs/*.go)
2. `./build.sh go` to check it compiles
3. `./build.sh goose` to translate; this updates src/code/.../*.v (the model)
   and src/generatedproof/.../*.v (struct lemmas)
4. Write/fix proofs in src/proof/*.v
5. `./build.sh make`; exit 0 means type check + proof check passed

Note: after changing Go, always re-run goose. `make` alone keeps the stale
translation and your change will appear to have no effect. Plain `./build.sh`
(= all) is the safe default.

## Checking a single proof file (fast)

    ARGS=$(sed -E -e '/^#/d' -e "s/'([^']*)'/\1/g" -e 's/-arg //g' _RocqProject)
    rocq compile $ARGS src/proof/yjs_proof.v -o src/proof/yjs_proof.vo

- The output name must match the source name (`-o .../yjs_proof.vo`),
  otherwise: "Source and target file names must coincide".
- Insert a temporary `Show.` at the line you want to inspect to dump the goal.

## Directory layout

| path | contents | edit? |
|---|---|---|
| yjs/ | hand-written Go | yes |
| src/proof/*.v | hand-written proofs | yes |
| src/code/.../*.v | goose translation (GooseLang model) | no, generated |
| src/generatedproof/.../*.v | proofgen (struct points-to lemmas) | no, generated |

Generated files (src/code, src/generatedproof) are gitignored. Only Go and
src/proof are committed.

## Gotchas absorbed by build.sh

- Go version: perennial requires go 1.26 → GOTOOLCHAIN=go1.26.0 is exported.
- goose location: not registered as a go.mod tool, so make's automatic goose
  does not run; perennial's bundled goose is called via --local. This matches
  the perennial commit pinned in cert-yjs.opam.
- `.goose-output` is touched to tell make the translation already happened.
- `src/generatedproof/_` is cleaned up (proofgen occasionally emits it).

On a machine with perennial elsewhere:

    env PERENNIAL=/path/to/perennial ./build.sh

## One-time setup

- An opam switch with Perennial installed (New / Perennial in user-contrib).
  Either share an existing switch:

      opam switch link <path-to-switch> .

  (e.g. the perennial-sandbox local switch, which uses the same pins), or
  build a dedicated one (takes hours):

      opam switch create . ocaml-base-compiler.5.2.0 --no-install
      opam install ./cert-yjs.opam --deps-only

- A local perennial checkout (with bundled goose) at the same commit as the
  pin in cert-yjs.opam.
