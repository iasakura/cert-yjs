# Development workflow

Write Go → translate to Rocq → prove. Three steps.

## TL;DR

    ./build.sh        # go build -> goose translation -> make (proof check)

Step by step when something breaks:

    ./build.sh go      # Go type check only (run first after editing Go)
    ./build.sh goose   # translate to Rocq (also runs go build)
    ./build.sh make    # type check + proof check (parallel vos/vok)

## Day-to-day loop

1. Edit Go (yjs/*.go)
2. `./build.sh go` to check it compiles
3. `./build.sh goose` to translate; this updates src/code/.../*.v (the model)
   and src/generatedproof/.../*.v (struct lemmas)
4. Write/fix proofs in src/proof/<type>/*.v
5. `./build.sh make`; exit 0 means type check + proof check passed

Note: after changing Go, always re-run goose. `make` alone keeps the stale
translation and your change will appear to have no effect. Plain `./build.sh`
(= all) is the safe default.

`make` runs the proof check as Rocq's vos/vok split (`make -j vos` then
`make -j vok`): a fast interface pass that skips Qed bodies, then an opaque
proof pass that runs fully in parallel across cores. It is about 3x faster than
the old serial `.vo` build and gives the same assurance (a broken Qed still
fails, in the vok phase). It writes `.vos` / `.vok`, not `.vo`; run
`./build.sh vo` if you actually need `.vo` files. Cap parallelism with
`JOBS=N ./build.sh make` (default: nproc).

## Checking a single proof file (fast)

    ARGS=$(sed -E -e '/^#/d' -e "s/'([^']*)'/\1/g" -e 's/-arg //g' _RocqProject)
    rocq compile $ARGS src/proof/store/heap.v -o src/proof/store/heap.vo

- The output name must match the source name (`-o .../repr.vo`),
  otherwise: "Source and target file names must coincide".
- Insert a temporary `Show.` at the line you want to inspect to dump the goal.
- For a structure-only check (does it elaborate, are the statements and
  `Require`s right?) add `-vos` and target `.vos`: it skips every Qed body and
  returns in seconds. Handy when reorganizing files. Follow with a real
  `.vo`/`.vok` for the proofs.

      rocq compile $ARGS -vos src/proof/store/heap.v -o src/proof/store/heap.vos

## Directory layout

| path | contents | edit? |
|---|---|---|
| yjs/ | hand-written Go | yes |
| src/proof/<type>/*.v | hand-written proofs, one directory per Go type | yes |
| src/code/.../*.v | goose translation (GooseLang model) | no, generated |
| src/generatedproof/.../*.v | proofgen (struct points-to lemmas) | no, generated |

Generated files (src/code, src/generatedproof) are gitignored. Only Go and
src/proof are committed.

## Gotchas absorbed by build.sh

- Go version: perennial requires go 1.26 → GOTOOLCHAIN=go1.26.0 is exported.
- goose location: not registered as a go.mod tool, so make's automatic goose
  does not run; perennial's bundled goose is called via --local. Its source is
  `$OPAM_SWITCH_PREFIX/.opam-switch/sources/perennial`, i.e. the very perennial
  opam installed, so goose is the pinned commit by construction and cannot
  drift from the library it was translated against.
- goose is refused if that source is missing, or if its `ffiMapping` lacks the
  grovenet / wsnet entries. Translating with the wrong goose is silent: the
  package comes out with no ffi prelude and only fails much later, as
  UNDEFINED EVARS in the generated `Assumptions` class.
- `.goose-output` is touched to tell make the translation already happened.
- `src/generatedproof/_` is cleaned up (proofgen occasionally emits it).

To translate with a perennial checkout of your own instead (it must carry the
ffiMapping entries; see the note above):

    env PERENNIAL=/path/to/perennial ./build.sh

## One-time setup

- A **dedicated** opam switch with Perennial installed (New / Perennial in
  user-contrib). Dedicated because `cert-yjs.opam` pins perennial to the
  `iasakura` fork, and a switch has one pin: shared with other perennial
  projects it would either hand them the fork or leave cert-yjs building
  against something its own opam file does not declare. (The fork's patches
  touch no `.v`, so today the installed library happens to be identical to
  upstream's; the pin is still what CI builds, so the local switch should
  match it.) Named rather than a local `_opam`, because the repo is worked in
  through several git worktrees that would each get their own copy. The name
  is yours to choose; this document, and `build.sh`'s error hint, write it
  `cert-yjs`:

      opam switch create cert-yjs ocaml-base-compiler.5.2.0 --no-install --no-switch
      opam install ./cert-yjs.opam --deps-only --switch=cert-yjs

  Then either make it current (`opam switch set cert-yjs`) or run the build
  through it:

      opam exec --switch=cert-yjs -- ./build.sh

  That is the whole setup: goose comes out of the switch too (see the goose
  note above), so there is no second perennial checkout to keep in step.
