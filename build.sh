#!/usr/bin/env bash
# Build pipeline: write Go -> translate to Rocq with goose -> check proofs.
#
# Usage:
#   ./build.sh          # everything (go build -> goose -> make)
#   ./build.sh go       # Go build (type check) only
#   ./build.sh goose    # goose translation (also runs go build)
#   ./build.sh make     # proof check only (vos/vok, parallel), translation assumed done
#   ./build.sh vo       # plain .vo full build (serial-ish; only if you need .vo files)
#
# Tuning:
#   JOBS=8 ./build.sh make      # cap parallelism (default: nproc)
#
# Why these steps exist:
#  - perennial requires go 1.26, so GOTOOLCHAIN is forced.
#  - goose/proofgen are not registered as tools in go.mod, so make's automatic
#    goose step does not work; we call the goose bundled with the perennial
#    source via --local.
#  - .goose-output is touched to tell make the translation is up to date.
#  - proofgen sometimes emits a bogus src/generatedproof/_ directory; clean it.
set -euo pipefail

# --- configuration (adjust per machine via env) ---
export GOTOOLCHAIN=go1.26.0
# goose comes from the perennial that opam actually installed into the current
# switch, so it cannot drift from the pin in cert-yjs.opam: that directory IS
# the pinned source. (opam keeps it for pinned dev packages.) A separate
# checkout kept at the same commit by hand is the alternative, and getting it
# wrong is silent: goose without the ffiMapping entry emits a package with no
# ffi prelude, which only fails much later as UNDEFINED EVARS in the generated
# Assumptions class. Hence check_goose below.
PERENNIAL="${PERENNIAL:-${OPAM_SWITCH_PREFIX:-}/.opam-switch/sources/perennial}"
GOOSE_SRC="$PERENNIAL/goose"
JOBS="${JOBS:-$(nproc 2>/dev/null || echo 4)}"

cd "$(dirname "$0")"

step="${1:-all}"

# Packages whose translation depends on an ffiMapping entry in goose. Without
# the entry goose still succeeds and produces unusable output, so refuse to run
# rather than translate against the wrong goose.
FFI_MAPPED_PKGS="grovenet wsnet"

check_goose() {
  if [ ! -d "$GOOSE_SRC" ]; then
    echo "error: no goose source at $GOOSE_SRC" >&2
    if [ -z "${OPAM_SWITCH_PREFIX:-}" ]; then
      echo "  OPAM_SWITCH_PREFIX is unset: run through opam, e.g." >&2
      echo "    opam exec --switch=cert-yjs -- ./build.sh" >&2
    else
      echo "  the current switch has no pinned perennial source; check that" >&2
      echo "  perennial is installed from the pin in cert-yjs.opam, or point" >&2
      echo "  PERENNIAL= at a perennial checkout at that commit." >&2
    fi
    exit 1
  fi
  local missing=""
  for pkg in $FFI_MAPPED_PKGS; do
    grep -qF "github.com/iasakura/cert-yjs/$pkg" "$GOOSE_SRC/util/util.go" ||
      missing="$missing $pkg"
  done
  if [ -n "$missing" ]; then
    echo "error: goose at $GOOSE_SRC has no ffiMapping entry for:$missing" >&2
    echo "  cert-yjs needs the iasakura/perennial fork (upstream plus those" >&2
    echo "  entries); this goose would translate the package with no ffi" >&2
    echo "  prelude and the generated Assumptions class would not typecheck." >&2
    exit 1
  fi
}

do_go() {
  echo ">>> go build (type check)"
  go build ./...
  echo "    OK"
}

do_goose() {
  check_goose
  echo ">>> goose translation (Go -> Rocq, using perennial's bundled goose via --local)"
  echo "    goose source: $GOOSE_SRC"
  go tool perennial-cli goose --local "$GOOSE_SRC"
  rm -rf src/generatedproof/_   # clean up proofgen artifacts
  echo "    OK -> updated src/code/... and src/generatedproof/..."
}

# Proof check via Rocq's vos/vok split, which parallelizes the slow part.
#   vos: elaborate every file and emit its interface, skipping opaque (Qed)
#        proof bodies. This is the only phase that must follow the dependency
#        chain, but each file is cheap because the hard proofs are skipped
#        (the whole vos pass is ~30s here).
#   vok: check the opaque proof bodies that vos skipped. Each file's .vok needs
#        only the .vos interfaces, so all of them run fully in parallel across
#        cores instead of one at a time down the store -> text chain.
# vos + vok together give exactly the same assurance as a plain `.vo` build: a
# broken Qed is rejected in the vok phase (verified). set -e makes a vok failure
# abort the script, so this stays a real, strict proof check.
do_make() {
  echo ">>> make (proof check via vos/vok, -j$JOBS)"
  touch .goose-output          # tell make the translation is done
  make -j"$JOBS" vos           # interfaces: fast, dependency-ordered
  make -j"$JOBS" vok           # opaque proofs: full check, embarrassingly parallel
  echo "    OK -> all proofs checked (vos + vok)"
}

# Plain .vo build. Kept as an escape hatch for when actual .vo artifacts are
# needed (downstream Require, debugging a vok-only anomaly). Note: the .vo
# dependency graph is essentially serial through the store chain, so -j barely
# helps here; prefer `make` (vos/vok) for a fast full check.
do_makevo() {
  echo ">>> make (.vo full build, -j$JOBS)"
  touch .goose-output
  make -j"$JOBS"
  echo "    OK -> all .vo built"
}

case "$step" in
  go)    do_go ;;
  goose) do_go; do_goose ;;
  make)  do_make ;;
  vo)    do_makevo ;;
  all)   do_go; do_goose; do_make ;;
  *) echo "usage: ./build.sh [go|goose|make|vo|all]"; exit 1 ;;
esac

echo "=== done ($step) ==="
