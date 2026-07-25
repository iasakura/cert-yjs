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
#    checkout via --local (same version as the opam pin).
#  - .goose-output is touched to tell make the translation is up to date.
#  - proofgen sometimes emits a bogus src/generatedproof/_ directory; clean it.
set -euo pipefail

# --- configuration (adjust per machine via env) ---
export GOTOOLCHAIN=go1.26.0
PERENNIAL="${PERENNIAL:-/home/ia/ghq/github.com/mit-pdos/perennial}"
GOOSE_SRC="$PERENNIAL/goose"
JOBS="${JOBS:-$(nproc 2>/dev/null || echo 4)}"

cd "$(dirname "$0")"

step="${1:-all}"

do_go() {
  echo ">>> go build (type check)"
  go build ./...
  echo "    OK"
}

do_goose() {
  echo ">>> goose translation (Go -> Rocq, using perennial's bundled goose via --local)"
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
