#!/usr/bin/env bash
# Build pipeline: write Go -> translate to Rocq with goose -> check proofs.
#
# Usage:
#   ./build.sh          # everything (go build -> goose -> make)
#   ./build.sh go       # Go build (type check) only
#   ./build.sh goose    # goose translation (also runs go build)
#   ./build.sh make     # make (proof check) only, assuming translation is done
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

do_make() {
  echo ">>> make (compile .v to .vo = type check + proof check)"
  touch .goose-output          # tell make the translation is done
  make
  echo "    OK -> all .vo built"
}

case "$step" in
  go)    do_go ;;
  goose) do_go; do_goose ;;
  make)  do_make ;;
  all)   do_go; do_goose; do_make ;;
  *) echo "usage: ./build.sh [go|goose|make|all]"; exit 1 ;;
esac

echo "=== done ($step) ==="
