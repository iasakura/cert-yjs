#!/usr/bin/env bash
# Build the wasm module and copy Go's wasm loader next to it. The loader must
# come from the toolchain that compiled the module, hence the copy.
set -euo pipefail
cd "$(dirname "$0")"

GOOS=js GOARCH=wasm go build -o cert-yjs.wasm .
# install, not cp: the toolchain copy is read-only, and so would a copy of it be.
install -m 644 "$(go env GOROOT)/lib/wasm/wasm_exec.js" wasm_exec.js
echo "built $(du -h cert-yjs.wasm | cut -f1) cert-yjs.wasm"
