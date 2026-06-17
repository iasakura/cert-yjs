// Package yjs is a Yjs-style CRDT implementation in Go, intended to be
// translated to Rocq with goose and verified with Perennial.
//
// The data structures and the integrate algorithm are a port of y-octo
// (https://github.com/y-crdt/y-octo), the Rust Yjs implementation by the
// Toeverything / AFFiNE team, used here under the MIT License. See the NOTICE
// file at the repository root for the full y-octo copyright and license.
//
// The package is split into files that mirror y-octo's module layout:
//
//	id.go        Id / Client / Clock        (y-octo: codec/id.rs)
//	content.go   Content                    (y-octo: codec/content.rs)
//	item.go      Item + flag bits           (y-octo: codec/item.rs, item_flag.rs)
//	refs.go      Node / GC / Skip / Item    (y-octo: codec/refs.rs)
//	range.go     OrderRange / DeletedSet    (y-octo: common/range.rs, codec/delete_set.rs)
//	store.go     Store + Integrate          (y-octo: doc/store.rs)
//	ytext.go     YText (internal sequence)  (y-octo: doc/types/text.rs)
//	document.go  Doc + Text handle + API    (y-octo: doc/document.rs)   [not translated]
//	codec.go     v1 update encode/decode    (y-octo: codec/{update,...}) [not translated]
//
// document.go and codec.go carry the `//go:build !goose` constraint: they are
// the runtime API / interop layer (byte-level codec, string manipulation),
// excluded from goose translation so the verified core (store.go's Integrate)
// stays the proof surface. Normal `go build` / `go test` compile every file.
package yjs
