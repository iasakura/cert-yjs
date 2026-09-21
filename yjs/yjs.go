// Package yjs is a Yjs-style CRDT implementation in Go, intended to be
// translated to Rocq with goose and verified with Perennial.
//
// The package is written after three implementations of the Yjs CRDT: Yjs
// (https://github.com/yjs/yjs), yrs (https://github.com/y-crdt/y-crdt) and
// y-octo (https://github.com/y-crdt/y-octo). The data structures and the
// integrate algorithm are a port of y-octo (the Toeverything / AFFiNE team)
// and the text observer follows Yjs's YTextEvent.delta, both used here under
// the MIT License; see the NOTICE file at the repository root. Where the three
// implementations differ, the code comment at the divergence says which one is
// followed and why.
//
// The package is split into files that mirror y-octo's module layout:
//
//	id.go        id / Client / Clock        (y-octo: codec/id.rs)
//	content.go   content                    (y-octo: codec/content.rs)
//	item.go      item + flag bits           (y-octo: codec/item.rs, item_flag.rs)
//	range.go     orderRange / deletedSet    (y-octo: common/range.rs, codec/delete_set.rs)
//	store.go     store + Integrate          (y-octo: doc/store.rs DocStore)
//	ytype.go     yType (lock-guarded inner) (y-octo: doc/types YType)
//	text.go      Text API (unlocked handle) (y-octo: doc/types/text.rs)
//	observe.go   TextObserver / ApplyDelta  (Yjs: src/utils/YEvent.js delta)
//	doc.go       Doc handle + GetOrCreateText       (y-octo: doc/document.rs)
//	transaction.go Transaction + Doc.Transact  (Yjs: src/utils/Transaction.js; y-octo has none)
//	refs.go      node / GC / Skip tombstones (y-octo: codec/refs.rs)     [not translated]
//	delete.go    Delete                     (y-octo: doc/types/text.rs)  [not translated]
//	codec.go     v1 update encode/decode    (y-octo: codec/{update,...}) [not translated]
//
// refs.go, delete.go and codec.go carry the `//go:build !goose` constraint: the
// node enum is used only by the byte-level v1 codec, and Delete / the codec are
// the runtime interop layer -- all excluded from goose translation so the
// verified core (store.go's Integrate, text.go's Insert) stays the proof
// surface. Normal `go build` / `go test` compile every file.
package yjs
