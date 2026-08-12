package yjs

// Decoded, in-memory update of the verified subset (y-octo: doc/codec/update.rs
// Update + codec/item.rs Item): the Update batch and its updateItem structs.
// The application loop itself lives in store.applyUpdate (store.go) -- the
// *verified core* of apply_update, proved by wp_store__applyUpdate in
// src/proof/store/store.v. Since issue #40 that loop is TOTAL: the batch needs
// no ordering or causal closure, and structs whose dependencies (origins /
// own predecessor) have not arrived are buffered in store.pending and drained
// by later calls, mirroring y-octo's UpdateIterator + DocStore.pending.
//
// The byte-level v1 decode (Update::read), the delete set
// (store::delete_range), GC/Skip nodes, Parent::Id / parent_sub and
// multi-clock runs remain out of the verified subset; the unverified runtime
// path for those stays in codec.go (//go:build !goose), whose Doc.ApplyUpdate
// is the thin decode wrapper routing through the locked Doc.applyUpdate
// (doc.go).

// updateItem is one decoded insert struct in the verified subset: an item carrying
// its id, both sibling origins, its parent info and its single-char string content
// (y-octo: codec/item.rs Item, as stored in codec/update.rs Update.structs). The
// Phase-2 simplification fixes the content to a 1-char string and drops
// Parent::Id / parent_sub (root types only, #43).
type updateItem struct {
	id            id
	originLeftId  *id
	originRightId *id
	// parentName is the decoded parent (y-octo: Item.parent): non-nil is
	// Parent::String, the name of the root type the item targets; nil is
	// Parent::None, meaning store.repair borrows the parent from the item's
	// resolved left/right neighbour (the wire format only carries a parent for
	// structs with no sibling origins).
	parentName *string
	content    string
}

// deleteSpan is one decoded delete range: the half-open clock interval
// [clock, clock+length) of client's per-client clock space (y-octo: the
// per-client OrderRange of codec/update.rs Update.delete_set, which drives
// DocStore::delete_range). A delete carries no id and consumes no clock, which
// is why the model treats the delete set as state, not as an operation
// (docs/plan-delete-set.md).
type deleteSpan struct {
	client Client
	clock  uint64
	length uint64
}

// Update is the decoded, in-memory update of the verified subset: a batch of
// insert structs in ARBITRARY order, with no causal-closure requirement, plus
// the delete spans that tombstone already-integrated chars (y-octo:
// codec/update.rs Update.structs + Update.delete_set). Each struct carries its
// own parent info, so one update may touch several root types (issue #49).
// Structs whose dependencies are missing are buffered by store.applyUpdate in
// store.pending, and spans whose targets have not arrived are buffered in
// store.pendingDeletes by store.applyDeleteSpans (issue #40 discipline,
// issue #133); y-octo's in-update pending_structs / missing_state staging
// fields are out of the verified subset.
type Update struct {
	structs []updateItem
	deletes []deleteSpan
}
