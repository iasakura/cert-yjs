package yjs

// Decoded, in-memory update of the verified subset (y-octo: doc/codec/update.rs
// Update + codec/item.rs Item): the Update batch and its updateItem structs.
// The application loop itself lives in store.applyUpdate (store.go) -- the
// *verified core* of apply_update, proved by wp_store__applyUpdate in
// src/proof/yjs_store.v.
//
// The byte-level v1 decode (Update::read), the state-vector + pending/missing
// causal-order iterator (UpdateIterator), the delete set (store::delete_range),
// GC/Skip nodes, Parent::Id / parent_sub and multi-clock runs are all out of the
// verified subset; the unverified runtime path for those stays in codec.go
// (//go:build !goose), whose Doc.ApplyUpdate is the thin decode+lock+call
// wrapper over store.applyUpdate. Its honest verified public spec is tracked in
// issue #40.

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

// Update is the decoded, in-memory update of the verified subset: a batch of
// insert structs in causal order -- every struct's origins occur earlier in the
// list, and each client's structs are clock-ascending (y-octo: codec/update.rs
// Update, restricted to its structs field). Each struct carries its own parent
// info, so one update may touch several root types (issue #49). The
// pending_structs / missing_state / pending_delete_set fields that drive
// UpdateIterator's retry machinery, and delete_set which drives delete_range, are
// out of the verified subset.
type Update struct {
	structs []updateItem
}
