package yjs

// In-memory update application (y-octo: doc/document.rs Doc::apply_update +
// doc/codec/update.rs Update). This is the *verified core* of apply_update: given
// an already-decoded update whose insert structs are in causal order, integrate
// each one with the proven store.Integrate. It is goose-translated and the proof
// (wp_store__applyUpdate in src/proof/yjs_store.v) shows it preserves the document
// invariant and refines a fold of the pure model's integrate.
//
// The byte-level v1 decode (Update::read), the state-vector + pending/missing
// causal-order iterator (codec/update.rs UpdateIterator), the delete set
// (store::delete_range), GC/Skip nodes, Parent::Id / parent_sub and multi-clock
// runs are all out of the verified subset; the unverified runtime path for those
// stays in codec.go (//go:build !goose). See docs and CLAUDE.md.
//
// The public locking entry (y-octo: Doc::apply_update takes the store write lock)
// is deferred: a thin lock+call wrapper adds no verification value over the lock
// discipline already proved for Insert/Delete, and its honest public spec belongs
// in the order-independent / ghost-global-history restatement tracked in issue #40.

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

// applyUpdate integrates the decoded structs in list order: each struct is
// repaired (origins and parent resolved against the store) and then integrated
// with the proven store.Integrate. This is the integrate loop of y-octo's
// Doc::apply_update (document.rs): there the UpdateIterator yields structs in
// causal order and store.repair + store.integrate(s, offset, None) splice each
// one in; here the caller supplies that causal order directly. The update is a
// doc-level batch: the target type of each struct is per-item data, not a
// parameter (issue #49). Callers hold s.mu.
func (s *store) applyUpdate(structs []updateItem) {
	for i := 0; i < len(structs); i++ {
		ui := structs[i]
		it := newItem(ui.id, ui.content, ui.originLeftId, ui.originRightId)
		s.repair(it, ui.parentName)
		s.Integrate(nil, it)
	}
}
