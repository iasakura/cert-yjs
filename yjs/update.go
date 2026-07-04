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
// its id, both sibling origins, and its single-char string content (y-octo:
// codec/item.rs Item, as stored in codec/update.rs Update.structs). The Phase-2
// simplification fixes the content to a 1-char string and drops Parent::Id /
// parent_sub (the struct's parent is the root text it is applied to).
type updateItem struct {
	id            id
	originLeftId  *id
	originRightId *id
	content       string
}

// Update is the decoded, in-memory update of the verified subset: a batch of
// insert structs in causal order -- every struct's origins occur earlier in the
// list, and each client's structs are clock-ascending -- all targeting one root
// text (y-octo: codec/update.rs Update, restricted to its structs field). The
// pending_structs / missing_state / pending_delete_set fields that drive
// UpdateIterator's retry machinery, and delete_set which drives delete_range, are
// out of the verified subset.
type Update struct {
	structs []updateItem
}

// applyUpdate integrates the decoded structs into parent in list order, reusing
// store.Integrate for each. This is the integrate loop of y-octo's
// Doc::apply_update (document.rs): there the UpdateIterator yields structs in
// causal order and store.integrate splices each one in; here the caller supplies
// that causal order directly. Callers hold s.mu.
func (s *store) applyUpdate(parent *yType, structs []updateItem) {
	for i := 0; i < len(structs); i++ {
		ui := structs[i]
		it := newItem(ui.id, ui.content, ui.originLeftId, ui.originRightId)
		s.Integrate(parent, it)
	}
}
