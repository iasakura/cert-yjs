package yjs

// Text-type API (y-octo: doc/types/text.rs); the Doc handle lives in doc.go and
// the inner lock-guarded sequence type [yType] in ytype.go.
//
// These ops are goose-translated (part of the verified model): Insert is a loop
// over the proven store.Integrate and Delete tombstones a visible run, so both
// preserve the document invariant is_ytype (see wp_Text__Insert / wp_Text__Delete
// in src/proof/text/text.v). The byte-level v1 codec and the delete-set cache stay
// behind //go:build !goose (codec.go, delete.go).
//
// Simplifications vs y-octo:
//   - the store owns the root types by name (no nested types, no maps/arrays);
//   - the local client's next clock lives in the store (state-vector head); an
//     edit takes the store lock, integrates, and registers the new item into the
//     store's item set -- faithful to y-octo's Arc<RwLock<DocStore>>;
//   - content is assumed single-byte (ASCII): a clock unit is one byte, which
//     keeps id arithmetic consistent with content.Len (byte length).

// Text is the public handle for a root text type (y-octo: Text is a YTypeRef
// newtype). It carries the store (for the lock / client / clock) and the inner
// YType it edits; the type name is only needed at GetText time, so it is not
// stored in the handle.
type Text struct {
	store *store
	inner *yType
}

// String returns the current visible text. A pure read: takes the read lock
// (RLock) so it runs concurrently with other readers (y-octo reads the type
// under the RwLock read guard).
func (t *Text) String() string {
	s := t.store
	s.mu.RLock()
	r := t.inner.Text()
	s.mu.RUnlock()
	return r
}

// Len returns the visible (countable, non-deleted) length. A pure read: takes
// the read lock (RLock) so it runs concurrently with other readers.
func (t *Text) Len() uint64 {
	s := t.store
	s.mu.RLock()
	n := t.inner.len
	s.mu.RUnlock()
	return n
}

// Insert inserts content at the visible character index, generating one
// 1-char item per byte. Each item's left origin chains to the previous one and
// every item shares the same right origin, matching how Yjs splits a run
// (y-octo: ListType::insert_after via store::create_item + integrate). The whole
// edit runs under the store lock; each character's id comes from the store's
// local clock counter.
func (t *Text) Insert(index uint64, content string) {
	s := t.store
	s.mu.Lock()
	if index > t.inner.len {
		s.mu.Unlock()
		return
	}
	// Guard against clock overflow: if integrating this run would wrap the
	// per-client clock counter (s.clock + len(content) overflowing uint64),
	// refuse the edit and leave the document unchanged. Unreachable in
	// practice (2^64 edits); needed so the store's monotone clock invariant
	// survives the insert without an externally supplied bound on s.clock.
	if s.clock+uint64(len(content)) < s.clock {
		s.mu.Unlock()
		return
	}
	// Normalize the position (y-octo: ItemPosition::normalize): when the
	// index lands inside a multi-element run, split [left] at the offset so
	// the insertion point sits on a node boundary. With 1-char items the
	// offset is always 0 and the split is dead code (issue #28; reachable
	// once multi-element updates land, M4).
	left, right, offset := t.inner.findPos(index)
	if offset > 0 {
		left, right = s.splitNode(left, offset)
	}
	client := s.client

	// Every character in this run shares the same right origin: the node that
	// was to the right of the insertion point (y-octo chains a run between one
	// fixed left/right pair). [right] never moves in the loop, so read it once.
	var originRightId *id
	if right != nil {
		rid := right.id
		originRightId = &rid
	}

	for i := 0; i < len(content); i++ {
		clk := s.clock
		s.clock = clk + 1

		var originLeftId *id
		if left != nil {
			lid := left.LastId()
			originLeftId = &lid
		}

		// The local item is created already linked to its neighbours and
		// carrying its parent (y-octo: store::create_item receives pos.left /
		// pos.right / Some(Parent::Type)); the update path resolves the same
		// fields with store.repair instead.
		newit := newItem(newId(client, clk), string(content[i]), originLeftId, originRightId)
		newit.left = left
		newit.right = right
		newit.parent = t.inner
		s.Integrate(t.inner, newit)

		// the next character integrates immediately to the right of this one.
		left = newit
	}
	s.mu.Unlock()
}

// Delete tombstones length visible characters starting at the visible index,
// marking each item deleted and shrinking the visible length (y-octo:
// ListType::remove_after via store::delete_item, splitting at both range
// boundaries when they land inside a run). Tombstoning keeps the items in the list and the
// document order, so it preserves the integrate invariant -- only visibility
// changes. The whole edit runs under the store lock.
//
// The Deleted flag is the source of truth for visibility; the store's DeleteSet
// (a serialization cache, y-octo derives it from the flags in generate_delete_set)
// is regenerated at encode time (codec.go: generateDeleteSet), so Delete only
// flips flags and shrinks the visible length.
func (t *Text) Delete(index uint64, length uint64) {
	s := t.store
	s.mu.Lock()
	// Normalize the range start (split [left] when the index lands inside a
	// run), then tombstone forward, splitting once more when the budget ends
	// inside a run (y-octo: ListType::remove_after; both splits are dead code
	// while every item is 1-char, issue #28).
	left, right, offset := t.inner.findPos(index)
	if offset > 0 {
		_, r2 := s.splitNode(left, offset)
		right = r2
	}
	remaining := length
	cur := right
	for remaining > 0 && cur != nil {
		if cur.Indexable() {
			if remaining < cur.Len() {
				// Split at the range end: [cur] is truncated in place to
				// exactly the remaining budget (the in-place left half),
				// so the tombstone below covers precisely the range.
				s.splitNode(cur, remaining)
			}
			cur.flags = cur.flags | itemDeleted
			t.inner.len = t.inner.len - cur.Len()
			remaining = remaining - cur.Len()
		}
		cur = cur.right
	}
	s.mu.Unlock()
}
