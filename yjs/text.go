package yjs

// Text-type API (y-octo: doc/types/text.rs); the Doc handle lives in doc.go.
//
// These ops are goose-translated (part of the verified model): Insert is a loop
// over the proven store.Integrate, so it preserves the document invariant
// is_valid_ytext (see wp_Text__Insert in src/proof/yjs_text.v). Delete and
// the byte-level v1 codec stay behind //go:build !goose (delete.go, codec.go).
//
// Simplifications vs y-octo:
//   - the store owns the root types by name (no nested types, no maps/arrays);
//   - the local client's next clock lives in the store (state-vector head); an
//     edit takes the store lock, integrates, and registers the new item into the
//     store's item set -- faithful to y-octo's Arc<RwLock<DocStore>>;
//   - every user-visible character becomes its own 1-char internal item, so
//     positions never fall inside an item and no splitting is needed;
//   - content is assumed single-byte (ASCII): a clock unit is one byte, which
//     keeps id arithmetic consistent with content.Len (byte length).

// yType is the root sequence type the items are integrated into (y-octo: YType
// in doc/types). The Phase-1 simplification fixes the content to a single string
// type with no parent_sub, so we only need the head of the item linked list and
// the visible length.
type yType struct {
	// start is the head of the doubly linked list of items (parent.start).
	start *item
	// len is the visible (countable, non-deleted) length.
	len uint64
}

// newYType creates an empty root sequence.
func newYType() *yType {
	return &yType{start: nil, len: 0}
}

// Text is the public handle for a root text type (y-octo: the Text wrapper
// around a YTypeRef, which holds the store ref). It carries the store directly so
// edits reach the lock / client / clock and integrate the resulting items, with
// no Doc indirection.
type Text struct {
	store *store
	name  string
	inner *yType
}

// String returns the current visible text. Reads the shared DLL under the lock.
func (t *Text) String() string {
	s := t.store
	s.mu.Lock()
	r := t.inner.Text()
	s.mu.Unlock()
	return r
}

// Len returns the visible (countable, non-deleted) length, read under the lock.
func (t *Text) Len() uint64 {
	s := t.store
	s.mu.Lock()
	n := t.inner.len
	s.mu.Unlock()
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
	left, right := t.inner.findPos(index)
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

		newit := newItem(newId(client, clk), string(content[i]), originLeftId, originRightId)
		s.Integrate(t.inner, newit)

		// the next character integrates immediately to the right of this one.
		left = newit
	}
	s.mu.Unlock()
}

// findPos walks to the visible character index and returns the doubly-linked
// neighbours (left, right) straddling that position (y-octo: ListType::find_pos
// specialised to 1-char items, so the offset/normalize/split path is gone).
func (y *yType) findPos(index uint64) (*item, *item) {
	var left *item
	right := y.start

	// avoid the first item being a deleted one
	for right != nil && right.Deleted() {
		right = right.right
	}

	remaining := index
	for remaining > 0 && right != nil {
		if right.Indexable() {
			remaining = remaining - right.Len()
		}
		left = right
		right = right.right
	}
	return left, right
}

// Text reads the current visible string by walking the item list left to right
// (skipping deleted items). Useful for stating/verifying convergence.
func (parent *yType) Text() string {
	result := ""
	cur := parent.start
	for cur != nil {
		if !cur.Deleted() {
			result = result + cur.content.content
		}
		cur = cur.right
	}
	return result
}
