//go:build !goose

package yjs

// Document-level API: the user-facing Doc and Text handle.
//
// This mirrors y-octo's doc/document.rs (Doc, get_or_create_text) and
// doc/types/text.rs + doc/types/list (insert_at / remove_at). It is the runtime
// API layer and is excluded from goose translation (`//go:build !goose`); only
// the integrate core in store.go is the proof surface.
//
// Simplifications vs y-octo:
//   - a Doc owns root Text types by name (no nested types, no maps/arrays);
//   - every user-visible character becomes its own 1-char internal item, so
//     positions never fall inside an item and no splitting is needed;
//   - content is assumed single-byte (ASCII): a clock unit is one byte, which
//     keeps id arithmetic consistent with content.Len (byte length).

// Doc is a document: a struct store plus the root text types it owns.
type Doc struct {
	store *store
	// types is the root-type registry by name (y-octo: DocStore types).
	types map[string]*yText
}

// NewDoc creates a document with a fresh store owned by client.
func NewDoc(client Client) *Doc {
	return &Doc{
		store: newStore(client),
		types: make(map[string]*yText),
	}
}

// getOrCreateYText returns the internal sequence for name, creating it on first
// use (y-octo: DocStore::get_or_create_type).
func (d *Doc) getOrCreateYText(name string) *yText {
	y, ok := d.types[name]
	if !ok {
		y = newYText()
		d.types[name] = y
	}
	return y
}

// GetText returns the root text type named name, creating it on first use
// (y-octo: Doc::get_or_create_text).
func (d *Doc) GetText(name string) *Text {
	return &Text{doc: d, name: name, inner: d.getOrCreateYText(name)}
}

// Text is the public handle for a root text type (y-octo: the Text wrapper
// around a YTypeRef). It carries the owning Doc so edits can allocate ids from
// the store and register the resulting items.
type Text struct {
	doc   *Doc
	name  string
	inner *yText
}

// String returns the current visible text.
func (t *Text) String() string { return t.inner.Text() }

// Len returns the visible (countable, non-deleted) length.
func (t *Text) Len() uint64 { return t.inner.len }

// Insert inserts content at the visible character index, generating one
// 1-char item per byte. Each item's left origin chains to the previous one and
// every item shares the same right origin, matching how Yjs splits a run
// (y-octo: ListType::insert_after via store::create_item + integrate).
func (t *Text) Insert(index uint64, content string) {
	if index > t.inner.len {
		return
	}
	left, right := t.inner.findPos(index)
	client := t.doc.store.client

	for i := 0; i < len(content); i++ {
		clock := t.doc.store.getState(client)

		var originLeftId *id
		var originRightId *id
		if left != nil {
			lid := left.LastId()
			originLeftId = &lid
		}
		if right != nil {
			rid := right.id
			originRightId = &rid
		}

		item := newItem(newId(client, clock), content[i:i+1], originLeftId, originRightId)
		t.doc.store.Integrate(t.inner, item)
		t.doc.store.AddNode(itemNode{item: *item})

		// the next character integrates immediately to the right of this one.
		left = item
	}
}

// Delete tombstones length visible characters starting at index, recording the
// deletion in the store's delete set (y-octo: ListType::remove_after via
// store::delete_item).
func (t *Text) Delete(index uint64, length uint64) {
	_, right := t.inner.findPos(index)
	remaining := length
	cur := right
	for remaining > 0 && cur != nil {
		if cur.Indexable() {
			cur.flags = cur.flags | itemDeleted
			t.inner.len = t.inner.len - cur.Len()
			t.doc.store.deletedSet.addRange(cur.id, cur.Len())
			remaining = remaining - cur.Len()
		}
		cur = cur.right
	}
}

// getState returns the next clock for client: the end clock of its last
// recorded struct, or 0 (y-octo: DocStore::get_state).
func (s *store) getState(client Client) Clock {
	nodes, ok := s.items[client]
	if !ok {
		return 0
	}
	n := len(nodes)
	if n == 0 {
		return 0
	}
	last := nodes[n-1]
	return last.clock() + last.length()
}

// findPos walks to the visible character index and returns the doubly-linked
// neighbours (left, right) straddling that position (y-octo: ListType::find_pos
// specialised to 1-char items, so the offset/normalize/split path is gone).
func (y *yText) findPos(index uint64) (*item, *item) {
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

// addRange records [id.clock, id.clock+length) as deleted for id's client
// (y-octo: DeleteSet::add_range, without the adjacency merging).
func (d *deletedSet) addRange(id id, length uint64) {
	r := span[uint64]{start: id.clock, end: id.clock + length}
	existing, ok := d.deletedSet[id.clientId]
	if !ok {
		d.deletedSet[id.clientId] = fragmentOrderRange{fragment: []span[uint64]{r}}
		return
	}
	if frag, isFrag := existing.(fragmentOrderRange); isFrag {
		frag.fragment = append(frag.fragment, r)
		d.deletedSet[id.clientId] = frag
		return
	}
	if rr, isRange := existing.(rangeOrderRange); isRange {
		d.deletedSet[id.clientId] = fragmentOrderRange{fragment: []span[uint64]{rr.range_, r}}
	}
}
