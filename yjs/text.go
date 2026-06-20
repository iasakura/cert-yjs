package yjs

// Document- and text-level API (y-octo: doc/document.rs + doc/types/text.rs).
//
// These ops are goose-translated (part of the verified model): Insert is a loop
// over the proven store.Integrate, so it preserves the document invariant
// is_valid_ytext (see wp_Text__Insert in src/proof/yjs_invariant.v). Delete and
// the byte-level v1 codec stay behind //go:build !goose (delete.go, codec.go).
//
// Simplifications vs y-octo:
//   - a Doc owns root Text types by name (no nested types, no maps/arrays);
//   - the next clock for the local client is a plain Doc counter (clock) rather
//     than derived from the struct store's state vector -- this keeps Insert
//     decoupled from store.items, so verifying it needs only is_valid_ytext and
//     the counter, not ownership of the interface-typed node-slice map;
//   - every user-visible character becomes its own 1-char internal item, so
//     positions never fall inside an item and no splitting is needed;
//   - content is assumed single-byte (ASCII): a clock unit is one byte, which
//     keeps id arithmetic consistent with content.Len (byte length).

// Doc is a document: a struct store plus the root text types it owns.
type Doc struct {
	store *store
	// types is the root-type registry by name (y-octo: DocStore types).
	types map[string]*yText
	// clock is the next clock for the local client (store.client). Each local
	// insert consumes one and bumps it; this makes generated ids maximal.
	clock Clock
}

// NewDoc creates a document with a fresh store owned by client.
func NewDoc(client Client) *Doc {
	return &Doc{
		store: newStore(client),
		types: make(map[string]*yText),
		clock: 0,
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
// the doc's clock counter and integrate the resulting items.
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
// (y-octo: ListType::insert_after via store::create_item + integrate). The id of
// each character comes from the doc's local clock counter.
func (t *Text) Insert(index uint64, content string) {
	if index > t.inner.len {
		return
	}
	left, right := t.inner.findPos(index)
	client := t.doc.store.client

	for i := 0; i < len(content); i++ {
		clk := t.doc.clock
		t.doc.clock = clk + 1

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

		newit := newItem(newId(client, clk), string(content[i]), originLeftId, originRightId)
		t.doc.store.Integrate(t.inner, newit)

		// the next character integrates immediately to the right of this one.
		left = newit
	}
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
