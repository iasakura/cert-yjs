package yjs

// Document-level API (y-octo: doc/document.rs).
//
// A Doc is just a handle around the struct store; it owns nothing itself beyond
// the store pointer (the store is y-octo's Arc<RwLock<DocStore>>). Goose-translated
// like store.go / text.go.

// Doc is a document: a handle around the struct store (y-octo: Doc wraps an
// Arc<RwLock<DocStore>>). The store owns the types, clock, items and lock.
type Doc struct {
	store *store
}

// NewDoc creates a document with a fresh store owned by client.
func NewDoc(client Client) *Doc {
	return &Doc{store: newStore(client)}
}

// GetText returns the root text type named name, creating it on first use
// (y-octo: Doc::get_or_create_text). Registering the type mutates the store, so
// it is done under the store lock.
func (d *Doc) GetText(name string) *Text {
	s := d.store
	s.mu.Lock()
	inner := s.getOrCreateYType(name)
	s.mu.Unlock()
	return &Text{store: s, inner: inner}
}

// applyUpdate integrates a decoded update batch under the store's write lock
// (y-octo: Doc::apply_update takes store.write() for the whole apply). The
// verified core is store.applyUpdate, which is total: structs whose
// dependencies have not arrived are buffered in the store and drained by
// later calls. The codec-level Doc.ApplyUpdate (codec.go) decodes the wire
// format and routes the batch through here.
func (d *Doc) applyUpdate(structs []updateItem) {
	s := d.store
	s.mu.Lock()
	s.applyUpdate(structs)
	s.mu.Unlock()
}
