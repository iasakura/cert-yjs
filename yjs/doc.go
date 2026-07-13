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

// applyUpdate integrates a decoded, causal-order batch of insert structs under
// the store lock: the locking public entry over the verified store.applyUpdate
// core (y-octo: Doc::apply_update, document.rs, whose whole update application
// runs inside store.write(), the RwLock write guard). The byte-level decode
// stays in the unverified codec rind (Doc.ApplyUpdate in codec.go), which
// routes each ready batch through this wrapper. Verified as
// wp_Doc__applyUpdate in src/proof/yjs_doc.v (issue #40).
func (d *Doc) applyUpdate(structs []updateItem) {
	s := d.store
	s.mu.Lock()
	s.applyUpdate(structs)
	s.mu.Unlock()
}
