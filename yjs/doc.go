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

// GetOrCreateText returns the root text type named name, creating it on first use
// (y-octo: Doc::get_or_create_text). Registering the type mutates the store, so
// it is done under the store lock.
func (d *Doc) GetOrCreateText(name string) *Text {
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

// Codec is the decoding half of the update codec: data decodes to a batch of
// insert structs, ok reports whether it decoded at all. The struct type is
// unexported, so a Codec can only be built inside this package; the
// deployment's is WireCodec (codec.go). The byte codec stays outside the
// verified core (codec.go, //go:build !goose), so verified code takes it as a
// VALUE, and the server's proofs assume only its specification (codec_spec,
// src/proof/yjs_prot.v) against the abstract decode the wire protocol
// [yjs_prot] is defined over; the real codec is trusted to meet it, the same
// trust boundary codec.go already is.
type Codec = func(data []byte) (ok bool, structs []updateItem, deletes []deleteSpan)

// ApplyEncodedUpdate decodes one wire update with decode and applies the
// batch with the verified total apply path (ApplySyncUpdate, under the
// store's write lock). It reports whether the update decoded; an applied
// update is one the caller may relay (y-websocket relays exactly what it
// applied).
func (d *Doc) ApplyEncodedUpdate(decode Codec, data []byte) bool {
	ok, structs, deletes := decode(data)
	if !ok {
		return false
	}
	d.ApplySyncUpdate(structs, deletes)
	return true
}
