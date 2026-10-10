package yjs

// Document-level API (y-octo: doc/document.rs).
//
// A Doc is just a handle around the struct store; it owns nothing itself beyond
// the store pointer (the store is y-octo's Arc<RwLock<DocStore>>). Goose-translated
// like store.go / text.go.

// Doc is a document: a handle around the lock-guarded struct store
// (y-octo: Doc wraps an Arc<RwLock<DocStore>>, our storeRef). The store
// owns the types, clock and items; the ref owns the lock.
type Doc struct {
	store *storeRef
}

// NewDoc creates a document with a fresh store owned by client.
func NewDoc(client Client) *Doc {
	return &Doc{store: newStoreRef(client)}
}

// GetOrCreateText returns the root text type named name, creating it on first use
// (y-octo: Doc::get_or_create_text). Registering the type mutates the store, so
// it is done under the store lock.
func (d *Doc) GetOrCreateText(name string) *Text {
	ref := d.store
	ref.wlock()
	inner := ref.store.getOrCreateYType(name)
	ref.wunlock()
	return &Text{store: ref, inner: inner}
}

// Transact runs f as one transaction on the document (Yjs doc.transact,
// src/utils/Doc.js:179; yrs Doc::transact_mut): every write inside is one
// unit, and the observers of the types it changed are called once at its end.
// f must not lock the document again (no Transact, Insert, Delete,
// ApplySyncUpdate, String or Len on the same document: deadlock, #206 item
// 2); it uses the In-variants with tr.
func (d *Doc) Transact(f func(tr *Transaction)) {
	transact(d.store, f)
}

// applyUpdate integrates a decoded update batch as one transaction (y-octo:
// Doc::apply_update takes store.write() for the whole apply; Yjs applyUpdate
// runs inside transact). The verified core is Transaction.applyUpdate, which
// is total: structs whose dependencies have not arrived are buffered in the
// store and drained by later calls. The codec-level Doc.ApplyUpdate
// (codec.go) decodes the wire format and routes the batch through here.
func (d *Doc) applyUpdate(structs []updateItem) {
	transact(d.store, func(tr *Transaction) {
		tr.applyUpdate(structs)
	})
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
