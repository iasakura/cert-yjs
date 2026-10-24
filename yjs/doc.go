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
// ApplySyncUpdate, CodeUnits, String or Len on the same document: deadlock, #206 item
// 2); it uses the In-variants with tr.
func (d *Doc) Transact(f func(tr *Transaction)) {
	transact(d.store, f)
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
//
// It is the document's only byte-level entry point, and it takes the whole
// decode as a value, for the reason given at Codec above. In the three
// references the decode is the library's own. Yjs v14.0.0-rc.18
// applyUpdate(ydoc, update, transactionOrigin) decodes v1
// (src/utils/encoding.js:370); applyUpdateV2 takes an optional decoder
// class, v2 by default (src/utils/encoding.js:354), but the class only picks
// the field encoding, and the reading of the structs and the delete set
// stays inside Yjs (readUpdateV2, src/utils/encoding.js:246). yrs 0.27.2 has
// no byte-level apply: the caller decodes with Update::decode_v1
// (src/updates/decoder.rs:11) and applies the decoded Update with
// TransactionMut::apply_update (src/transaction.rs:820). y-octo 0.1.0
// Doc::apply_update_from_binary_v1 (src/doc/document.rs:343) decodes v1 with
// its own reader and hands the Update to Doc::apply_update (:349). Past the
// decode the Go follows all three: the structs, then the delete set, in one
// transaction (ApplySyncUpdate; in y-octo, under one write lock).
func (d *Doc) ApplyEncodedUpdate(decode Codec, data []byte) bool {
	ok, structs, deletes := decode(data)
	if !ok {
		return false
	}
	d.ApplySyncUpdate(structs, deletes)
	return true
}
