package yjs

import "sync"

// Document-level API (Yjs: src/utils/Doc.js; yrs: src/doc.rs; y-octo:
// doc/document.rs). Goose-translated like store.go / text.go.

// Doc is a document: the lock and, under it, the store (the data and the
// observers, store.go). The lock is yrs's RwLock<Store> (src/store.rs:509-512)
// and y-octo's Arc<RwLock<DocStore>> (src/doc/store.rs:36) placed on the Doc;
// Yjs is single-threaded and has none. Where y-octo's lock guards the data
// alone (its publisher has its own lock), this one guards the observers too,
// so that a transaction's callbacks run before its unlock (Transact,
// transaction.go).
type Doc struct {
	// mu guards *store: the data (and the YTypes' DLLs reached through its
	// types) and the observers. Writers (Insert/Delete/GetOrCreateText/
	// ApplySyncUpdate/Observe) take the write lock (Lock); pure readers
	// (String/Len) take the read lock (RLock) so concurrent reads are allowed.
	mu sync.RWMutex
	// store is what mu guards, made once and never reassigned.
	store *store
}

// NewDoc creates a document with a fresh store owned by client.
func NewDoc(client Client) *Doc {
	return &Doc{store: newStore(client)}
}

// GetOrCreateText returns the root text type named name, creating it on first use
// (y-octo: Doc::get_or_create_text). Registering the type mutates the data, so
// it is done under the write lock.
func (d *Doc) GetOrCreateText(name string) *Text {
	d.mu.Lock()
	inner := d.store.data.getOrCreateYType(name)
	d.mu.Unlock()
	return &Text{doc: d, inner: inner}
}

// applyUpdate integrates a decoded update batch as one transaction (y-octo:
// Doc::apply_update takes store.write() for the whole apply; Yjs applyUpdate
// runs inside transact). The verified core is dataStore.applyUpdate, which is
// total: structs whose dependencies have not arrived are buffered in the
// data and drained by later calls. The codec-level Doc.ApplyUpdate
// (codec.go) decodes the wire format and routes the batch through here.
func (d *Doc) applyUpdate(structs []updateItem) {
	d.Transact(func(tr *Transaction) {
		tr.store.data.applyUpdate(tr, structs)
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
