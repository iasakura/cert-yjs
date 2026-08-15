package yjs

// Sync-protocol apply path over the real document (issue #51).
//
// A decoded Step2/Update batch is integrated into the document's own store,
// under the write lock, with the proven conflict-resolving integrate loop
// (store.applyUpdate). There is NO shadow item list: the structs go through the
// real CRDT integration against the real store, so the replica's history
// advances for real. The verified spec (wp_Doc__ApplySyncUpdate, in
// src/proof/doc/doc.v) reports that change as growth of the ghost history
// certificate is_history_lb -- i.e. the document's delivered-history fragment
// now contains exactly this batch.
//
// This is the receiving half of the sync protocol (y-protocols/sync
// readSyncMessage's Step2/Update case). The byte decoding of the wire update
// into []updateItem is the unverified codec (codec.go, //go:build !goose); the
// sender-side diff (Step1) against the real store is separate follow-on work.
func (d *Doc) ApplySyncUpdate(structs []updateItem, deletes []deleteSpan) {
	s := d.store
	s.mu.Lock()
	s.applyUpdate(structs)
	// deletes go second: a span may target a struct that just arrived in
	// this very batch (y-octo applies the delete set after the structs).
	s.applyDeleteSpans(deletes)
	s.mu.Unlock()
}
