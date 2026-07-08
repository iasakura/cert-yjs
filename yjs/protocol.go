//go:build !goose

package yjs

import "sort"

// y-protocols/sync doc-message layer (y-octo: src/protocol/{sync,doc}.rs;
// y-protocols/sync.js). This is the UNVERIFIED codec + dispatch rind wrapped
// around the verified execution core in sync.go: it parses a Step1/Step2/Update
// message, runs the core against the document, and frames the response. The
// verified core (computeStateVector / computeDiff / store.applyUpdate) is reached
// through the snapshot + (de)serialization here. Codec verification is future
// work (#43), so like codec.go this file is excluded from goose translation.
//
// Layout mirrors y-octo:
//   - readDocMessage / writeDocMessage   <- protocol/doc.rs (tag + var buffer)
//   - readStateVector / writeStateVector <- common/state.rs (StateVector codec)
//   - HandleSyncMessage                  <- y-protocols readSyncMessage (dispatch)
//   - snapshotStructs / encodeDiffUpdate <- doc/store.rs diff_state_vector's
//                                           item materialization + Update write
//
// Scope: only the Doc sub-protocol (Step1/Step2/Update) of y-octo's SyncMessage
// is implemented; Awareness / Auth / AwarenessQuery are out of scope for this
// issue. Single-threaded runtime interop, matching codec.go: the snapshot reads
// the DLLs and ApplyUpdate mutates the store without taking the lock, as the
// other codec entry points (EncodeUpdate / ApplyUpdate) already do.

// doc-message tags (y-octo: protocol/doc.rs DOC_MESSAGE_STEP1/STEP2/UPDATE).
const (
	docMessageStep1  = 0
	docMessageStep2  = 1
	docMessageUpdate = 2
)

// ----- lib0 var buffer (length-prefixed byte slice) --------------------------

func (e *encoder) writeVarBuffer(b []byte) {
	e.writeVarUint(uint64(len(b)))
	e.buf = append(e.buf, b...)
}

func (d *decoder) readVarBuffer() []byte {
	n := int(d.readVarUint())
	b := d.buf[d.pos : d.pos+n]
	d.pos += n
	return b
}

// ----- state vector codec (y-octo: common/state.rs StateVector read/write) ---

// writeStateVector serializes a state vector: the client count, then each
// (client, clock) pair (y-octo: impl CrdtWrite for StateVector).
func writeStateVector(sv map[Client]Clock) []byte {
	e := &encoder{}
	clients := sortedClientsDesc(sv)
	e.writeVarUint(uint64(len(clients)))
	for _, client := range clients {
		e.writeVarUint(client)
		e.writeVarUint(sv[client])
	}
	return e.buf
}

// readStateVector decodes a state vector into a client -> clock map (y-octo:
// impl CrdtRead for StateVector).
func readStateVector(data []byte) map[Client]Clock {
	d := &decoder{buf: data}
	sv := make(map[Client]Clock)
	n := d.readVarUint()
	for i := uint64(0); i < n; i++ {
		client := d.readVarUint()
		clock := d.readVarUint()
		sv[client] = clock
	}
	return sv
}

// ----- item snapshot + diff-update encoding ----------------------------------

// snapshotStructs materializes every live item in the document as a decoded
// updateItem, grouped by client and clock-ascending within each client (y-octo:
// the DocStore item map is the source of diff_structs; here we walk each root
// type's sequence, as EncodeUpdate does). Head items (no sibling origins) carry
// their root-type name so the receiver's repair can attach them (Parent::String);
// the rest carry their sibling origins. This snapshot is the input fed to the
// verified computeStateVector / computeDiff.
func snapshotStructs(doc *Doc) []updateItem {
	byClient := map[Client][]updateItem{}
	for nm, y := range doc.store.types {
		name := nm
		for cur := y.start; cur != nil; cur = cur.right {
			ui := updateItem{
				id:            cur.id,
				originLeftId:  cur.originLeftId,
				originRightId: cur.originRightId,
				content:       cur.content.content,
			}
			if cur.originLeftId == nil && cur.originRightId == nil {
				ui.parentName = &name
			}
			byClient[cur.id.clientId] = append(byClient[cur.id.clientId], ui)
		}
	}

	out := []updateItem{}
	for _, client := range sortedClientsDesc(byClient) {
		run := byClient[client]
		sort.Slice(run, func(i, j int) bool { return run[i].id.clock < run[j].id.clock })
		out = append(out, run...)
	}
	return out
}

// encodeUpdateItem serializes one decoded struct (y-octo: codec/item.rs Item
// write), reading its parent from updateItem.parentName rather than a reverse
// item->name lookup. Mirrors codec.go's encodeItem for the updateItem shape.
func encodeUpdateItem(e *encoder, ui updateItem) {
	info := byte(contentTypeString)
	if ui.originLeftId != nil {
		info |= infoHasLeftID
	}
	if ui.originRightId != nil {
		info |= infoHasRightID
	}
	e.writeU8(info)

	if ui.originLeftId != nil {
		e.writeItemID(*ui.originLeftId)
	}
	if ui.originRightId != nil {
		e.writeItemID(*ui.originRightId)
	}

	// a head item (no sibling origins) carries its parent: the root type name.
	if info&infoHasSibling == 0 {
		e.writeVarUint(1) // 1 => Parent::String
		name := ""
		if ui.parentName != nil {
			name = *ui.parentName
		}
		e.writeVarString(name)
	}

	e.writeVarString(ui.content)
}

// encodeDiffUpdate serializes a diff (the decoded struct list from computeDiff)
// plus the document's full delete set as a Yjs v1 update (y-octo:
// diff_state_vector packs the filtered structs and the *unfiltered*
// generate_delete_set). Structs are regrouped by client; each client's run is
// already clock-ascending, so the run head's clock is the section base clock.
// The result is what the receiver hands to Doc.ApplyUpdate.
func encodeDiffUpdate(structs []updateItem, doc *Doc) []byte {
	e := &encoder{}

	byClient := map[Client][]updateItem{}
	for _, ui := range structs {
		byClient[ui.id.clientId] = append(byClient[ui.id.clientId], ui)
	}
	clients := sortedClientsDesc(byClient)
	e.writeVarUint(uint64(len(clients)))
	for _, client := range clients {
		run := byClient[client]
		e.writeVarUint(uint64(len(run)))
		e.writeVarUint(client)
		e.writeVarUint(run[0].id.clock)
		for _, ui := range run {
			encodeUpdateItem(e, ui)
		}
	}

	// full delete set (y-octo diff_state_vector: generate_delete_set)
	deletedSet := generateDeleteSet(doc)
	delClients := sortedClientsDesc(deletedSet)
	e.writeVarUint(uint64(len(delClients)))
	for _, client := range delClients {
		e.writeVarUint(client)
		encodeOrderRange(e, deletedSet[client])
	}

	return e.buf
}

// ----- doc message framing + dispatch ----------------------------------------

// readDocMessage decodes the tag and raw payload of a y-protocols/sync doc
// message (y-octo: protocol/doc.rs read_doc_message). The payload is a state
// vector for Step1 and a v1 update for Step2/Update.
func readDocMessage(data []byte) (uint64, []byte) {
	d := &decoder{buf: data}
	tag := d.readVarUint()
	payload := d.readVarBuffer()
	return tag, payload
}

// writeDocMessage frames a tag + payload as a doc message (y-octo:
// write_doc_message).
func writeDocMessage(tag uint64, payload []byte) []byte {
	e := &encoder{}
	e.writeVarUint(tag)
	e.writeVarBuffer(payload)
	return e.buf
}

// WriteSyncStep1 frames this document's state vector as a Step1 message: the
// opening move of the y-protocols/sync handshake, asking a peer for whatever
// this replica is missing (y-protocols: writeSyncStep1). The state vector is
// computed by the verified computeStateVector over a document snapshot.
func (doc *Doc) WriteSyncStep1() []byte {
	sv := computeStateVector(snapshotStructs(doc))
	return writeDocMessage(docMessageStep1, writeStateVector(sv))
}

// WriteUpdate frames a raw v1 update as an Update message (y-protocols:
// writeUpdate), for broadcasting a local change to peers.
func WriteUpdate(update []byte) []byte {
	return writeDocMessage(docMessageUpdate, update)
}

// HandleSyncMessage parses one incoming sync doc message, executes it against
// the document, and returns the response bytes (nil when no reply is needed).
// This is the y-protocols readSyncMessage dispatcher (y-octo would route it via
// read_sync_message -> read_doc_message):
//   - Step1(sv):  reply with Step2 carrying computeDiff(doc, sv);
//   - Step2(u):   apply u (no reply);
//   - Update(u):  apply u (no reply).
func (doc *Doc) HandleSyncMessage(msg []byte) []byte {
	tag, payload := readDocMessage(msg)
	switch tag {
	case docMessageStep1:
		sv := readStateVector(payload)
		diff := computeDiff(snapshotStructs(doc), sv)
		return writeDocMessage(docMessageStep2, encodeDiffUpdate(diff, doc))
	case docMessageStep2:
		doc.ApplyUpdate(payload)
		return nil
	case docMessageUpdate:
		doc.ApplyUpdate(payload)
		return nil
	}
	return nil
}
