// Package wsrelay is the verified Yjs WebSocket server (issue #107, W3):
// rooms, a per-room connection table, and the y-websocket message loop for
// the update case, over the ws FFI. What a connection sends is decoded,
// applied to the room's document through the verified total apply path
// (yjs.Doc.ApplyEncodedUpdate), and relayed verbatim to the room's other
// connections.
//
// The ownership architecture is the part the FFI was built for:
//
//   - Accept hands out both cursors of a connection. The RECEIVE cursor stays
//     with that connection's own goroutine, which is why the receive loop needs
//     no lock and processes the peer's stream in order and exactly once.
//   - The SEND cursors of every connection in a room live together under the
//     room's lock, which is what lets any one connection's goroutine relay to
//     all the others. A connection's send side is not owned by its own
//     goroutine at all.
//
// One room.mu critical section spans the apply and the fan-out (process), so
// processing serializes per room. That is y-websocket's own semantics (a Node
// process runs a doc's message handlers on one thread), and it is what makes
// the room's processed-message log simultaneously the apply order and the
// relay order in the proofs (src/proof/ws_relay.v). The store's write lock
// nests inside room.mu and nothing takes them in the other order.
//
// Under grove this package could not exist: accepting a connection there grants
// no right to answer it, so a relay would need every peer to be modeled code
// escrowing its mailbox invariant. See src/goose_lang/ffi/ws_ffi/impl.v.
package wsrelay

import (
	"sync"

	"github.com/iasakura/cert-yjs/wsnet"
	"github.com/iasakura/cert-yjs/yjs"
)

// Room is one y-websocket room: its document, the connections currently in
// it (keyed by the order they joined in), and the codec the deployment
// decodes wire updates with. The lock owns the document and the send side of
// every connection in the table.
type Room struct {
	mu     sync.Mutex
	conns  []wsnet.Connection
	doc    *yjs.Doc
	decode yjs.Codec
}

// NewRoom creates an empty room around doc, decoding wire updates with
// decode (the deployment passes yjs.WireCodec()).
func NewRoom(doc *yjs.Doc, decode yjs.Codec) *Room {
	return &Room{doc: doc, decode: decode}
}

// Join hands the room the right to answer c. Relays reach c from this point
// on; there is no backfill of earlier state until the Step1/Step2 handshake
// lands (issue #107, W3c).
func (r *Room) Join(c wsnet.Connection) {
	r.mu.Lock()
	r.conns = append(r.conns, c)
	r.mu.Unlock()
}

// process handles one message received from self: decode it, apply the batch
// to the room's document, and relay the applied update, verbatim, to every
// other connection in the room.
//
// A message that does not decode is not applied and not relayed, as in
// y-websocket (only applied updates reach the broadcast); the wire protocol
// makes that branch dead for the verified server. Send errors are ignored,
// as in y-websocket: a peer that has gone away must not stop the others from
// receiving, and an error says nothing about delivery either way (the
// model's late failure).
//
// Divergence from y-websocket, deliberate: its updateHandler sends to ALL
// connections including the origin (the origin dedups the echo); we skip
// self, as the W3a relay already did. Safe either way, since delivery is
// idempotent per operation.
func (r *Room) process(self wsnet.Connection, data []byte) {
	r.mu.Lock()
	applied := r.doc.ApplyEncodedUpdate(r.decode, data)
	if applied {
		for _, c := range r.conns {
			if c != self {
				wsnet.Send(c, data)
			}
		}
	}
	r.mu.Unlock()
}

// Serve runs one connection's receive loop until the peer goes away,
// processing every message it receives (apply + relay). It owns that
// connection's receive cursor for the whole run and shares it with nobody,
// which is what makes the peer's stream arrive in order and exactly once
// with no lock on the read path. Its send side is not here: Join gave it to
// the room.
func (r *Room) Serve(c wsnet.Connection) {
	for {
		err, data := wsnet.Receive(c)
		if err {
			return
		}
		r.process(c, data)
	}
}

// Run accepts connections forever, joining each to the room and serving it
// on its own goroutine. Single-room: the path Accept reports (the
// y-websocket room name) is ignored until the multi-room server lands.
func Run(l wsnet.Listener, r *Room) {
	for {
		c, _ := wsnet.Accept(l)
		r.Join(c)
		go r.Serve(c)
	}
}

// ListenAndServe listens on host, creates the server document as client,
// and serves a room around it forever, decoding wire updates with decode
// (the deployment passes yjs.WireCodec()). This is the whole server; the
// closed-system theorem (src/proof/demo/ws_server.v) is about booting
// exactly this function.
func ListenAndServe(host wsnet.Address, client yjs.Client, decode yjs.Codec) {
	l := wsnet.Listen(host)
	dv := yjs.NewDoc(client)
	r := NewRoom(dv, decode)
	Run(l, r)
}
