// Package wsrelay is the connection-management half of the verified Yjs
// WebSocket server (issue #107, W3): rooms, a per-room connection table, and
// relay fan-out, over the ws FFI.
//
// It carries no Yjs content yet. Whatever a connection sends is relayed
// verbatim to the room's other connections; the document and the sync-protocol
// handling are wired in at Serve's relay point next. What this package settles
// first is the ownership architecture, which is the part the FFI was built for:
//
//   - Accept hands out both cursors of a connection. The RECEIVE cursor stays
//     with that connection's own goroutine, which is why the receive loop needs
//     no lock and processes the peer's stream in order and exactly once.
//   - The SEND cursors of every connection in a room live together under the
//     room's lock, which is what lets any one connection's goroutine relay to
//     all the others. A connection's send side is not owned by its own
//     goroutine at all.
//
// Under grove this package could not exist: accepting a connection there grants
// no right to answer it, so a relay would need every peer to be modeled code
// escrowing its mailbox invariant. See src/goose_lang/ffi/ws_ffi/impl.v.
package wsrelay

import (
	"sync"

	"github.com/iasakura/cert-yjs/wsnet"
)

// Room is one y-websocket room: the connections currently in it, keyed by the
// order they joined in. The lock owns the send side of every connection in the
// table.
type Room struct {
	mu    sync.Mutex
	conns []wsnet.Connection
}

// NewRoom creates an empty room.
func NewRoom() *Room {
	return &Room{}
}

// Join hands the room the right to answer c.
func (r *Room) Join(c wsnet.Connection) {
	r.mu.Lock()
	r.conns = append(r.conns, c)
	r.mu.Unlock()
}

// Broadcast relays data to every connection in the room except self.
//
// Send errors are ignored, as in y-websocket: a peer that has gone away must
// not stop the others from receiving. Nothing is lost by ignoring them, since
// an error says nothing about delivery either way (the model's late failure).
func (r *Room) Broadcast(self wsnet.Connection, data []byte) {
	r.mu.Lock()
	for _, c := range r.conns {
		if c != self {
			wsnet.Send(c, data)
		}
	}
	r.mu.Unlock()
}

// Run accepts connections forever, joining each to the room and running its
// receive loop. This is the composition Join and Serve are meant to be used in,
// and the reason they are separate calls rather than one: the order matters.
//
// Join has to come first. A connection that is serving but not yet in the table
// does not receive what the others send in that window. y-websocket has the
// same race and absorbs it with the pending buffer; here the order rules it
// out. Between the two is where the sync handshake goes: a real client sends
// Step1 on connect and expects Step2 before the stream of updates, and that
// exchange belongs after joining and before the loop.
//
// Serve never returns, so it runs on its own goroutine. That is also the
// ownership split: Join hands the room this connection's send side, while the
// goroutine keeps its receive side and shares it with nobody.
func (r *Room) Run(l wsnet.Listener) {
	for {
		c, _ := wsnet.Accept(l)
		r.Join(c)
		go r.Serve(c)
	}
}

// Serve runs one connection's receive loop until the peer goes away, relaying
// every message it receives to the room's other connections. This is where the
// sync-protocol handling and the document go next: instead of relaying the
// bytes verbatim, decode them, apply the batch to the room's document, and
// relay what was applied.
func (r *Room) Serve(c wsnet.Connection) {
	for {
		err, data := wsnet.Receive(c)
		if err {
			return
		}
		r.Broadcast(c, data)
	}
}
