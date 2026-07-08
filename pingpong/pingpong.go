// Package pingpong is the feasibility demo for the grovenet (Grove FFI)
// pipeline (issue #45 / plan-network-yjs-protocol.md milestone N0): the
// smallest programs exercising Listen/Accept/Connect/Send/Receive, verified
// against the Grove network model via the WP wrappers in
// src/manualproof/github_com/iasakura/cert_yjs/grovenet.v (specs in
// src/proof/grove_pingpong.v).
//
// The two halves are verified with explicit mailbox ownership, so each is a
// single-owner spec: ServeOnce owns the server endpoint's mailbox, Ping owns
// it while sending. A concurrent echo server (Send back on the accepted
// connection) additionally needs the mailbox-invariant + first-message escrow
// design of docs/plan-network-yjs-protocol.md §5.3 and is deliberately out of
// this demo's scope.
package pingpong

import "github.com/iasakura/cert-yjs/grovenet"

// ServeOnce accepts one connection on l and receives one message from it.
// Returns (err, data); on err=true the connection died before a message
// arrived.
func ServeOnce(l grovenet.Listener) (bool, []byte) {
	c := grovenet.Accept(l)
	err, data := grovenet.Receive(c)
	return err, data
}

// Ping connects to host and sends msg as one message. Returns true on error
// (either connecting or sending).
func Ping(host grovenet.Address, msg []byte) bool {
	err, c := grovenet.Connect(host)
	if err {
		return true
	}
	return grovenet.Send(c, msg)
}
