// Package wsecho is the feasibility demo for the ws FFI pipeline: the smallest
// program that accepts a connection and ANSWERS it, which is exactly what the
// grove FFI cannot express (see wsnet/wsnet.go's header). Verified against the
// ws network model via the WP wrappers in
// src/manualproof/github_com/iasakura/cert_yjs/wsnet.v (specs in
// src/proof/demo/ws_echo.v).
//
// Unlike the grovenet ping-pong demo, no mailbox ownership has to be escrowed
// from the peer: Accept hands the server both cursors of the connection, so
// the reply is provable with no assumption whatsoever about who connected.
package wsecho

import "github.com/iasakura/cert-yjs/wsnet"

// ServeEcho accepts one connection and echoes its first message back on the
// same connection. Returns true if either half failed.
func ServeEcho(l wsnet.Listener) bool {
	c, _ := wsnet.Accept(l)
	err, data := wsnet.Receive(c)
	if err {
		return true
	}
	return wsnet.Send(c, data)
}
