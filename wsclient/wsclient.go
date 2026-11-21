// Package wsclient is the verified Yjs WebSocket client (issue #131): one
// connection to a y-websocket server, one document, one root text. What the
// connection delivers is decoded and applied through the verified total apply
// path (yjs.Doc.ApplyEncodedUpdate). The updates of the document are sent
// from an update handler (yjs.Doc.ObserveUpdate), except those the client
// applied itself. After every local edit and every applied update the client
// writes the report of its root to the run's trace, as the server does
// (wsrelay, issue #239), so that a closed theorem can compare the replicas.
//
// The reference client is y-websocket's WebsocketProvider (y-websocket v2.1.0
// src/y-websocket.js), and the client has its shape. The provider registers
// a document 'update' handler that sends every update whose origin is not
// the provider (:353-361), and it applies what it receives with itself as
// the transaction origin (:39-44), so that it does not send back what the
// server sent. The provider also runs the sync handshake on connect (it
// writes sync Step1 when the socket opens, :203-208) and the awareness
// protocol; neither is here. Without the handshake a client never receives
// what was edited before it joined (the server relays only what it applies
// after the join, wsrelay.Join), which the closed theorem's convergence
// statement accounts for: it compares reports that hold the same ids.
//
// Ownership: the connection's receive cursor belongs to the goroutine running
// Serve. Its send cursor is under the client's send lock, because the update
// handler runs in whichever goroutine ended a transaction.
package wsclient

import (
	"sync"

	"github.com/iasakura/cert-yjs/wsnet"
	"github.com/iasakura/cert-yjs/yjs"
)

// providerOrigin is the origin of the transactions that apply what the
// connection delivered; the update handler does not send their updates.
// y-websocket passes the provider object as the origin (y-websocket v2.1.0
// src/y-websocket.js:39-44) and compares identities (:354). Origin is a
// string here (yjs.Origin, after yrs), so the provider's origin is a name.
const providerOrigin yjs.Origin = "wsclient"

// Client is one y-websocket client: its connection, its document, the root
// text it edits and reports on, the deployment's decoder, and the lock that
// orders the sends of the update handler.
type Client struct {
	conn   wsnet.Connection
	doc    *yjs.Doc
	text   *yjs.Text
	name   string
	decode yjs.Codec
	sendMu sync.Mutex
}

// Connect dials host at path, creates the document as client, and returns
// the client around them, editing and reporting on the root text name. It
// registers the update handler that sends the document's updates. The error
// flag is wsnet.Connect's: on true there is no client. The deployment passes
// yjs.WireCodec() and yjs.WireEncoder().
func Connect(host wsnet.Address, path string, client yjs.Client,
	decode yjs.Codec, encode yjs.Encoder, name string) (bool, *Client) {
	err, conn := wsnet.Connect(host, path)
	if err {
		return true, nil
	}
	doc := yjs.NewDoc(client)
	c := &Client{
		conn:   conn,
		doc:    doc,
		text:   doc.GetOrCreateText(name),
		name:   name,
		decode: decode,
	}
	doc.ObserveUpdate(encode, func(update []byte, origin yjs.Origin) {
		c.sendUpdate(update, origin)
	})
	return false, c
}

// sendUpdate is the client's update handler (y-websocket v2.1.0
// src/y-websocket.js:353-361): it sends update unless the transaction that
// made it is one of the client's own applies (providerOrigin). Send's error
// flag is dropped, as the provider drops it: an error says nothing about
// delivery (the model's late failure), and the edit is made locally either
// way. It runs under the document's write lock (yjs.Doc.ObserveUpdate) and
// must not touch the document.
//
// What a local transaction inserts should hold no surrogate code unit: the
// update is UTF-8, which has no encoding of half a surrogate pair, so such an
// insert reaches the peers as U+FFFD (yjs/codec.go, issue #233; Yjs and
// y-websocket have the same limit). What a transaction deletes is not sent
// (yjs.Doc.ObserveUpdate).
func (c *Client) sendUpdate(update []byte, origin yjs.Origin) {
	if origin == providerOrigin {
		return
	}
	c.sendMu.Lock()
	wsnet.Send(c.conn, update)
	c.sendMu.Unlock()
}

// report writes the report of the root to the run's trace: its name and the
// text as a read sees it, character by character (yjs.EncodeReport).
// Verification tooling, as in wsrelay: no reference client has it.
func (c *Client) report() {
	chars := c.text.Snapshot()
	wsnet.Trace(yjs.EncodeReport(c.name, chars))
}

// Transact is one local edit of any shape: it runs f as one transaction on
// the client's document, handing it the transaction and the root text, and
// then writes the report of the root to the trace. The update handler sends
// what the transaction integrated before Transact returns. f must not lock
// the document again (yjs.Doc.Transact); it uses the In-variants with tr.
// An application may also edit the document directly, as a y-websocket
// application does; Transact adds the report.
func (c *Client) Transact(f func(tr *yjs.Transaction, text *yjs.Text)) {
	text := c.text
	c.doc.Transact(func(tr *yjs.Transaction) {
		f(tr, text)
	})
	c.report()
}

// Serve is the receive loop, until the connection is gone: apply every
// received update through the verified total apply path, with the provider's
// origin so that the update handler does not send it back, and, after each
// one that decoded, write the report of the root to the trace. It owns the
// connection's receive cursor for the whole run.
func (c *Client) Serve() {
	for {
		err, data := wsnet.Receive(c.conn)
		if err {
			return
		}
		applied := c.doc.ApplyEncodedUpdate(c.decode, data, providerOrigin)
		if applied {
			c.report()
		}
	}
}

// Run is a whole client: connect, serve on a goroutine, and run the
// application app with the client. Connecting, sending and receiving are
// fixed; app is the part that edits, through Transact. This is what a closed
// theorem boots, for any app that meets the client's contract.
func Run(host wsnet.Address, path string, client yjs.Client,
	decode yjs.Codec, encode yjs.Encoder, name string, app func(c *Client)) {
	err, c := Connect(host, path, client, decode, encode, name)
	if err {
		return
	}
	go c.Serve()
	app(c)
}

// Typist is an application for Run: it types script at the end of the text
// one byte at a time, each byte as one code unit and one transaction, so
// that an ASCII script types its text. The script is bytes and not code
// units because a byte is never a surrogate code unit: a unit typed alone is
// sent alone, and the wire cannot carry half of a surrogate pair
// (yjs/codec.go, issue #233).
func Typist(script string) func(c *Client) {
	return func(c *Client) {
		units := []byte(script)
		for i := 0; i < len(units); i++ {
			unit := []uint16{uint16(units[i])}
			c.Transact(func(tr *yjs.Transaction, text *yjs.Text) {
				text.InsertIn(tr, uint64(len(text.CodeUnitsIn(tr))), unit)
			})
		}
	}
}
