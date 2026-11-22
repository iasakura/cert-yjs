// Package wsclient is the verified Yjs WebSocket client (issue #131): one
// connection to a y-websocket server, one document, one root text. What the
// connection delivers is decoded and applied through the verified total apply
// path (yjs.Doc.ApplyEncodedUpdate). The updates of the document are sent
// from an update handler (yjs.Doc.ObserveUpdate), except those the client
// applied itself, so an application edits the document with the document's
// own operations (Doc, Text). After every applied update the client writes
// the report of its root to the run's trace, as the server does (wsrelay,
// issue #239), and an application may write it after its own edits (Report),
// so that a closed theorem can compare the replicas.
//
// The reference client is y-websocket's WebsocketProvider (y-websocket v2.1.0
// src/y-websocket.js), and the client has its shape. The provider registers
// a document 'update' handler that sends every update whose origin is not
// the provider (:353-361), and it applies what it receives with itself as
// the transaction origin (:39-44), so that it does not send back what the
// server sent. The provider is given the application's document (the
// constructor's doc, :270, kept as this.doc, :296); here Connect creates the
// document and Doc returns it, so that one function sets up a whole client.
// The provider also runs the sync handshake on connect (it writes sync Step1
// when the socket opens, :203-208) and the awareness protocol; neither is
// here. Without the handshake a client never receives
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
// text Report reports, the deployment's decoder, and the lock that orders the
// sends of the update handler.
type Client struct {
	conn   wsnet.Connection
	doc    *yjs.Doc
	text   *yjs.Text
	name   string
	decode yjs.Codec
	sendMu sync.Mutex
}

// Connect dials host at path, creates the document as client and its root
// text name, and returns the client around them. It registers the update
// handler that sends the document's updates. The error
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

// Doc returns the client's document. An application edits it with the
// document's own operations (yjs.Doc.Transact, yjs.Text.Insert), as a
// y-websocket application edits the Y.Doc it gave the provider (y-websocket
// v2.1.0 src/y-websocket.js:296): the update handler Connect registered
// sends what each of its transactions integrated, before the transaction
// returns.
func (c *Client) Doc() *yjs.Doc {
	return c.doc
}

// Text returns the root text of the client's document, the one Report
// reports.
func (c *Client) Text() *yjs.Text {
	return c.text
}

// Report writes the report of the root to the run's trace: its name and the
// text as a read sees it, character by character (yjs.EncodeReport). Serve
// calls it after every applied update, and an application may call it after
// its own edits. It takes the document's read lock, so it must not be called
// inside a transaction. Verification tooling, as in wsrelay: no reference
// client has it.
func (c *Client) Report() {
	chars := c.text.Snapshot()
	wsnet.Trace(yjs.EncodeReport(c.name, chars))
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
			c.Report()
		}
	}
}

// Run is a whole client: connect, serve on a goroutine, and run the
// application app with the client. Connecting, sending and receiving are
// fixed; app is the part that edits, on the client's document (Doc, Text).
// This is what a closed theorem boots, for any app that meets the client's
// contract.
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
// one byte at a time, each byte as one code unit and one transaction of the
// client's document, and writes the report after each. An ASCII script types
// its text. The script is bytes and not code units because a byte is never a
// surrogate code unit: a unit typed alone is sent alone, and the wire cannot
// carry half of a surrogate pair (yjs/codec.go, issue #233).
func Typist(script string) func(c *Client) {
	return func(c *Client) {
		doc := c.Doc()
		text := c.Text()
		units := []byte(script)
		for i := 0; i < len(units); i++ {
			unit := []uint16{uint16(units[i])}
			doc.Transact(func(tr *yjs.Transaction) {
				text.InsertIn(tr, uint64(len(text.CodeUnitsIn(tr))), unit)
			})
			c.Report()
		}
	}
}
