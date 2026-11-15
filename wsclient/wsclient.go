// Package wsclient is the verified Yjs WebSocket client (issue #131): one
// connection to a y-websocket server, one document, one root text. What the
// connection delivers is decoded and applied through the verified total apply
// path (yjs.Doc.ApplyEncodedUpdate); a local edit is inserted, encoded and
// sent in one call (yjs.Text.InsertEncoded, then wsnet.Send). After every
// local edit and every applied update the client writes the report of its
// root to the run's trace, as the server does (wsrelay, issue #239), so that
// a closed theorem can compare the replicas.
//
// The reference client is y-websocket's WebsocketProvider (y-websocket v2.1.0
// src/y-websocket.js). It sends every local update from a document 'update'
// handler as soon as the transaction that made it ends (:353-361), and so
// does Insert, without the handler registry: the edit and the send are one
// call. The provider also runs the sync handshake on connect (it writes sync
// Step1 when the socket opens, :203-208) and the awareness protocol; neither
// is here. Without the
// handshake a client never receives what was edited before it joined (the
// server relays only what it applies after the join, wsrelay.Join), which
// the closed theorem's convergence statement accounts for: it compares
// reports that hold the same ids.
//
// Ownership: the connection's receive cursor belongs to the goroutine running
// Serve and its send cursor to the goroutine calling Insert, so neither needs
// a lock; the document's own lock orders an apply against a local edit.
package wsclient

import (
	"github.com/iasakura/cert-yjs/wsnet"
	"github.com/iasakura/cert-yjs/yjs"
)

// Client is one y-websocket client: its connection, its document, the root
// text it edits and reports on, and the deployment's two codec values.
type Client struct {
	conn   wsnet.Connection
	doc    *yjs.Doc
	text   *yjs.Text
	name   string
	decode yjs.Codec
	encode yjs.Encoder
}

// Connect dials host at path, creates the document as client, and returns
// the client around them, editing and reporting on the root text name. The
// error flag is wsnet.Connect's: on true there is no client. The deployment
// passes yjs.WireCodec() and yjs.WireEncoder().
func Connect(host wsnet.Address, path string, client yjs.Client,
	decode yjs.Codec, encode yjs.Encoder, name string) (bool, *Client) {
	err, conn := wsnet.Connect(host, path)
	if err {
		return true, nil
	}
	doc := yjs.NewDoc(client)
	return false, &Client{
		conn:   conn,
		doc:    doc,
		text:   doc.GetOrCreateText(name),
		name:   name,
		decode: decode,
		encode: encode,
	}
}

// report writes the report of the root to the run's trace: its name and the
// text as a read sees it, character by character (yjs.EncodeReport).
// Verification tooling, as in wsrelay: no reference client has it.
func (c *Client) report() {
	chars := c.text.Snapshot()
	wsnet.Trace(yjs.EncodeReport(c.name, chars))
}

// Insert is one local edit: insert content at the visible index as one
// transaction, send the update that carries it, and write the report of the
// root to the trace. It returns Send's error flag; the edit is made locally
// either way, and an error says nothing about delivery (the model's late
// failure). Not to be called concurrently with itself: the connection's send
// side is the caller's. The content should hold no surrogate code unit: the
// wire carries UTF-8, which has no encoding of half a surrogate pair, so the
// update of such an insert does not carry what was inserted here (yjs/codec.go,
// issue #233; Yjs and y-websocket have the same limit, an insert that ends
// between the halves of a pair reaches the peers as U+FFFD).
func (c *Client) Insert(index uint64, content []uint16) bool {
	update := c.text.InsertEncoded(index, content, c.encode)
	err := wsnet.Send(c.conn, update)
	c.report()
	return err
}

// Transact is one local edit of any shape: it runs f as one transaction on
// the client's document, handing it the transaction and the root text, then
// sends the update that carries what the transaction integrated and writes
// the report of the root to the trace. This is the fixed half of a client:
// whatever f edits, what it inserted is what goes on the wire (y-websocket's
// provider does the same from the document's 'update' handler, y-websocket
// v2.1.0 src/y-websocket.js:353-361). It returns Send's error flag, as
// Insert does, and like Insert it is not to be called concurrently with
// itself or with Insert. f must not lock the document again (yjs.Doc.Transact);
// it uses the In-variants with tr. What f inserts should hold no surrogate
// code unit, for the reason given at Insert. What f deletes is not sent
// (yjs.Doc.TransactEncoded).
func (c *Client) Transact(f func(tr *yjs.Transaction, text *yjs.Text)) bool {
	text := c.text
	update := c.doc.TransactEncoded(func(tr *yjs.Transaction) {
		f(tr, text)
	}, c.encode)
	err := wsnet.Send(c.conn, update)
	c.report()
	return err
}

// Serve is the receive loop, until the connection is gone: apply every
// received update through the verified total apply path and, after each one
// that decoded, write the report of the root to the trace. It owns the
// connection's receive cursor for the whole run.
func (c *Client) Serve() {
	for {
		err, data := wsnet.Receive(c.conn)
		if err {
			return
		}
		applied := c.doc.ApplyEncodedUpdate(c.decode, data)
		if applied {
			c.report()
		}
	}
}

// Run is a whole client: connect, serve on a goroutine, and run the
// application app with the client. Connecting and receiving are fixed; app is
// the part that edits, through Insert and Transact, and it holds the client's
// send side for the whole run. This is what a closed theorem boots, for any
// app that meets the client's contract.
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
