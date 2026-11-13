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
// side is the caller's.
func (c *Client) Insert(index uint64, content []uint16) bool {
	update := c.text.InsertEncoded(index, content, c.encode)
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

// Run is the scripted client the closed theorem boots: connect, serve on a
// goroutine, and type script at the end of the text one code unit at a time.
// A real client calls Insert from its user interface instead. A script is
// free of surrogate code units: a unit typed alone is sent alone, and the
// wire cannot carry half of a surrogate pair (yjs/codec.go, issue #233).
func Run(host wsnet.Address, path string, client yjs.Client,
	decode yjs.Codec, encode yjs.Encoder, name string, script []uint16) {
	err, c := Connect(host, path, client, decode, encode, name)
	if err {
		return
	}
	go c.Serve()
	for i := uint64(0); i < uint64(len(script)); i++ {
		c.Insert(c.text.Len(), script[i:i+1])
	}
}
