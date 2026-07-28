// Package wsnet is the connection-oriented network layer of the verified
// subset: the Go realization of the ws FFI (a connection is two one-way,
// ordered, exactly-once message channels), speaking WebSocket on the wire.
// goose maps this package to that FFI (see the ffiMapping entry in the
// perennial fork's goose/util), so callers are verified against the model in
// src/goose_lang/ffi/ws_ffi/impl.v via the trusted model in
// src/trusted_code/github_com/iasakura/cert_yjs/wsnet.v; this file is only the
// runtime realization and is never translated (the declfilter config
// src/code/github_com/iasakura/cert_yjs/wsnet.v.toml marks the API as
// trusted). Same trust status as goose itself.
//
// Why not grovenet: the grove FFI models endpoints with mailboxes rather than
// connections, so Accept grants no right to answer the peer and Send needs the
// receiver's mailbox. A server cannot be verified against it unless every peer
// is itself modeled code that hands its mailbox invariant over. See
// src/goose_lang/ffi/ws_ffi/impl.v's header.
//
// The impedance match is exact: the ws FFI's unit of transfer is a message and
// so is a WebSocket binary frame, so Send is one frame out and Receive is one
// frame in. Handshake, framing, masking, fragmentation and control frames are
// github.com/coder/websocket's job (a dependency-free RFC 6455
// implementation); the trust added over the model is that library plus the
// glue below.
//
// The path a peer connects to is the HTTP request path, i.e. the y-websocket
// room name, and is returned by Accept.
package wsnet

import (
	"context"
	"fmt"
	"net"
	"net/http"
	"strconv"
	"strings"
	"sync"

	"github.com/coder/websocket"
)

// readLimit caps one incoming message. The default (32KiB) is too small for
// Yjs updates; a document's whole state can arrive as a single Step2 message.
const readLimit int64 = 32 << 20

// Address is a host (IPv4 + port) packed into a uint64, exactly as in
// grovenet: byte i of the IP at bits 8i..8i+7, port at bits 32..47.
type Address = uint64

// MakeAddress parses "a.b.c.d:port" into an Address. Runtime helper (not part
// of the verified API).
func MakeAddress(ipStr string) uint64 {
	ipPort := strings.Split(ipStr, ":")
	if len(ipPort) != 2 {
		panic(fmt.Sprintf("not ipv4:port %s", ipStr))
	}
	port, err := strconv.ParseUint(ipPort[1], 10, 16)
	if err != nil {
		panic(err)
	}
	ss := strings.Split(ipPort[0], ".")
	if len(ss) != 4 {
		panic(fmt.Sprintf("not ipv4:port %s", ipStr))
	}
	ip := make([]byte, 4)
	for i, s := range ss {
		a, err := strconv.ParseUint(s, 10, 8)
		if err != nil {
			panic(err)
		}
		ip[i] = byte(a)
	}
	return uint64(ip[0]) | uint64(ip[1])<<8 | uint64(ip[2])<<16 | uint64(ip[3])<<24 | port<<32
}

// AddressToStr renders an Address as "a.b.c.d:port". Runtime helper.
func AddressToStr(e Address) string {
	a0 := byte(e & 0xff)
	e = e >> 8
	a1 := byte(e & 0xff)
	e = e >> 8
	a2 := byte(e & 0xff)
	e = e >> 8
	a3 := byte(e & 0xff)
	e = e >> 8
	port := e & 0xffff
	return fmt.Sprintf("%s:%d", net.IPv4(a0, a1, a2, a3).String(), port)
}

// arrival is one upgraded connection waiting to be handed to Accept, together
// with the path it asked for.
type arrival struct {
	conn *websocket.Conn
	path string
	// closed when the connection is finished with, releasing the HTTP handler
	// that owns the hijacked socket.
	done chan struct{}
}

type listener struct {
	incoming chan arrival
}

// Listener is an opaque handle for a listening socket (ws model: a
// ListenSocketV behind a pointer).
type Listener *listener

// Listen starts serving WebSocket upgrades on host. Errors are fatal (as in
// gokv: retrying makes little sense, the port is likely in use).
//
// Origin checking is disabled on purpose: the model makes no assumption about
// who connects, and the safety theorems hold for arbitrary peers, so refusing
// cross-origin browsers would buy nothing the proofs rely on.
func Listen(host Address) Listener {
	sock, err := net.Listen("tcp", AddressToStr(host))
	if err != nil {
		panic(err)
	}
	l := &listener{incoming: make(chan arrival)}
	srv := &http.Server{
		Handler: http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			c, err := websocket.Accept(w, r, &websocket.AcceptOptions{
				OriginPatterns: []string{"*"},
			})
			if err != nil {
				return
			}
			c.SetReadLimit(readLimit)
			a := arrival{conn: c, path: r.URL.Path, done: make(chan struct{})}
			l.incoming <- a
			// The hijacked socket belongs to this handler; returning would
			// tear the connection down, so wait until it is finished with.
			<-a.done
		}),
	}
	go srv.Serve(sock)
	return l
}

// There is no send or receive mutex here, deliberately. Serialization comes
// from two places already: the ws FFI hands out the send and receive cursors
// exclusively, so verified code cannot interleave two sends (a caller that
// wants to share a connection puts the cursor in a lock invariant of its own,
// which is where the lock belongs); and the library serializes both directions
// internally ("only one writer can be open at a time" for Writer, a blocking
// readMu in reader). Send and Receive still run concurrently with each other,
// which is why killConn is guarded by a Once.
type connection struct {
	conn *websocket.Conn
	done chan struct{} // nil on the dialing side (no HTTP handler to release)
	once *sync.Once
}

// Connection is an opaque handle for one endpoint of a connection: the send
// side of one channel and the receive side of the other (ws model: a
// ConnectionV behind a pointer).
type Connection *connection

func makeConnection(conn *websocket.Conn, done chan struct{}) Connection {
	return &connection{conn: conn, done: done, once: new(sync.Once)}
}

// killConn retires a connection after a transport error. The model has no
// close operation (a dead connection is one whose receives never progress
// again), so this only releases the runtime resources. It is a function rather
// than a method because Connection is a defined pointer type, which carries no
// methods.
func killConn(c Connection) {
	c.once.Do(func() {
		c.conn.CloseNow()
		if c.done != nil {
			close(c.done)
		}
	})
}

// Accept waits for the next incoming connection and returns it together with
// the path the peer asked for (the y-websocket room name).
func Accept(l Listener) (Connection, string) {
	a := <-l.incoming
	return makeConnection(a.conn, a.done), a.path
}

// Connect dials host and asks for path. Returns (err, conn); on err=true the
// connection is not usable (ws model: BadConnectionV).
//
// path is the request path and must begin with "/", so that the path Accept
// reports on the other side is exactly the one passed here, as the model says.
func Connect(host Address, path string) (bool, Connection) {
	if !strings.HasPrefix(path, "/") {
		panic(fmt.Sprintf("wsnet.Connect: path must begin with \"/\": %q", path))
	}
	c, _, err := websocket.Dial(context.Background(), "ws://"+AddressToStr(host)+path, nil)
	if err != nil {
		return true, nil
	}
	c.SetReadLimit(readLimit)
	return false, makeConnection(c, nil)
}

// Send transmits data as one WebSocket binary frame. Returns true on error; an
// error kills the connection and says nothing about delivery (the model's late
// failure: the frame may or may not have reached the peer).
func Send(c Connection, data []byte) bool {
	if err := c.conn.Write(context.Background(), websocket.MessageBinary, data); err != nil {
		killConn(c)
		return true
	}
	return false
}

// Receive blocks for the next binary message on c. Returns (err, data);
// err=true means nothing was delivered (the connection is dead, e.g. the peer
// hung up). Text frames are skipped: the model's messages are byte strings and
// the Yjs sync protocol is binary.
func Receive(c Connection) (bool, []byte) {
	for {
		typ, data, err := c.conn.Read(context.Background())
		if err != nil {
			killConn(c)
			return true, nil
		}
		if typ == websocket.MessageBinary {
			return false, data
		}
	}
}
