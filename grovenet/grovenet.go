// Package grovenet is the network layer of the verified subset: the Go
// realization of Perennial's Grove FFI. goose maps this package to the grove
// FFI model (see the ffiMapping entry in perennial's goose/util), so callers
// are verified against the Grove network semantics
// (Perennial.goose_lang.ffi.grove_ffi.impl) via the trusted model in
// src/trusted_code/github_com/iasakura/cert_yjs/grovenet.v; this file is only
// the runtime realization and is never translated (the declfilter config
// src/code/github_com/iasakura/cert_yjs/grovenet.v.toml marks the API as
// trusted). Same trust status as goose itself.
//
// The TCP implementation is adapted from github.com/mit-pdos/gokv/grove_ffi
// (network.go), with two deviations: the ConnectRet/ReceiveRet struct returns
// are flattened to multiple return values (matching Perennial New's trusted
// grove model), and the length-prefix framing uses encoding/binary instead of
// the marshal dependency.
package grovenet

import (
	"encoding/binary"
	"fmt"
	"io"
	"net"
	"strconv"
	"strings"
	"sync"
)

// Address is a host (IPv4 + port) packed into a uint64, exactly as in
// gokv/grove_ffi: byte i of the IP at bits 8i..8i+7, port at bits 32..47.
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

type listener struct {
	l net.Listener
}

// Listener is an opaque handle for a listening socket (grove model:
// ListenSocketV behind a pointer).
type Listener *listener

// Listen starts listening on host. Errors are fatal (as in gokv: retrying
// makes little sense, the port is likely in use).
func Listen(host Address) Listener {
	l, err := net.Listen("tcp", AddressToStr(host))
	if err != nil {
		panic(err)
	}
	return &listener{l}
}

// Accept waits for the next incoming connection.
func Accept(l Listener) Connection {
	conn, err := l.l.Accept()
	if err != nil {
		panic(err)
	}
	return makeConnection(conn)
}

type connection struct {
	conn   net.Conn
	sendMu *sync.Mutex // guards sending on conn
	recvMu *sync.Mutex // guards receiving on conn
}

// Connection is an opaque handle for one bidirectional connection (grove
// model: ConnectionSocketV behind a pointer).
type Connection *connection

func makeConnection(conn net.Conn) Connection {
	return &connection{conn: conn, sendMu: new(sync.Mutex), recvMu: new(sync.Mutex)}
}

// Connect dials host. Returns (err, conn); on err=true the connection is not
// usable (grove model: BadSocketV).
func Connect(host Address) (bool, Connection) {
	conn, err := net.Dial("tcp", AddressToStr(host))
	if err != nil {
		return true, nil
	}
	return false, makeConnection(conn)
}

// Send transmits data as one message ([dataLen] ++ data framing). Returns
// true on error; a partial write kills the connection (the grove model's
// "late failure": the message may or may not have been delivered).
func Send(c Connection, data []byte) bool {
	msg := make([]byte, 8+len(data))
	binary.LittleEndian.PutUint64(msg, uint64(len(data)))
	copy(msg[8:], data)

	c.sendMu.Lock()
	defer c.sendMu.Unlock()
	_, err := c.conn.Write(msg)
	if err != nil {
		// There might have been a partial write; never send on this
		// connection again.
		c.conn.Close()
	}
	return err != nil
}

// Receive blocks for the next message on c. Returns (err, data); err=true
// means the connection is dead (e.g. the peer hung up).
func Receive(c Connection) (bool, []byte) {
	c.recvMu.Lock()
	defer c.recvMu.Unlock()

	header := make([]byte, 8)
	if _, err := io.ReadFull(c.conn, header); err != nil {
		c.conn.Close()
		return true, nil
	}
	dataLen := binary.LittleEndian.Uint64(header)
	data := make([]byte, dataLen)
	if _, err := io.ReadFull(c.conn, data); err != nil {
		c.conn.Close()
		return true, nil
	}
	return false, data
}
