package wsclient

import (
	"net"
	"strconv"
	"testing"
	"time"

	"github.com/iasakura/cert-yjs/wsnet"
	"github.com/iasakura/cert-yjs/wsrelay"
	"github.com/iasakura/cert-yjs/yjs"
)

// startServer brings the verified server up on a free port and returns its
// address.
func startServer(t *testing.T) wsnet.Address {
	t.Helper()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("reserving a port: %v", err)
	}
	port := l.Addr().(*net.TCPAddr).Port
	if err := l.Close(); err != nil {
		t.Fatalf("closing the probe listener: %v", err)
	}
	addr := wsnet.MakeAddress("127.0.0.1:" + strconv.Itoa(port))
	go wsrelay.ListenAndServe(addr, 1, yjs.WireCodec(), "root")
	return addr
}

// connect dials the server as client, retrying while the listener comes up,
// and serves the connection on a goroutine.
func connect(t *testing.T, addr wsnet.Address, client yjs.Client) *Client {
	t.Helper()
	deadline := time.Now().Add(5 * time.Second)
	for {
		err, c := Connect(addr, "/room", client, yjs.WireCodec(), yjs.WireEncoder(), "root")
		if !err {
			go c.Serve()
			return c
		}
		if time.Now().After(deadline) {
			t.Fatalf("client %d could not connect", client)
		}
		time.Sleep(10 * time.Millisecond)
	}
}

// waitForText polls c's text until it reads want.
func waitForText(t *testing.T, c *Client, want string) {
	t.Helper()
	deadline := time.Now().Add(5 * time.Second)
	for c.text.String() != want {
		if time.Now().After(deadline) {
			t.Fatalf("text reads %q, want %q", c.text.String(), want)
		}
		time.Sleep(10 * time.Millisecond)
	}
}

// units is the code units of an ASCII string.
func units(s string) []uint16 {
	result := make([]uint16, 0, len(s))
	for _, r := range s {
		result = append(result, uint16(r))
	}
	return result
}

// insert is one transaction of c that inserts content at index.
func insert(c *Client, index uint64, content string) {
	c.Transact(func(tr *yjs.Transaction, text *yjs.Text) {
		text.InsertIn(tr, index, units(content))
	})
}

// An edit one client makes through Transact reaches the other client through
// the server: the update handler sends the transaction's structs, encoded by
// the deployment's encoder, and they are decoded and applied twice (server,
// other client).
func TestInsertReachesTheOtherClient(t *testing.T) {
	addr := startServer(t)
	a := connect(t, addr, 2)
	b := connect(t, addr, 3)
	// the server relays only to connections it has already joined
	time.Sleep(200 * time.Millisecond)

	insert(a, 0, "hello")
	waitForText(t, b, "hello")

	insert(b, 5, " world")
	waitForText(t, a, "hello world")
	waitForText(t, b, "hello world")
}

// Concurrent edits at the same position converge on both clients, whatever
// order the relays arrive in.
func TestConcurrentInsertsConverge(t *testing.T) {
	addr := startServer(t)
	a := connect(t, addr, 2)
	b := connect(t, addr, 3)
	time.Sleep(200 * time.Millisecond)

	insert(a, 0, "AAA")
	insert(b, 0, "BBB")
	// client 2 sorts before client 3 at the same origin
	waitForText(t, a, "AAABBB")
	waitForText(t, b, "AAABBB")
}

// Two scripted clients, each typing its script one byte at a time,
// end up with the same text, which holds both scripts in order.
func TestScriptedClientsConverge(t *testing.T) {
	addr := startServer(t)
	observer := connect(t, addr, 9)
	time.Sleep(200 * time.Millisecond)

	done := make(chan struct{}, 2)
	for i, script := range []string{"abc", "xyz"} {
		go func(client yjs.Client, script string) {
			// Run returns once the script is typed; its Serve goroutine goes on.
			Run(addr, "/room", client, yjs.WireCodec(), yjs.WireEncoder(), "root", Typist(script))
			done <- struct{}{}
		}(yjs.Client(20+i), script)
	}
	<-done
	<-done

	deadline := time.Now().Add(5 * time.Second)
	for len(observer.text.String()) != 6 {
		if time.Now().After(deadline) {
			t.Fatalf("observer reads %q, want six characters", observer.text.String())
		}
		time.Sleep(10 * time.Millisecond)
	}
	got := observer.text.String()
	for _, script := range []string{"abc", "xyz"} {
		position := 0
		for _, r := range got {
			if position < len(script) && byte(r) == script[position] {
				position++
			}
		}
		if position != len(script) {
			t.Fatalf("observer reads %q, which does not hold %q in order", got, script)
		}
	}
}
