package wsrelay

import (
	"net"
	"testing"
	"time"

	"github.com/iasakura/cert-yjs/wsnet"
)

// freeAddr picks a port the kernel says is free and returns it as an Address.
func freeAddr(t *testing.T) wsnet.Address {
	t.Helper()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("reserving a port: %v", err)
	}
	addr := l.Addr().(*net.TCPAddr)
	if err := l.Close(); err != nil {
		t.Fatalf("closing the probe listener: %v", err)
	}
	return wsnet.MakeAddress("127.0.0.1:" + itoa(addr.Port))
}

func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	var b []byte
	for n > 0 {
		b = append([]byte{byte('0' + n%10)}, b...)
		n /= 10
	}
	return string(b)
}

// serveRoom accepts connections forever, joining each to the room and running
// its receive loop. This is the accept loop the verified server will have; it
// is written here so the relay can be exercised end to end.
func serveRoom(l wsnet.Listener, r *Room) {
	for {
		c, _ := wsnet.Accept(l)
		r.Join(c)
		go r.Serve(c)
	}
}

// TestRelayReachesTheOtherConnection is the property the room exists for: what
// one connection sends comes out on the others, and not back on itself.
func TestRelayReachesTheOtherConnection(t *testing.T) {
	addr := freeAddr(t)
	l := wsnet.Listen(addr)
	room := NewRoom()
	go serveRoom(l, room)

	errA, a := wsnet.Connect(addr, "/room")
	if errA {
		t.Fatal("client A could not connect")
	}
	errB, b := wsnet.Connect(addr, "/room")
	if errB {
		t.Fatal("client B could not connect")
	}
	// Both connections must be joined before A sends, otherwise the relay
	// legitimately has nobody to forward to.
	waitForRoomSize(t, room, 2)

	payload := []byte("hello from A")
	if wsnet.Send(a, payload) {
		t.Fatal("A could not send")
	}

	errB2, got := wsnet.Receive(b)
	if errB2 {
		t.Fatal("B received nothing")
	}
	if string(got) != string(payload) {
		t.Fatalf("B got %q, want %q", got, payload)
	}

	// A must not receive its own message back. There is no negative-receive
	// primitive, so give the relay a window and check nothing shows up.
	done := make(chan []byte, 1)
	go func() {
		err, echo := wsnet.Receive(a)
		if err {
			done <- nil
			return
		}
		done <- echo
	}()
	select {
	case echo := <-done:
		t.Fatalf("A received its own message back: %q", echo)
	case <-time.After(200 * time.Millisecond):
	}
}

// TestRelayToThreeConnections checks the fan-out reaches every other member,
// not just one.
func TestRelayToThreeConnections(t *testing.T) {
	addr := freeAddr(t)
	l := wsnet.Listen(addr)
	room := NewRoom()
	go serveRoom(l, room)

	errA, a := wsnet.Connect(addr, "/room")
	if errA {
		t.Fatal("client A could not connect")
	}
	var readers []wsnet.Connection
	for i := 0; i < 3; i++ {
		err, c := wsnet.Connect(addr, "/room")
		if err {
			t.Fatalf("reader %d could not connect", i)
		}
		readers = append(readers, c)
	}
	waitForRoomSize(t, room, 4)

	payload := []byte("to everyone")
	if wsnet.Send(a, payload) {
		t.Fatal("A could not send")
	}
	for i, c := range readers {
		err, got := wsnet.Receive(c)
		if err {
			t.Fatalf("reader %d received nothing", i)
		}
		if string(got) != string(payload) {
			t.Fatalf("reader %d got %q, want %q", i, got, payload)
		}
	}
}

// waitForRoomSize blocks until the room's table has reached n entries. Join
// happens on the server's accept loop, so a client returning from Connect does
// not yet mean it is in the table.
func waitForRoomSize(t *testing.T, r *Room, n int) {
	t.Helper()
	deadline := time.Now().Add(2 * time.Second)
	for time.Now().Before(deadline) {
		r.mu.Lock()
		size := len(r.conns)
		r.mu.Unlock()
		if size >= n {
			return
		}
		time.Sleep(2 * time.Millisecond)
	}
	t.Fatalf("room did not reach %d connections in time", n)
}
