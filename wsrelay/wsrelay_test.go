package wsrelay

import (
	"net"
	"testing"
	"time"

	"github.com/iasakura/cert-yjs/wsnet"
	"github.com/iasakura/cert-yjs/yjs"
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

// startRoom brings up a server room around a fresh document and returns it
// with its address.
func startRoom(t *testing.T) (wsnet.Address, *Room, *yjs.Doc) {
	t.Helper()
	addr := freeAddr(t)
	l := wsnet.Listen(addr)
	doc := yjs.NewDoc(1)
	room := NewRoom(doc, yjs.WireCodec())
	go Run(l, room)
	return addr, room, doc
}

// TestUpdateReachesTheOtherClientAndTheServer is the property the server
// exists for: an update one client sends is applied to the server's own
// document and comes out on the other connections, and not back on itself.
func TestUpdateReachesTheOtherClientAndTheServer(t *testing.T) {
	addr, room, serverDoc := startRoom(t)

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

	docA := yjs.NewDoc(2)
	docA.GetOrCreateText("root").Insert(0, "hello")
	update := docA.EncodeUpdate()
	if wsnet.Send(a, update) {
		t.Fatal("A could not send")
	}

	// B receives the relay and applies it to its own replica.
	errB2, got := wsnet.Receive(b)
	if errB2 {
		t.Fatal("B received nothing")
	}
	docB := yjs.NewDoc(3)
	docB.ApplyUpdate(got)
	if s := docB.GetOrCreateText("root").String(); s != "hello" {
		t.Fatalf("B's replica reads %q, want %q", s, "hello")
	}

	// process applies before it relays, so B having received the relay means
	// the server's own document took the update in already.
	if s := serverDoc.GetOrCreateText("root").String(); s != "hello" {
		t.Fatalf("server document reads %q, want %q", s, "hello")
	}

	// A must not receive its own update back. There is no negative-receive
	// primitive, so give the relay a window and check nothing shows up.
	assertNothingArrives(t, a, "A received its own update back")
}

// TestFanOutReachesEveryOtherConnection checks the fan-out reaches every
// other member, not just one, and that every receiver converges.
func TestFanOutReachesEveryOtherConnection(t *testing.T) {
	addr, room, _ := startRoom(t)

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

	docA := yjs.NewDoc(2)
	docA.GetOrCreateText("root").Insert(0, "to everyone")
	update := docA.EncodeUpdate()
	if wsnet.Send(a, update) {
		t.Fatal("A could not send")
	}
	for i, c := range readers {
		err, got := wsnet.Receive(c)
		if err {
			t.Fatalf("reader %d received nothing", i)
		}
		replica := yjs.NewDoc(uint64(10 + i))
		replica.ApplyUpdate(got)
		if s := replica.GetOrCreateText("root").String(); s != "to everyone" {
			t.Fatalf("reader %d's replica reads %q, want %q", i, s, "to everyone")
		}
	}
}

// TestCrossEditsConverge sends edits from two clients and checks both
// replicas and the server converge to the same text.
func TestCrossEditsConverge(t *testing.T) {
	addr, room, serverDoc := startRoom(t)

	errA, a := wsnet.Connect(addr, "/room")
	if errA {
		t.Fatal("client A could not connect")
	}
	errB, b := wsnet.Connect(addr, "/room")
	if errB {
		t.Fatal("client B could not connect")
	}
	waitForRoomSize(t, room, 2)

	docA := yjs.NewDoc(2)
	docA.GetOrCreateText("root").Insert(0, "ab")
	if wsnet.Send(a, docA.EncodeUpdate()) {
		t.Fatal("A could not send")
	}
	errRecvB, fromA := wsnet.Receive(b)
	if errRecvB {
		t.Fatal("B did not receive A's update")
	}

	docB := yjs.NewDoc(3)
	docB.ApplyUpdate(fromA)
	docB.GetOrCreateText("root").Insert(2, "cd")
	if wsnet.Send(b, docB.EncodeUpdate()) {
		t.Fatal("B could not send")
	}
	errRecvA, fromB := wsnet.Receive(a)
	if errRecvA {
		t.Fatal("A did not receive B's update")
	}
	docA.ApplyUpdate(fromB)

	want := "abcd"
	if s := docA.GetOrCreateText("root").String(); s != want {
		t.Fatalf("A's replica reads %q, want %q", s, want)
	}
	if s := docB.GetOrCreateText("root").String(); s != want {
		t.Fatalf("B's replica reads %q, want %q", s, want)
	}
	if s := serverDoc.GetOrCreateText("root").String(); s != want {
		t.Fatalf("server document reads %q, want %q", s, want)
	}
}

// TestMalformedUpdateIsNotRelayed: a message that does not decode is neither
// applied nor forwarded, matching y-websocket (only applied updates reach
// the broadcast).
func TestMalformedUpdateIsNotRelayed(t *testing.T) {
	addr, room, serverDoc := startRoom(t)

	errA, a := wsnet.Connect(addr, "/room")
	if errA {
		t.Fatal("client A could not connect")
	}
	errB, b := wsnet.Connect(addr, "/room")
	if errB {
		t.Fatal("client B could not connect")
	}
	waitForRoomSize(t, room, 2)

	if wsnet.Send(a, []byte{0xff, 0xff, 0xff}) {
		t.Fatal("A could not send")
	}
	assertNothingArrives(t, b, "B received a relay of a malformed update")
	if s := serverDoc.GetOrCreateText("root").String(); s != "" {
		t.Fatalf("server document reads %q after a malformed update, want empty", s)
	}
}

// assertNothingArrives fails if a message shows up on c within a short
// window.
func assertNothingArrives(t *testing.T, c wsnet.Connection, msg string) {
	t.Helper()
	done := make(chan []byte, 1)
	go func() {
		err, data := wsnet.Receive(c)
		if err {
			done <- nil
			return
		}
		done <- data
	}()
	select {
	case data := <-done:
		t.Fatalf("%s: %q", msg, data)
	case <-time.After(200 * time.Millisecond):
	}
}

// waitForRoomSize blocks until the room's table has reached n entries. Join
// happens on the server's accept loop, so a client returning from Connect
// does not yet mean it is in the table.
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

// TestListenAndServeRelays boots the server through ListenAndServe, the
// exact composition the closed-system theorem verifies, and checks an
// update still relays end to end. The tests above keep handles to the room
// and the server document; this one has none, so it retries Connect until
// the goroutine's Listen is up, and A resends the (idempotent) update until
// B, whose Join may land after the first send, sees a relay.
func TestListenAndServeRelays(t *testing.T) {
	addr := freeAddr(t)
	go ListenAndServe(addr, 1, yjs.WireCodec())

	connect := func(who string) wsnet.Connection {
		for i := 0; ; i++ {
			err, c := wsnet.Connect(addr, "/room")
			if !err {
				return c
			}
			if i > 200 {
				t.Fatalf("client %s could not connect", who)
			}
			time.Sleep(10 * time.Millisecond)
		}
	}
	b := connect("B")
	a := connect("A")

	docA := yjs.NewDoc(2)
	docA.GetOrCreateText("root").Insert(0, "hello")
	update := docA.EncodeUpdate()

	got := make(chan []byte, 1)
	go func() {
		err, d := wsnet.Receive(b)
		if !err {
			got <- d
		}
	}()
	var data []byte
	for i := 0; ; i++ {
		if wsnet.Send(a, update) {
			t.Fatal("A could not send")
		}
		select {
		case data = <-got:
		case <-time.After(20 * time.Millisecond):
			if i > 200 {
				t.Fatal("no relay arrived at B")
			}
			continue
		}
		break
	}
	docB := yjs.NewDoc(3)
	docB.ApplyUpdate(data)
	if s := docB.GetOrCreateText("root").String(); s != "hello" {
		t.Fatalf("B's replica reads %q, want %q", s, "hello")
	}
}
