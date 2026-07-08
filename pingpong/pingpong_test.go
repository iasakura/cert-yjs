package pingpong

import (
	"bytes"
	"testing"

	"github.com/iasakura/cert-yjs/grovenet"
)

// TestPingServeOnce exercises the real TCP realization end to end: the same
// code paths the WP specs cover (Listen/Accept/Connect/Send/Receive over
// grovenet), over localhost.
func TestPingServeOnce(t *testing.T) {
	addr := grovenet.MakeAddress("127.0.0.1:42071")
	l := grovenet.Listen(addr)

	type result struct {
		err  bool
		data []byte
	}
	ch := make(chan result, 1)
	go func() {
		err, data := ServeOnce(l)
		ch <- result{err, data}
	}()

	msg := []byte("hello grove")
	if Ping(addr, msg) {
		t.Fatal("Ping reported an error")
	}
	r := <-ch
	if r.err {
		t.Fatal("ServeOnce reported an error")
	}
	if !bytes.Equal(r.data, msg) {
		t.Fatalf("echo mismatch: got %q, want %q", r.data, msg)
	}
}
