package wsecho_test

import (
	"bufio"
	"bytes"
	"crypto/rand"
	"crypto/sha1"
	"encoding/base64"
	"fmt"
	"io"
	"net"
	"net/http"
	"strings"
	"testing"
	"time"

	"github.com/iasakura/cert-yjs/wsecho"
	"github.com/iasakura/cert-yjs/wsnet"
)

// freeAddr picks a currently unused loopback port and returns it as a wsnet
// Address.
func freeAddr(t *testing.T) (wsnet.Address, string) {
	t.Helper()
	sock, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("could not find a free port: %v", err)
	}
	hostPort := sock.Addr().String()
	sock.Close()
	return wsnet.MakeAddress(hostPort), hostPort
}

// TestEchoRoundTrip runs the verified ServeEcho against a wsnet client: the
// message comes back unchanged, which is what src/proof/demo/ws_echo.v proves about
// the model.
func TestEchoRoundTrip(t *testing.T) {
	addr, _ := freeAddr(t)
	l := wsnet.Listen(addr)
	go wsecho.ServeEcho(l)

	err, c := wsnet.Connect(addr, "/room1")
	if err {
		t.Fatal("connect failed")
	}
	payload := []byte("hello, verified world")
	if wsnet.Send(c, payload) {
		t.Fatal("send failed")
	}
	rerr, got := wsnet.Receive(c)
	if rerr {
		t.Fatal("receive failed")
	}
	if !bytes.Equal(got, payload) {
		t.Fatalf("echo mismatch: sent %q, got %q", payload, got)
	}
}

// TestAcceptReportsPath checks the model's claim that Accept hands back the
// path the peer connected to (the y-websocket room name).
func TestAcceptReportsPath(t *testing.T) {
	addr, _ := freeAddr(t)
	l := wsnet.Listen(addr)

	type accepted struct{ path string }
	done := make(chan accepted, 1)
	go func() {
		_, path := wsnet.Accept(l)
		done <- accepted{path: path}
	}()

	cerr, _ := wsnet.Connect(addr, "/my-room")
	if cerr {
		t.Fatal("connect failed")
	}
	select {
	case a := <-done:
		if a.path != "/my-room" {
			t.Fatalf("path mismatch: got %q, want %q", a.path, "/my-room")
		}
	case <-time.After(5 * time.Second):
		t.Fatal("accept did not report the connection")
	}
}

// TestEchoAgainstRawWebSocketClient talks to the server with a hand-written
// RFC 6455 client: an HTTP Upgrade handshake whose Sec-WebSocket-Accept we
// check ourselves, then one masked binary frame. This is the evidence that the
// wire format is really WebSocket rather than something only our own library
// understands, i.e. that a browser y-websocket client can connect.
func TestEchoAgainstRawWebSocketClient(t *testing.T) {
	addr, hostPort := freeAddr(t)
	l := wsnet.Listen(addr)
	go wsecho.ServeEcho(l)

	conn, err := net.Dial("tcp", hostPort)
	if err != nil {
		t.Fatalf("dial: %v", err)
	}
	defer conn.Close()
	conn.SetDeadline(time.Now().Add(10 * time.Second))

	// --- handshake ---
	var keyBytes [16]byte
	if _, err := rand.Read(keyBytes[:]); err != nil {
		t.Fatalf("rand: %v", err)
	}
	key := base64.StdEncoding.EncodeToString(keyBytes[:])
	req := fmt.Sprintf("GET /raw-room HTTP/1.1\r\n"+
		"Host: %s\r\n"+
		"Upgrade: websocket\r\n"+
		"Connection: Upgrade\r\n"+
		"Sec-WebSocket-Key: %s\r\n"+
		"Sec-WebSocket-Version: 13\r\n\r\n", hostPort, key)
	if _, err := io.WriteString(conn, req); err != nil {
		t.Fatalf("write handshake: %v", err)
	}

	br := bufio.NewReader(conn)
	resp, err := http.ReadResponse(br, nil)
	if err != nil {
		t.Fatalf("read handshake response: %v", err)
	}
	if resp.StatusCode != http.StatusSwitchingProtocols {
		t.Fatalf("status: got %d, want 101", resp.StatusCode)
	}
	if !strings.EqualFold(resp.Header.Get("Upgrade"), "websocket") {
		t.Fatalf("Upgrade header: %q", resp.Header.Get("Upgrade"))
	}
	// RFC 6455 section 4.2.2: base64(SHA-1(key ++ GUID))
	sum := sha1.Sum([]byte(key + "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"))
	want := base64.StdEncoding.EncodeToString(sum[:])
	if got := resp.Header.Get("Sec-WebSocket-Accept"); got != want {
		t.Fatalf("Sec-WebSocket-Accept: got %q, want %q", got, want)
	}

	// --- one masked binary frame out ---
	payload := []byte("raw frame payload")
	var mask [4]byte
	if _, err := rand.Read(mask[:]); err != nil {
		t.Fatalf("rand: %v", err)
	}
	frame := []byte{
		0x80 | 0x2,                // FIN, opcode = binary
		0x80 | byte(len(payload)), // MASK, payload length (short form)
	}
	frame = append(frame, mask[:]...)
	for i, b := range payload {
		frame = append(frame, b^mask[i%4])
	}
	if _, err := conn.Write(frame); err != nil {
		t.Fatalf("write frame: %v", err)
	}

	// --- the echo comes back, unmasked (server frames are never masked) ---
	var hdr [2]byte
	if _, err := io.ReadFull(br, hdr[:]); err != nil {
		t.Fatalf("read frame header: %v", err)
	}
	if hdr[0] != 0x80|0x2 {
		t.Fatalf("frame header byte 0: got %#x, want %#x", hdr[0], 0x80|0x2)
	}
	if hdr[1]&0x80 != 0 {
		t.Fatal("server frame is masked, which RFC 6455 forbids")
	}
	n := int(hdr[1] & 0x7f)
	if n != len(payload) {
		t.Fatalf("payload length: got %d, want %d", n, len(payload))
	}
	got := make([]byte, n)
	if _, err := io.ReadFull(br, got); err != nil {
		t.Fatalf("read payload: %v", err)
	}
	if !bytes.Equal(got, payload) {
		t.Fatalf("echo mismatch: sent %q, got %q", payload, got)
	}
}
