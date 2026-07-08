package yjs

import "testing"

// ----- verified core: state vector + diff ------------------------------------

// computeStateVector records one past each client's largest clock.
func TestComputeStateVector(t *testing.T) {
	items := []updateItem{
		mkHeadUpdateItem(1, 0, "A", "text"),
		mkUpdateItem(1, 1, "B", mkIdp(1, 0), nil),
		mkHeadUpdateItem(2, 0, "X", "text"),
	}
	sv := computeStateVector(items)
	if sv[1] != 2 {
		t.Fatalf("client 1: got %d, want 2", sv[1])
	}
	if sv[2] != 1 {
		t.Fatalf("client 2: got %d, want 1", sv[2])
	}
	if _, ok := sv[3]; ok {
		t.Fatalf("client 3 should be absent, got %d", sv[3])
	}
}

// computeDiff keeps exactly the structs at or beyond the peer's per-client clock.
func TestComputeDiffSelectsMissing(t *testing.T) {
	items := []updateItem{
		mkHeadUpdateItem(1, 0, "A", "text"), // known to peer (clock 0 < 1)
		mkUpdateItem(1, 1, "B", mkIdp(1, 0), nil),
		mkUpdateItem(1, 2, "C", mkIdp(1, 1), nil),
		mkHeadUpdateItem(2, 0, "X", "text"), // peer has none of client 2
	}
	sv := map[Client]Clock{1: 1} // peer has client 1 up to clock 0

	diff := computeDiff(items, sv)
	if len(diff) != 3 {
		t.Fatalf("diff size: got %d, want 3", len(diff))
	}
	// order preserved: B (1,1), C (1,2), X (2,0)
	want := []id{newId(1, 1), newId(1, 2), newId(2, 0)}
	for i, w := range want {
		if !diff[i].id.Equal(w) {
			t.Fatalf("diff[%d].id = %+v, want %+v", i, diff[i].id, w)
		}
	}
}

// A peer's own state vector covers its own items, so diffing against it is empty
// (the runtime counterpart of the proof's diff_of_own_state_vector_empty).
func TestComputeDiffAgainstOwnStateVectorEmpty(t *testing.T) {
	items := []updateItem{
		mkHeadUpdateItem(1, 0, "A", "text"),
		mkUpdateItem(1, 1, "B", mkIdp(1, 0), nil),
		mkHeadUpdateItem(2, 0, "X", "text"),
	}
	if diff := computeDiff(items, computeStateVector(items)); len(diff) != 0 {
		t.Fatalf("self-diff should be empty, got %d structs", len(diff))
	}
}

// ----- state vector codec ----------------------------------------------------

func TestStateVectorCodecRoundTrip(t *testing.T) {
	sv := map[Client]Clock{1: 5, 2: 0, 7: 42}
	got := readStateVector(writeStateVector(sv))
	if len(got) != len(sv) {
		t.Fatalf("size: got %d, want %d", len(got), len(sv))
	}
	for c, clk := range sv {
		if got[c] != clk {
			t.Fatalf("client %d: got %d, want %d", c, got[c], clk)
		}
	}
}

// ----- the three protocol messages, end to end ------------------------------

// Full Step1/Step2 handshake: an empty receiver learns the whole document.
func TestSyncStep1Step2Handshake(t *testing.T) {
	src := NewDoc(1)
	src.GetText("root").Insert(0, "hello")

	dst := NewDoc(2) // empty receiver

	// dst asks (Step1); src answers with the diff (Step2); dst applies it.
	step1 := dst.WriteSyncStep1()
	step2 := src.HandleSyncMessage(step1)
	if resp := dst.HandleSyncMessage(step2); resp != nil {
		t.Fatalf("applying Step2 should need no reply, got %d bytes", len(resp))
	}

	if got := dst.GetText("root").String(); got != "hello" {
		t.Fatalf("after handshake dst = %q, want %q", got, "hello")
	}
}

// Step1 from a partially-synced receiver: the diff carries only the missing
// suffix, and the receiver still converges.
func TestSyncStep1DiffIsMinimal(t *testing.T) {
	src := NewDoc(1)
	src.GetText("root").Insert(0, "hello")

	dst := NewDoc(2)
	// bring dst up to "hello" via a first handshake.
	dst.HandleSyncMessage(src.HandleSyncMessage(dst.WriteSyncStep1()))
	if got := dst.GetText("root").String(); got != "hello" {
		t.Fatalf("setup: dst = %q, want %q", got, "hello")
	}

	// src extends the document; dst now knows the "hello" prefix.
	src.GetText("root").Insert(5, "!!!")

	step2 := src.HandleSyncMessage(dst.WriteSyncStep1())
	_, payload := readDocMessage(step2)
	// the diff must not re-send the 5 "hello" structs dst already has.
	got := decodeStructCount(payload)
	if got != 3 {
		t.Fatalf("minimal diff: got %d structs, want 3 (the missing \"!!!\")", got)
	}

	dst.HandleSyncMessage(step2)
	if got := dst.GetText("root").String(); got != "hello!!!" {
		t.Fatalf("after second sync dst = %q, want %q", got, "hello!!!")
	}
}

// A full bidirectional handshake between two concurrently-edited documents
// converges both to the same text.
func TestSyncHandshakeConverges(t *testing.T) {
	a := NewDoc(1)
	a.GetText("root").Insert(0, "abc")
	b := NewDoc(2)
	b.GetText("root").Insert(0, "xyz")

	aStep1 := a.WriteSyncStep1()
	bStep1 := b.WriteSyncStep1()

	// each side answers the other's Step1, then applies the reply.
	a.HandleSyncMessage(b.HandleSyncMessage(aStep1))
	b.HandleSyncMessage(a.HandleSyncMessage(bStep1))

	ta := a.GetText("root").String()
	tb := b.GetText("root").String()
	if ta != tb {
		t.Fatalf("divergence: a = %q, b = %q", ta, tb)
	}
	if len(ta) != 6 {
		t.Fatalf("merged length: got %d (%q), want 6", len(ta), ta)
	}
	// client 1 < client 2, so client 1's concurrent head run wins the tie.
	if ta != "abcxyz" {
		t.Fatalf("merged text: got %q, want %q", ta, "abcxyz")
	}
}

// The Update message applies a broadcast v1 update.
func TestSyncUpdateMessage(t *testing.T) {
	src := NewDoc(1)
	src.GetText("root").Insert(0, "hi")

	msg := WriteUpdate(src.EncodeUpdate())

	dst := NewDoc(2)
	if resp := dst.HandleSyncMessage(msg); resp != nil {
		t.Fatalf("applying an Update should need no reply, got %d bytes", len(resp))
	}
	if got := dst.GetText("root").String(); got != "hi" {
		t.Fatalf("after Update dst = %q, want %q", got, "hi")
	}
}

// decodeStructCount counts the insert structs in a v1 update payload (test-only
// helper: peeks the clients section without integrating).
func decodeStructCount(payload []byte) int {
	d := &decoder{buf: payload}
	total := 0
	numClients := d.readVarUint()
	for c := uint64(0); c < numClients; c++ {
		numStructs := d.readVarUint()
		client := d.readVarUint()
		clock := d.readVarUint()
		for s := uint64(0); s < numStructs; s++ {
			ds := readStruct(d, client, clock)
			clock += ds.length
			total++
		}
	}
	return total
}
