//go:build !goose

package yjs

import "testing"

// End-to-end wire deletes: an update encoded by the v1 codec carries its
// delete set, WireCodec decodes it, and ApplyEncodedUpdate applies both
// halves. This is the path the relay's documents run.

func TestWireCodecCarriesDeletes(t *testing.T) {
	docA := NewDoc(1)
	txtA := docA.GetOrCreateText("root")
	txtA.Insert(0, "hello world")
	txtA.Delete(5, 6) // " world"

	update := docA.EncodeUpdate()

	docB := NewDoc(2)
	txtB := docB.GetOrCreateText("root")
	if ok := docB.ApplyEncodedUpdate(WireCodec(), update); !ok {
		t.Fatal("ApplyEncodedUpdate reported a malformed update")
	}

	if got, want := txtB.String(), txtA.String(); got != want {
		t.Fatalf("B = %q, A = %q", got, want)
	}
	if got := txtB.String(); got != "hello" {
		t.Fatalf("B = %q, want %q", got, "hello")
	}
	if got := txtB.Len(); got != 5 {
		t.Fatalf("B.Len() = %d, want 5", got)
	}
}

func TestWireDeleteBeforeInsertsConverges(t *testing.T) {
	// The out-of-order case the pending buffers exist for: B hears the
	// delete-carrying update first (as a standalone update whose structs it
	// cannot integrate yet), then the inserts.
	docA := NewDoc(1)
	txtA := docA.GetOrCreateText("root")
	txtA.Insert(0, "abcd")
	inserts := docA.EncodeUpdate()

	txtA.Delete(1, 2) // "bc"
	full := docA.EncodeUpdate()

	docB := NewDoc(2)
	txtB := docB.GetOrCreateText("root")

	// deliver the delete-carrying update to a replica that has nothing yet:
	// its structs land, its spans land with them
	if ok := docB.ApplyEncodedUpdate(WireCodec(), full); !ok {
		t.Fatal("ApplyEncodedUpdate reported a malformed update")
	}
	// a re-delivery of the earlier update must not resurrect the deleted run
	if ok := docB.ApplyEncodedUpdate(WireCodec(), inserts); !ok {
		t.Fatal("ApplyEncodedUpdate reported a malformed update")
	}

	if got, want := txtB.String(), txtA.String(); got != want {
		t.Fatalf("B = %q, A = %q", got, want)
	}
	if got := txtA.String(); got != "ad" {
		t.Fatalf("A = %q, want %q", got, "ad")
	}
}
