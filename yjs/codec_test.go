package yjs

import "testing"

// Basic editing: insert at head, in the middle, and delete a span.
func TestTextInsertDelete(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")

	txt.Insert(0, "hello")
	if got := txt.String(); got != "hello" {
		t.Fatalf("insert head: got %q, want %q", got, "hello")
	}

	txt.Insert(2, "XY") // h e | l l o  ->  h e X Y l l o
	if got := txt.String(); got != "heXYllo" {
		t.Fatalf("insert middle: got %q, want %q", got, "heXYllo")
	}

	txt.Delete(2, 2) // remove "XY"
	if got := txt.String(); got != "hello" {
		t.Fatalf("delete: got %q, want %q", got, "hello")
	}
	if txt.Len() != 5 {
		t.Fatalf("len after delete: got %d, want 5", txt.Len())
	}
}

// Encode the whole document and decode it into a fresh one: the visible text
// and the delete set must survive the round trip exactly.
func TestUpdateRoundTrip(t *testing.T) {
	doc := NewDoc(7)
	txt := doc.GetOrCreateText("root")
	txt.Insert(0, "hello world")
	txt.Delete(5, 6) // drop " world"
	if got := txt.String(); got != "hello" {
		t.Fatalf("source text: got %q, want %q", got, "hello")
	}

	update := doc.EncodeUpdate()

	clone := NewDoc(99) // a different local client; only receives
	clone.ApplyUpdate(update)
	ct := clone.GetOrCreateText("root")
	if got := ct.String(); got != "hello" {
		t.Fatalf("round-trip text: got %q, want %q", got, "hello")
	}
	if ct.Len() != 5 {
		t.Fatalf("round-trip len: got %d, want 5", ct.Len())
	}

	// re-encoding the clone yields a document with the same observable text.
	again := NewDoc(1)
	again.ApplyUpdate(clone.EncodeUpdate())
	if got := again.GetOrCreateText("root").String(); got != "hello" {
		t.Fatalf("re-encode text: got %q, want %q", got, "hello")
	}
}

// Two root types in one document survive a round trip through a single update:
// each struct resolves its own parent on apply (issue #49).
func TestUpdateRoundTripMultipleRoots(t *testing.T) {
	doc := NewDoc(7)
	doc.GetOrCreateText("title").Insert(0, "hi")
	doc.GetOrCreateText("body").Insert(0, "yo")

	clone := NewDoc(9)
	clone.ApplyUpdate(doc.EncodeUpdate())
	if got := clone.GetOrCreateText("title").String(); got != "hi" {
		t.Fatalf("title: got %q, want %q", got, "hi")
	}
	if got := clone.GetOrCreateText("body").String(); got != "yo" {
		t.Fatalf("body: got %q, want %q", got, "yo")
	}
}

// Two clients edit the same named text concurrently, then exchange updates.
// Applying the two updates in either order must converge to the same string.
func TestConcurrentMergeConverges(t *testing.T) {
	docA := NewDoc(1)
	docA.GetOrCreateText("root").Insert(0, "abc")
	updA := docA.EncodeUpdate()

	docB := NewDoc(2)
	docB.GetOrCreateText("root").Insert(0, "xyz")
	updB := docB.EncodeUpdate()

	// A learns B; B learns A.
	docA.ApplyUpdate(updB)
	docB.ApplyUpdate(updA)

	// Fresh receivers applying the two updates in opposite orders.
	docC := NewDoc(3)
	docC.ApplyUpdate(updA)
	docC.ApplyUpdate(updB)

	docD := NewDoc(4)
	docD.ApplyUpdate(updB)
	docD.ApplyUpdate(updA)

	a := docA.GetOrCreateText("root").String()
	b := docB.GetOrCreateText("root").String()
	c := docC.GetOrCreateText("root").String()
	d := docD.GetOrCreateText("root").String()

	if a != b || a != c || a != d {
		t.Fatalf("divergence: A=%q B=%q C=%q D=%q", a, b, c, d)
	}
	if len(a) != 6 {
		t.Fatalf("merged length: got %d (%q), want 6", len(a), a)
	}
	// client 1 < client 2, so client 1's concurrent head run wins the tie.
	if a != "abcxyz" {
		t.Fatalf("merged text: got %q, want %q", a, "abcxyz")
	}
}

// Non-ASCII text is stored byte for byte (issue #216): each byte of "é" is its
// own item holding exactly that byte, so the text reads back unchanged and its
// length is its byte count.
func TestNonASCIIInsertKeepsBytes(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")
	txt.Insert(0, "héllo")
	if got := txt.String(); got != "héllo" {
		t.Fatalf("got %q, want %q", got, "héllo")
	}
	if txt.Len() != uint64(len("héllo")) {
		t.Fatalf("len: got %d, want %d", txt.Len(), len("héllo"))
	}
}

// With non-ASCII text, splitting an item and sending the document to another
// replica keep every id unique, so both replicas read the same text (issue
// #216: when a byte became two, a split gave its right half an id another item
// already had, and the replicas diverged).
func TestNonASCIIReplicasConverge(t *testing.T) {
	a := NewDoc(1)
	ta := a.GetOrCreateText("root")
	ta.Insert(0, "éa")
	ta.Delete(1, 1)
	ta.Insert(2, "z")
	b := NewDoc(2)
	b.ApplyUpdate(a.EncodeUpdate())
	if got, want := b.GetOrCreateText("root").String(), ta.String(); got != want {
		t.Fatalf("replica B reads %q, replica A reads %q", got, want)
	}
}
