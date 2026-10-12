package yjs

import "testing"

// Basic editing: insert at head, in the middle, and delete a span.
func TestTextInsertDelete(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")

	txt.InsertString(0, "hello")
	if got := txt.String(); got != "hello" {
		t.Fatalf("insert head: got %q, want %q", got, "hello")
	}

	txt.InsertString(2, "XY") // h e | l l o  ->  h e X Y l l o
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
	txt.InsertString(0, "hello world")
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
	doc.GetOrCreateText("title").InsertString(0, "hi")
	doc.GetOrCreateText("body").InsertString(0, "yo")

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
	docA.GetOrCreateText("root").InsertString(0, "abc")
	updA := docA.EncodeUpdate()

	docB := NewDoc(2)
	docB.GetOrCreateText("root").InsertString(0, "xyz")
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

// Text is counted in UTF-16 code units, as Yjs counts it: "héllo" is five
// units, and a character outside the Basic Multilingual Plane is a surrogate
// pair, two units (issue #216 made the byte count exact; this is the unit
// count).
func TestInsertCountsCodeUnits(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")
	txt.InsertString(0, "héllo")
	if got := txt.String(); got != "héllo" {
		t.Fatalf("got %q, want %q", got, "héllo")
	}
	if txt.Len() != 5 {
		t.Fatalf("len: got %d, want 5", txt.Len())
	}
	txt.InsertString(5, " 😀")
	if got := txt.String(); got != "héllo 😀" {
		t.Fatalf("got %q, want %q", got, "héllo 😀")
	}
	if txt.Len() != 8 {
		t.Fatalf("len with a surrogate pair: got %d, want 8", txt.Len())
	}
	if got := txt.CodeUnits(); len(got) != 8 || got[6] != 0xD83D || got[7] != 0xDE00 {
		t.Fatalf("code units: got %x", got)
	}
}

// With non-ASCII text, splitting an item and sending the document to another
// replica keep every id unique, so both replicas read the same text (issue
// #216: when a byte became two, a split gave its right half an id another item
// already had, and the replicas diverged).
func TestNonASCIIReplicasConverge(t *testing.T) {
	a := NewDoc(1)
	ta := a.GetOrCreateText("root")
	ta.InsertString(0, "éa")
	ta.Delete(1, 1)
	ta.InsertString(1, "z")
	b := NewDoc(2)
	b.ApplyUpdate(a.EncodeUpdate())
	if got, want := b.GetOrCreateText("root").String(), ta.String(); got != want {
		t.Fatalf("replica B reads %q, replica A reads %q", got, want)
	}
}

// A surrogate pair typed locally is two one-unit items; the encoder joins
// them into one struct, so the wire carries the code point as one UTF-8
// string and a replica decodes it back into the same two units.
func TestSurrogatePairRoundTrip(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")
	txt.InsertString(0, "a😀b")
	update := doc.EncodeUpdate()
	ok, structs, _ := decodeUpdateItems(update)
	if !ok || len(structs) != 4 {
		t.Fatalf("decoded %v, %d structs, want 4 one-unit structs", ok, len(structs))
	}
	if structs[1].content[0] != 0xD83D || structs[2].content[0] != 0xDE00 {
		t.Fatalf("the pair did not survive the wire: %x %x", structs[1].content, structs[2].content)
	}
	clone := NewDoc(2)
	clone.ApplyUpdate(update)
	ct := clone.GetOrCreateText("root")
	if got := ct.String(); got != "a😀b" {
		t.Fatalf("round-trip text: got %q, want %q", got, "a😀b")
	}
	if ct.Len() != 4 {
		t.Fatalf("round-trip len: got %d, want 4", ct.Len())
	}
}

// A lone surrogate stays exact in the document and leaves on the wire as
// U+FFFD, one unit for one, so a replica agrees on every clock (the file
// comment of codec.go: Yjs replaces the halves of a split pair the same way).
func TestLoneSurrogateEncodesAsReplacement(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")
	txt.Insert(0, []uint16{0xD83D})
	if got := txt.CodeUnits(); len(got) != 1 || got[0] != 0xD83D {
		t.Fatalf("the document changed the unit: %x", got)
	}
	clone := NewDoc(2)
	clone.ApplyUpdate(doc.EncodeUpdate())
	ct := clone.GetOrCreateText("root")
	if got := ct.CodeUnits(); len(got) != 1 || got[0] != 0xFFFD {
		t.Fatalf("replica reads %x, want the replacement character", got)
	}
	// the replica's own encoding of it is stable, and converges with the source
	txt.InsertString(1, "z")
	clone.ApplyUpdate(doc.EncodeUpdate())
	doc.ApplyUpdate(clone.EncodeUpdate())
	if got := txt.Len(); got != 2 {
		t.Fatalf("source len: got %d, want 2", got)
	}
	if got := ct.String(); got != "\uFFFDz" {
		t.Fatalf("replica reads %q", got)
	}
}

// A concurrent insert between the halves of a pair splits them for good: in
// memory both replicas keep the exact units around the intruder, and on the
// wire each half, no longer joinable, becomes U+FFFD (what Yjs's
// ContentString.splice does in memory, Yjs v14.0.0-rc.18 src/structs/Item.js:1326).
func TestSplitSurrogatePairEncodesReplacements(t *testing.T) {
	a := NewDoc(1)
	ta := a.GetOrCreateText("root")
	ta.InsertString(0, "😀")
	b := NewDoc(2)
	b.ApplyUpdate(a.EncodeUpdate())
	tb := b.GetOrCreateText("root")
	tb.InsertString(1, "x")
	a.ApplyUpdate(b.EncodeUpdate())
	want := []uint16{0xD83D, 'x', 0xDE00}
	for _, txt := range []*Text{ta, tb} {
		got := txt.CodeUnits()
		if len(got) != 3 || got[0] != want[0] || got[1] != want[1] || got[2] != want[2] {
			t.Fatalf("in memory: got %x, want %x", got, want)
		}
	}
	c := NewDoc(3)
	c.ApplyUpdate(a.EncodeUpdate())
	if got := c.GetOrCreateText("root").String(); got != "\uFFFDx\uFFFD" {
		t.Fatalf("over the wire: got %q", got)
	}
	if got := c.GetOrCreateText("root").Len(); got != 3 {
		t.Fatalf("over the wire: len %d, want 3", got)
	}
}
