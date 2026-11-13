package yjs

import (
	"reflect"
	"testing"
)

// plainStruct is an updateItem with its pointers followed, so that two
// structs compare by what they say.
type plainStruct struct {
	id          id
	originLeft  id
	hasLeft     bool
	originRight id
	hasRight    bool
	parentName  string
	hasParent   bool
	content     []uint16
}

func plainStructs(structs []updateItem) []plainStruct {
	result := []plainStruct{}
	for _, st := range structs {
		plain := plainStruct{id: st.id, content: append([]uint16{}, st.content...)}
		if st.originLeftId != nil {
			plain.originLeft, plain.hasLeft = *st.originLeftId, true
		}
		if st.originRightId != nil {
			plain.originRight, plain.hasRight = *st.originRightId, true
		}
		if st.parentName != nil {
			plain.parentName, plain.hasParent = *st.parentName, true
		}
		result = append(result, plain)
	}
	return result
}

// insertedStructsOf runs f as one transaction on doc and returns the structs
// the transaction integrated, read at its end.
func insertedStructsOf(doc *Doc, f func(tr *Transaction)) []updateItem {
	var structs []updateItem
	doc.Transact(func(tr *Transaction) {
		f(tr)
		structs = tr.insertedStructs()
	})
	return structs
}

// expectWireRoundTrip encodes structs with the deployment's encoder and
// decodes the bytes with the deployment's decoder: the result must be the
// given structs, and no delete span.
func expectWireRoundTrip(t *testing.T, structs []updateItem) {
	t.Helper()
	ok, decoded, deletes := WireCodec()(WireEncoder()(structs))
	if !ok {
		t.Fatal("the encoder's output does not decode")
	}
	if len(deletes) != 0 {
		t.Fatalf("decoded delete spans %v, want none", deletes)
	}
	if got, want := plainStructs(decoded), plainStructs(structs); !reflect.DeepEqual(got, want) {
		t.Fatalf("round trip:\n got %+v\nwant %+v", got, want)
	}
}

// A transaction's structs are its inserted nodes as the wire carries them:
// the first names the root, the others chain by their left origin.
func TestInsertedStructsHead(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")
	structs := insertedStructsOf(doc, func(tr *Transaction) {
		txt.InsertStringIn(tr, 0, "ab")
	})
	want := []plainStruct{
		{id: newId(1, 0), parentName: "root", hasParent: true, content: []uint16{'a'}},
		{id: newId(1, 1), originLeft: newId(1, 0), hasLeft: true, content: []uint16{'b'}},
	}
	if got := plainStructs(structs); !reflect.DeepEqual(got, want) {
		t.Fatalf("structs:\n got %+v\nwant %+v", got, want)
	}
	expectWireRoundTrip(t, structs)
}

// An insert between two characters carries both origins and no parent, and
// only the structs of this transaction are read, not the earlier ones.
func TestInsertedStructsMiddle(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")
	txt.InsertString(0, "ac")
	structs := insertedStructsOf(doc, func(tr *Transaction) {
		txt.InsertStringIn(tr, 1, "b")
	})
	want := []plainStruct{
		{id: newId(1, 2), originLeft: newId(1, 0), hasLeft: true, originRight: newId(1, 1), hasRight: true, content: []uint16{'b'}},
	}
	if got := plainStructs(structs); !reflect.DeepEqual(got, want) {
		t.Fatalf("structs:\n got %+v\nwant %+v", got, want)
	}
	expectWireRoundTrip(t, structs)
}

// A node that is split after the transaction recorded it is read back as its
// parts, which together carry the recorded ids. The multi-unit node comes
// from a remote struct; the split from a local insert inside it, in the same
// transaction.
func TestInsertedStructsSplitAfterRecord(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")
	root := "root"
	structs := insertedStructsOf(doc, func(tr *Transaction) {
		tr.applyUpdate([]updateItem{{id: newId(2, 0), parentName: &root, content: []uint16{'a', 'b', 'c'}}})
		txt.InsertStringIn(tr, 1, "X")
	})
	want := []plainStruct{
		{id: newId(2, 0), parentName: "root", hasParent: true, content: []uint16{'a'}},
		{id: newId(2, 1), originLeft: newId(2, 0), hasLeft: true, content: []uint16{'b', 'c'}},
		{id: newId(1, 0), originLeft: newId(2, 0), hasLeft: true, originRight: newId(2, 1), hasRight: true, content: []uint16{'X'}},
	}
	if got := plainStructs(structs); !reflect.DeepEqual(got, want) {
		t.Fatalf("structs:\n got %+v\nwant %+v", got, want)
	}
	if got := txt.String(); got != "aXbc" {
		t.Fatalf("text: got %q, want %q", got, "aXbc")
	}
}

// A transaction that integrates nothing has no structs, and the encoding of
// no structs decodes to no structs.
func TestInsertedStructsEmpty(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")
	structs := insertedStructsOf(doc, func(tr *Transaction) {
		txt.InsertStringIn(tr, 5, "refused: past the end")
	})
	if len(structs) != 0 {
		t.Fatalf("structs = %+v, want none", plainStructs(structs))
	}
	expectWireRoundTrip(t, structs)
}

// The encoder writes a gap in a client's clocks as a Skip, so that the
// structs after it keep their clocks, and writes clients in descending
// order, each in clock order.
func TestWireEncoderGapAndClients(t *testing.T) {
	root := "root"
	left := newId(1, 0)
	structs := []updateItem{
		{id: newId(2, 0), parentName: &root, content: []uint16{'x'}},
		{id: newId(1, 0), parentName: &root, content: []uint16{'a'}},
		{id: newId(1, 5), originLeftId: &left, content: []uint16{'b'}},
	}
	expectWireRoundTrip(t, structs)
}

// A struct whose first clock an earlier struct already covers is left out,
// so that what comes back is still made of the given structs.
func TestWireEncoderRepeatedStruct(t *testing.T) {
	root := "root"
	first := updateItem{id: newId(1, 0), parentName: &root, content: []uint16{'a', 'b'}}
	left := newId(1, 0)
	inside := updateItem{id: newId(1, 1), originLeftId: &left, content: []uint16{'b'}}
	ok, decoded, _ := WireCodec()(WireEncoder()([]updateItem{first, first, inside}))
	if !ok {
		t.Fatal("the encoder's output does not decode")
	}
	want := []plainStruct{
		{id: newId(1, 0), parentName: "root", hasParent: true, content: []uint16{'a'}},
		{id: newId(1, 1), originLeft: newId(1, 0), hasLeft: true, content: []uint16{'b'}},
	}
	if got := plainStructs(decoded); !reflect.DeepEqual(got, want) {
		t.Fatalf("decoded:\n got %+v\nwant %+v", got, want)
	}
}

// The two halves of a surrogate pair typed in one insert are two one-unit
// structs; the encoder joins them, so the pair crosses the wire as one code
// point and comes back as the same two structs.
func TestWireEncoderSurrogatePair(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")
	structs := insertedStructsOf(doc, func(tr *Transaction) {
		txt.InsertStringIn(tr, 0, "a😀b")
	})
	if len(structs) != 4 {
		t.Fatalf("%d structs, want 4 (one per code unit)", len(structs))
	}
	expectWireRoundTrip(t, structs)
}

// Two replicas that send each other every edit through InsertEncoded and
// apply what they receive through ApplyEncodedUpdate read the same text,
// whichever order the concurrent edits arrive in.
func TestInsertEncodedConverges(t *testing.T) {
	docA, docB := NewDoc(1), NewDoc(2)
	textA, textB := docA.GetOrCreateText("root"), docB.GetOrCreateText("root")
	encode, decode := WireEncoder(), WireCodec()

	first := textA.InsertEncoded(0, encodeContent("hello"), encode)
	if !docB.ApplyEncodedUpdate(decode, first) {
		t.Fatal("B: update did not decode")
	}

	// concurrent edits at the same position, delivered crosswise.
	fromA := textA.InsertEncoded(5, encodeContent(" from A"), encode)
	fromB := textB.InsertEncoded(5, encodeContent(" from B"), encode)
	// B's later edit arrives at A before the one it depends on.
	laterB := textB.InsertEncoded(0, encodeContent("😀"), encode)
	for _, update := range [][]byte{laterB, fromB} {
		if !docA.ApplyEncodedUpdate(decode, update) {
			t.Fatal("A: update did not decode")
		}
	}
	if !docB.ApplyEncodedUpdate(decode, fromA) {
		t.Fatal("B: update did not decode")
	}

	if a, b := textA.String(), textB.String(); a != b {
		t.Fatalf("diverged: A %q, B %q", a, b)
	}
	if got, want := textA.String(), "😀hello from A from B"; got != want {
		t.Fatalf("text: got %q, want %q", got, want)
	}

	// an insert that is refused sends the encoding of no structs, which
	// applies as a no-op.
	refused := textA.InsertEncoded(1000, encodeContent("x"), encode)
	if !docB.ApplyEncodedUpdate(decode, refused) {
		t.Fatal("B: the empty update did not decode")
	}
	if a, b := textA.String(), textB.String(); a != b {
		t.Fatalf("diverged after the empty update: A %q, B %q", a, b)
	}
}
