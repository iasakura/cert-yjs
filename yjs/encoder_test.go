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

// A span that begins and ends inside a node is read back as the part of the
// node it covers: its first unit takes the unit before it as left origin.
func TestAppendSpanStructsInsideNode(t *testing.T) {
	doc := NewDoc(1)
	root := "root"
	doc.Transact(func(tr *Transaction) {
		tr.applyUpdate([]updateItem{{id: newId(2, 0), parentName: &root, content: []uint16{'a', 'b', 'c', 'd'}}})
	})
	s := &doc.store.store
	structs := s.appendSpanStructs(nil, idSpan{id: newId(2, 1), len: 2})
	want := []plainStruct{
		{id: newId(2, 1), originLeft: newId(2, 0), hasLeft: true, content: []uint16{'b', 'c'}},
	}
	if got := plainStructs(structs); !reflect.DeepEqual(got, want) {
		t.Fatalf("structs:\n got %+v\nwant %+v", got, want)
	}
	whole := s.appendSpanStructs(nil, idSpan{id: newId(2, 0), len: 4})
	wantWhole := []plainStruct{
		{id: newId(2, 0), parentName: "root", hasParent: true, content: []uint16{'a', 'b', 'c', 'd'}},
	}
	if got := plainStructs(whole); !reflect.DeepEqual(got, wantWhole) {
		t.Fatalf("whole:\n got %+v\nwant %+v", got, wantWhole)
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

// Two replicas that send each other every local update their update
// observer receives and apply what they receive through ApplyEncodedUpdate
// read the same text, whichever order the concurrent edits arrive in.
func TestObserveUpdateConverges(t *testing.T) {
	docA, docB := NewDoc(1), NewDoc(2)
	textA, textB := docA.GetOrCreateText("root"), docB.GetOrCreateText("root")
	encode, decode := WireEncoder(), WireCodec()
	// A provider's use of the observer: every update is applied with the
	// origin "provider", and only the updates of other origins are sent.
	// sent holds, per document, the updates to send, in order; remote counts
	// the calls for transactions that applied an update.
	sent := map[*Doc][][]byte{}
	remote := 0
	for _, doc := range []*Doc{docA, docB} {
		doc.ObserveUpdate(encode, func(update []byte, origin Origin) {
			if origin != "provider" {
				sent[doc] = append(sent[doc], update)
			} else {
				remote++
			}
		})
	}
	// insert is one transaction that inserts content at index and returns
	// the update the observer was called with, nil if it was not called.
	insert := func(doc *Doc, text *Text, index uint64, content string) []byte {
		before := len(sent[doc])
		doc.Transact(func(tr *Transaction) {
			text.InsertIn(tr, index, encodeContent(content))
		})
		if len(sent[doc]) == before {
			return nil
		}
		return sent[doc][before]
	}

	first := insert(docA, textA, 0, "hello")
	if !docB.ApplyEncodedUpdate(decode, first, "provider") {
		t.Fatal("B: update did not decode")
	}

	// concurrent edits at the same position, delivered crosswise.
	fromA := insert(docA, textA, 5, " from A")
	fromB := insert(docB, textB, 5, " from B")
	// B's later edit arrives at A before the one it depends on.
	laterB := insert(docB, textB, 0, "😀")
	for _, update := range [][]byte{laterB, fromB} {
		if !docA.ApplyEncodedUpdate(decode, update, "provider") {
			t.Fatal("A: update did not decode")
		}
	}
	if !docB.ApplyEncodedUpdate(decode, fromA, "provider") {
		t.Fatal("B: update did not decode")
	}

	if a, b := textA.String(), textB.String(); a != b {
		t.Fatalf("diverged: A %q, B %q", a, b)
	}
	if got, want := textA.String(), "😀hello from A from B"; got != want {
		t.Fatalf("text: got %q, want %q", got, want)
	}

	// four updates were applied and three of them called the receiving
	// document's observer, with the provider's origin: B's later edit arrived at A
	// first and waited for the one before it, so its transaction integrated
	// nothing, and the next one integrated both.
	if remote != 3 {
		t.Fatalf("%d calls for applied updates, want 3", remote)
	}

	// a transaction that integrates nothing calls nobody: a refused insert,
	// and a transaction that only deletes.
	if update := insert(docA, textA, 1000, "x"); update != nil {
		t.Fatal("A: a refused insert called the observer")
	}
	calls := len(sent[docA])
	textA.Delete(0, 1)
	if len(sent[docA]) != calls {
		t.Fatal("A: a delete called the observer")
	}
}
