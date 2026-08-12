package yjs

import "testing"

// deleteRange is the id-driven tombstoning the wire delete path runs
// (y-octo DocStore::delete_range); Text.Delete is its index-driven sibling.
// These tables pin the behaviours the verified spec has to reproduce: exact
// coverage of the requested clock range, idempotence, and skipping chars whose
// structs have not arrived.

func TestDeleteRangeWholeRun(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")
	txt.Insert(0, "hello")

	doc.store.mu.Lock()
	doc.store.deleteRange(1, 1, 3) // clocks 1..3 = "ell"
	doc.store.mu.Unlock()

	if got := txt.String(); got != "ho" {
		t.Fatalf("String() = %q, want %q", got, "ho")
	}
	if got := txt.Len(); got != 2 {
		t.Fatalf("Len() = %d, want 2", got)
	}
}

func TestDeleteRangeIdempotent(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")
	txt.Insert(0, "abcd")

	doc.store.mu.Lock()
	doc.store.deleteRange(1, 0, 2)
	doc.store.deleteRange(1, 0, 2) // again: no double length shrink
	doc.store.mu.Unlock()

	if got := txt.String(); got != "cd" {
		t.Fatalf("String() = %q, want %q", got, "cd")
	}
	if got := txt.Len(); got != 2 {
		t.Fatalf("Len() = %d, want 2", got)
	}
}

func TestDeleteRangeSkipsUnintegrated(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")
	txt.Insert(0, "ab")

	doc.store.mu.Lock()
	// clocks 0..4 requested, only 0..1 exist: the rest is skipped, not a panic
	doc.store.deleteRange(1, 0, 5)
	// a client with no items at all
	doc.store.deleteRange(7, 0, 3)
	doc.store.mu.Unlock()

	if got := txt.String(); got != "" {
		t.Fatalf("String() = %q, want empty", got)
	}
	if got := txt.Len(); got != 0 {
		t.Fatalf("Len() = %d, want 0", got)
	}
}

func TestDeleteRangeRemoteConverges(t *testing.T) {
	// The wire scenario: A types, B receives the structs, A deletes a range,
	// B applies the same range by id and ends up with A's text.
	docA := NewDoc(1)
	txtA := docA.GetOrCreateText("root")
	txtA.Insert(0, "hello world")

	docB := NewDoc(2)
	txtB := docB.GetOrCreateText("root")
	docB.ApplySyncUpdate(structsOf(docA, "root"), nil)

	docA.store.mu.Lock()
	docA.store.deleteRange(1, 5, 6) // " world"
	docA.store.mu.Unlock()

	docB.store.mu.Lock()
	docB.store.deleteRange(1, 5, 6)
	docB.store.mu.Unlock()

	if got, want := txtB.String(), txtA.String(); got != want {
		t.Fatalf("B = %q, A = %q", got, want)
	}
	if got := txtA.String(); got != "hello" {
		t.Fatalf("A = %q, want %q", got, "hello")
	}
}

// structsOf builds the decoded insert batch for one root of doc, in clock
// order, the way a wire update would carry it.
func structsOf(doc *Doc, name string) []updateItem {
	doc.store.mu.RLock()
	defer doc.store.mu.RUnlock()
	items := []updateItem{}
	cur := doc.store.types[name].start
	for cur != nil {
		var ol *id
		if cur.originLeftId != nil {
			v := *cur.originLeftId
			ol = &v
		}
		var or *id
		if cur.originRightId != nil {
			v := *cur.originRightId
			or = &v
		}
		nm := name
		items = append(items, updateItem{
			id:            cur.id,
			originLeftId:  ol,
			originRightId: or,
			parentName:    &nm,
			content:       cur.content.content,
		})
		cur = cur.right
	}
	return items
}
