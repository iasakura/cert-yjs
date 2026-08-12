package yjs

import "testing"

// applyDeleteSpans is the batch entry point of the wire delete path: it
// applies the spans it is given on top of the buffered ones and keeps the
// ones that could not land yet. These tables pin the buffering behaviour the
// spec has to reproduce.

func TestApplyDeleteSpansBuffersUncovered(t *testing.T) {
	docA := NewDoc(1)
	txtA := docA.GetOrCreateText("root")
	txtA.Insert(0, "abcd")

	docB := NewDoc(2)
	txtB := docB.GetOrCreateText("root")

	// B hears the delete of "bc" BEFORE the inserts arrive: nothing to
	// tombstone, so the span is buffered.
	docB.store.mu.Lock()
	docB.store.applyDeleteSpans([]deleteSpan{{client: 1, clock: 1, length: 2}})
	buffered := len(docB.store.pendingDeletes)
	docB.store.mu.Unlock()
	if buffered != 1 {
		t.Fatalf("pendingDeletes = %d, want 1", buffered)
	}

	// now the inserts arrive; the drain re-applies the buffered span.
	docB.ApplySyncUpdate(structsOf(docA, "root"), nil)
	docB.store.mu.Lock()
	docB.store.applyDeleteSpans(nil)
	left := len(docB.store.pendingDeletes)
	docB.store.mu.Unlock()

	if left != 0 {
		t.Fatalf("pendingDeletes = %d after the structs arrived, want 0", left)
	}
	if got := txtB.String(); got != "ad" {
		t.Fatalf("B = %q, want %q", got, "ad")
	}
}

func TestApplyDeleteSpansConverges(t *testing.T) {
	// A deletes locally, B applies the same span by id: same visible text.
	docA := NewDoc(1)
	txtA := docA.GetOrCreateText("root")
	txtA.Insert(0, "hello world")

	docB := NewDoc(2)
	txtB := docB.GetOrCreateText("root")
	docB.ApplySyncUpdate(structsOf(docA, "root"), nil)

	txtA.Delete(5, 6) // " world", clocks 5..10

	docB.store.mu.Lock()
	docB.store.applyDeleteSpans([]deleteSpan{{client: 1, clock: 5, length: 6}})
	docB.store.mu.Unlock()

	if got, want := txtB.String(), txtA.String(); got != want {
		t.Fatalf("B = %q, A = %q", got, want)
	}
	if got := txtA.String(); got != "hello" {
		t.Fatalf("A = %q, want %q", got, "hello")
	}
}

func TestApplyDeleteSpansIdempotentAcrossCalls(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("root")
	txt.Insert(0, "abc")

	span := []deleteSpan{{client: 1, clock: 0, length: 2}}
	doc.store.mu.Lock()
	doc.store.applyDeleteSpans(span)
	doc.store.applyDeleteSpans(span)
	doc.store.mu.Unlock()

	if got := txt.String(); got != "c" {
		t.Fatalf("String() = %q, want %q", got, "c")
	}
	if got := txt.Len(); got != 1 {
		t.Fatalf("Len() = %d, want 1", got)
	}
}
