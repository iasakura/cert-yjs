//go:build !goose

package yjs

import (
	"math/rand"
	"sync"
	"testing"
)

// The transaction's contract (docs/plan-issue-198-observe.md, Part II,
// section 13): every write inside one Transact is one unit under the store's
// write lock, StringIn reads the text as the transaction sees it, and the
// record (insertSet, deleteSet, changed) is exactly what the transaction
// integrated and tombstoned and the types it touched.

func idsOf(spans []idSpan) map[id]bool {
	ids := make(map[id]bool)
	for _, sp := range spans {
		for k := uint64(0); k < sp.len; k++ {
			ids[newId(sp.id.clientId, sp.id.clock+k)] = true
		}
	}
	return ids
}

func expectIds(t *testing.T, what string, got map[id]bool, want ...id) {
	t.Helper()
	if len(got) != len(want) {
		t.Fatalf("%s: %d ids, want %d (%v)", what, len(got), len(want), got)
	}
	for _, w := range want {
		if !got[w] {
			t.Fatalf("%s: id %v missing from %v", what, w, got)
		}
	}
}

// TestTransactBatchesWrites: several writes in one transaction land as one
// unit, and StringIn sees each of them as it happens.
func TestTransactBatchesWrites(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("text")
	doc.Transact(func(tr *Transaction) {
		txt.InsertIn(tr, 0, "hello world")
		if s := txt.StringIn(tr); s != "hello world" {
			t.Fatalf("StringIn after insert = %q", s)
		}
		txt.DeleteIn(tr, 5, 6)
		txt.InsertIn(tr, 5, ", there")
		if s := txt.StringIn(tr); s != "hello, there" {
			t.Fatalf("StringIn after edits = %q", s)
		}
	})
	if s := txt.String(); s != "hello, there" {
		t.Fatalf("String after the transaction = %q", s)
	}
}

// TestTransactionRecordsLocalWrites: the record holds exactly the ids the
// transaction integrated and tombstoned, and the types it touched.
func TestTransactionRecordsLocalWrites(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("text")
	other := doc.GetOrCreateText("other")
	txt.Insert(0, "abc") // clocks 0..2
	doc.Transact(func(tr *Transaction) {
		txt.InsertIn(tr, 3, "de") // clocks 3, 4
		txt.DeleteIn(tr, 1, 2)    // "bc": clocks 1, 2
		expectIds(t, "insertSet", idsOf(tr.insertSet), newId(1, 3), newId(1, 4))
		expectIds(t, "deleteSet", idsOf(tr.deleteSet), newId(1, 1), newId(1, 2))
		if !tr.changed[txt.inner] || tr.changed[other.inner] || len(tr.changed) != 1 {
			t.Fatalf("changed = %v, want exactly the edited text", tr.changed)
		}
	})
	// an out-of-range index, an empty delete and a read change nothing
	doc.Transact(func(tr *Transaction) {
		txt.InsertIn(tr, 100, "x")
		txt.DeleteIn(tr, 0, 0)
		_ = txt.StringIn(tr)
		if len(tr.insertSet) != 0 || len(tr.deleteSet) != 0 || len(tr.changed) != 0 {
			t.Fatalf("no-op transaction recorded %v %v %v", tr.insertSet, tr.deleteSet, tr.changed)
		}
	})
	// a char inserted and deleted in the same transaction is in both sets
	doc.Transact(func(tr *Transaction) {
		txt.InsertIn(tr, 0, "z") // clock 5
		txt.DeleteIn(tr, 0, 1)
		expectIds(t, "insertSet", idsOf(tr.insertSet), newId(1, 5))
		expectIds(t, "deleteSet", idsOf(tr.deleteSet), newId(1, 5))
	})
}

// TestTransactionRecordsRemoteBatch: a remote batch applied by
// ApplySyncUpdate is one transaction whose record covers every struct it
// integrated, every span it tombstoned, and only the types they belong to.
func TestTransactionRecordsRemoteBatch(t *testing.T) {
	docA := NewDoc(1)
	txtA := docA.GetOrCreateText("text")
	txtA.Insert(0, "hello")
	docA.GetOrCreateText("other").Insert(0, "o")
	ok, structs, deletes := decodeUpdateItems(docA.EncodeUpdate())
	if !ok {
		t.Fatal("the encoded state did not decode")
	}

	docB := NewDoc(2)
	txtB := docB.GetOrCreateText("text")
	otherB := docB.GetOrCreateText("other")
	tr := newTransaction()
	docB.store.applyUpdate(tr, structs)
	docB.store.applyDeleteSpans(tr, deletes)
	if txtB.String() != "hello" || otherB.String() != "o" {
		t.Fatalf("texts after apply: %q %q", txtB.String(), otherB.String())
	}
	expectIds(t, "insertSet", idsOf(tr.insertSet),
		newId(1, 0), newId(1, 1), newId(1, 2), newId(1, 3), newId(1, 4), newId(1, 5))
	if len(tr.deleteSet) != 0 {
		t.Fatalf("deleteSet = %v, want empty", tr.deleteSet)
	}
	if !tr.changed[txtB.inner] || !tr.changed[otherB.inner] || len(tr.changed) != 2 {
		t.Fatalf("changed = %v, want both texts", tr.changed)
	}

	// a batch of delete spans only: the record has the tombstoned ids and the
	// one type they belong to; a span for a char not yet integrated records
	// nothing and stays pending
	tr2 := newTransaction()
	docB.store.applyDeleteSpans(tr2, []deleteSpan{{client: 1, clock: 1, length: 2}, {client: 9, clock: 0, length: 1}})
	if txtB.String() != "hlo" {
		t.Fatalf("text after delete spans: %q", txtB.String())
	}
	if len(tr2.insertSet) != 0 {
		t.Fatalf("insertSet = %v, want empty", tr2.insertSet)
	}
	expectIds(t, "deleteSet", idsOf(tr2.deleteSet), newId(1, 1), newId(1, 2))
	if !tr2.changed[txtB.inner] || len(tr2.changed) != 1 {
		t.Fatalf("changed = %v, want the one text", tr2.changed)
	}
	// re-applying the same spans tombstones nothing new
	tr3 := newTransaction()
	docB.store.applyDeleteSpans(tr3, []deleteSpan{{client: 1, clock: 1, length: 2}})
	if len(tr3.deleteSet) != 0 || len(tr3.changed) != 0 {
		t.Fatalf("re-applied spans recorded %v %v", tr3.deleteSet, tr3.changed)
	}
}

// TestTransactConcurrent: transactions from several goroutines serialize
// under the store's lock (the race detector is the check), and every
// transaction sees its own writes in StringIn.
func TestTransactConcurrent(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("text")
	var wg sync.WaitGroup
	for g := 0; g < 4; g++ {
		wg.Add(1)
		go func(seed int64) {
			defer wg.Done()
			r := rand.New(rand.NewSource(seed))
			for i := 0; i < 100; i++ {
				doc.Transact(func(tr *Transaction) {
					before := txt.StringIn(tr)
					at := uint64(r.Intn(len(before) + 1))
					txt.InsertIn(tr, at, "x")
					after := txt.StringIn(tr)
					if len(after) != len(before)+1 {
						t.Errorf("transaction did not see its own insert: %q -> %q", before, after)
					}
					if len(after) > 3 {
						txt.DeleteIn(tr, 0, 2)
					}
				})
			}
		}(int64(g))
	}
	wg.Wait()
	// the public wrappers are transactions too: they interleave with Transact
	var wg2 sync.WaitGroup
	for g := 0; g < 3; g++ {
		wg2.Add(1)
		go func() {
			defer wg2.Done()
			for i := 0; i < 100; i++ {
				txt.Insert(0, "y")
				txt.Delete(0, 1)
				_ = txt.String()
			}
		}()
	}
	wg2.Wait()
}
