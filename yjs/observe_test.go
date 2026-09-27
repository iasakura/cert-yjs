//go:build !goose

package yjs

import (
	"fmt"
	"math/rand"
	"sync"
	"testing"
)

// The observer's contract, as the application sees it: an app state that
// started as "" and was patched with every Poll's delta always equals the
// text (the patch law apply_text_delta of src/proof/textobserver/model.v).

func deltaEqual(a, b []DeltaOp) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func retain(n uint64) DeltaOp  { return DeltaOp{Kind: DeltaRetain, Length: n} }
func insert(s string) DeltaOp  { return DeltaOp{Kind: DeltaInsert, Content: s} }
func deleteN(n uint64) DeltaOp { return DeltaOp{Kind: DeltaDelete, Length: n} }

func expectDelta(t *testing.T, got []DeltaOp, want ...DeltaOp) {
	t.Helper()
	if !deltaEqual(got, want) {
		t.Fatalf("delta = %v, want %v", got, want)
	}
}

// patch applies delta to app and fails the test when the patch cannot be
// applied or does not reproduce the text.
func patch(t *testing.T, app string, delta []DeltaOp, txt *Text) string {
	t.Helper()
	next, ok := ApplyDelta(app, delta)
	if !ok {
		t.Fatalf("ApplyDelta(%q, %v) failed", app, delta)
	}
	if got := txt.String(); next != got {
		t.Fatalf("patched app = %q, text = %q (delta %v)", next, got, delta)
	}
	return next
}

func TestObserverFirstPollInsertsWholeText(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("text")
	txt.Insert(0, "hello")
	obs := txt.NewObserver()
	expectDelta(t, obs.Poll(), insert("hello"))
	expectDelta(t, obs.Poll())
}

func TestObserverEmptyTextHasEmptyDelta(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("text")
	obs := txt.NewObserver()
	expectDelta(t, obs.Poll())
	txt.Insert(0, "a")
	txt.Delete(0, 1)
	// inserted and deleted between polls: never visible to this observer
	expectDelta(t, obs.Poll())
}

func TestObserverInsertsAreRetainThenInsert(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("text")
	txt.Insert(0, "ac")
	obs := txt.NewObserver()
	obs.Poll()
	txt.Insert(1, "b")
	expectDelta(t, obs.Poll(), retain(1), insert("b"))
	txt.Insert(3, "d")
	expectDelta(t, obs.Poll(), retain(3), insert("d"))
	txt.Insert(0, "_")
	expectDelta(t, obs.Poll(), insert("_"))
}

func TestObserverDeletesAreRetainThenDelete(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("text")
	txt.Insert(0, "abcd")
	obs := txt.NewObserver()
	obs.Poll()
	txt.Delete(1, 2)
	expectDelta(t, obs.Poll(), retain(1), deleteN(2))
	// the tombstones stay tombstones: nothing more to report
	expectDelta(t, obs.Poll())
	txt.Delete(0, 1)
	expectDelta(t, obs.Poll(), deleteN(1))
}

func TestObserverMixedEditsPatch(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("text")
	obs := txt.NewObserver()
	app := ""
	txt.Insert(0, "hello world")
	app = patch(t, app, obs.Poll(), txt)
	txt.Delete(5, 6)
	txt.Insert(5, ", there")
	app = patch(t, app, obs.Poll(), txt)
	txt.Insert(0, ">> ")
	txt.Delete(3, 5)
	app = patch(t, app, obs.Poll(), txt)
	if app != ">> , there" {
		t.Fatalf("app = %q", app)
	}
}

func TestObserverRemoteUpdates(t *testing.T) {
	docA := NewDoc(1)
	txtA := docA.GetOrCreateText("text")
	docB := NewDoc(2)
	txtB := docB.GetOrCreateText("text")
	obs := txtB.NewObserver()
	app := ""

	txtA.Insert(0, "hello")
	if !docB.ApplyEncodedUpdate(WireCodec(), docA.EncodeUpdate()) {
		t.Fatal("malformed update")
	}
	expectDelta(t, obs.Poll(), insert("hello"))
	app = "hello"

	txtA.Delete(1, 3) // "ell"
	txtB.Insert(5, "!")
	if !docB.ApplyEncodedUpdate(WireCodec(), docA.EncodeUpdate()) {
		t.Fatal("malformed update")
	}
	app = patch(t, app, obs.Poll(), txtB)
	if app != "ho!" {
		t.Fatalf("app = %q", app)
	}
	// the other direction: A observes B's insert
	obsA := txtA.NewObserver()
	obsA.Poll()
	if !docA.ApplyEncodedUpdate(WireCodec(), docB.EncodeUpdate()) {
		t.Fatal("malformed update")
	}
	expectDelta(t, obsA.Poll(), retain(2), insert("!"))
}

func TestApplyDeltaRejectsOverrun(t *testing.T) {
	if _, ok := ApplyDelta("ab", []DeltaOp{retain(3)}); ok {
		t.Fatal("retain past the end accepted")
	}
	if _, ok := ApplyDelta("ab", []DeltaOp{retain(1), deleteN(2)}); ok {
		t.Fatal("delete past the end accepted")
	}
	if got, ok := ApplyDelta("ab", nil); !ok || got != "ab" {
		t.Fatalf("empty delta: %q %v", got, ok)
	}
}

// randomEdit performs one random local edit on txt, keeping indices in range.
func randomEdit(r *rand.Rand, txt *Text) {
	n := txt.Len()
	if n == 0 || r.Intn(3) != 0 {
		pos := uint64(r.Intn(int(n) + 1))
		txt.Insert(pos, fmt.Sprintf("%c", 'a'+rune(r.Intn(26))))
		return
	}
	pos := uint64(r.Intn(int(n)))
	length := uint64(1 + r.Intn(int(n-pos)))
	txt.Delete(pos, length)
}

// Several observers at different polling rates over random local edits and
// remote updates in both directions: every observer's patched app equals the
// text at every poll.
func TestObserverPatchLawRandom(t *testing.T) {
	r := rand.New(rand.NewSource(198))
	docA := NewDoc(1)
	txtA := docA.GetOrCreateText("text")
	docB := NewDoc(2)
	txtB := docB.GetOrCreateText("text")
	periods := []int{1, 2, 3, 7}
	observers := make([]*TextObserver, len(periods))
	apps := make([]string, len(periods))
	for i := range periods {
		observers[i] = txtA.NewObserver()
	}
	for step := 1; step <= 400; step++ {
		switch r.Intn(4) {
		case 0, 1:
			randomEdit(r, txtA)
		case 2:
			randomEdit(r, txtB)
		case 3:
			if !docA.ApplyEncodedUpdate(WireCodec(), docB.EncodeUpdate()) {
				t.Fatal("malformed update")
			}
			if !docB.ApplyEncodedUpdate(WireCodec(), docA.EncodeUpdate()) {
				t.Fatal("malformed update")
			}
		}
		for i, period := range periods {
			if step%period == 0 {
				apps[i] = patch(t, apps[i], observers[i].Poll(), txtA)
			}
		}
	}
	if txtA.String() == "" {
		t.Fatal("degenerate run: empty text")
	}
}

// An editor goroutine racing the observer: every poll's delta patches, and
// after the editor is done one more poll brings the app to the text.
func TestObserverConcurrentEditor(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("text")
	obs := txt.NewObserver()
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		r := rand.New(rand.NewSource(7))
		for i := 0; i < 300; i++ {
			randomEdit(r, txt)
		}
	}()
	app := ""
	for i := 0; i < 50; i++ {
		next, ok := ApplyDelta(app, obs.Poll())
		if !ok {
			t.Fatalf("patch %d failed", i)
		}
		app = next
	}
	wg.Wait()
	app = patch(t, app, obs.Poll(), txt)
	if app != txt.String() {
		t.Fatalf("app = %q, text = %q", app, txt.String())
	}
}

// ---- the callback API (issue #198 Part II, C2) ----------------------------
//
// The callback's contract: told the initial text as one insert at Observe,
// then one delta per transaction that changed the text, an app state patched
// with every delta equals the text (the callback runs under the store lock,
// so a Transact that reads the app state next to StringIn sees them agree).

// recorder is a callback that keeps every delta it was told and the app state
// patched with them.
type recorder struct {
	deltas [][]DeltaOp
	app    string
	failed bool
}

func (r *recorder) callback(delta []DeltaOp) {
	r.deltas = append(r.deltas, delta)
	next, ok := ApplyDelta(r.app, delta)
	if !ok {
		r.failed = true
		return
	}
	r.app = next
}

// check compares the recorder's app state with the text inside one
// transaction, where both are stable.
func (r *recorder) check(t *testing.T, doc *Doc, txt *Text, what string) {
	t.Helper()
	doc.Transact(func(tr *Transaction) {
		if r.failed {
			t.Fatalf("%s: a delta did not apply (%v)", what, r.deltas)
		}
		if s := txt.StringIn(tr); r.app != s {
			t.Fatalf("%s: app %q, text %q (deltas %v)", what, r.app, s, r.deltas)
		}
	})
}

// TestObserveInitialAndBatched: Observe on a non-empty text is told the whole
// text first; several writes in one Transact reach it as one merged delta; a
// transaction that changes nothing is silent.
func TestObserveInitialAndBatched(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("text")
	txt.Insert(0, "hello")
	r := &recorder{}
	txt.Observe(r.callback)
	if len(r.deltas) != 1 {
		t.Fatalf("Observe called the callback %d times, want 1", len(r.deltas))
	}
	expectDelta(t, r.deltas[0], insert("hello"))
	doc.Transact(func(tr *Transaction) {
		txt.InsertIn(tr, 5, " world")
		txt.DeleteIn(tr, 0, 1)
		txt.InsertIn(tr, 0, "J")
	})
	if len(r.deltas) != 2 {
		t.Fatalf("one transaction reached the callback %d times, want 1", len(r.deltas)-1)
	}
	// the tombstoned 'h' sits before 'J' in the item order (an insert at
	// visible index 0 lands after the tombstones the walk passes)
	expectDelta(t, r.deltas[1], deleteN(1), insert("J"), retain(4), insert(" world"))
	r.check(t, doc, txt, "after the batched transaction")
	// nothing written: nothing said
	doc.Transact(func(tr *Transaction) {
		txt.InsertIn(tr, 100, "x")
		_ = txt.StringIn(tr)
	})
	if len(r.deltas) != 2 {
		t.Fatalf("a no-op transaction reached the callback")
	}
	// a char inserted and deleted in one transaction is invisible to it
	doc.Transact(func(tr *Transaction) {
		txt.InsertIn(tr, 0, "zz")
		txt.DeleteIn(tr, 0, 2)
	})
	if len(r.deltas) != 3 {
		t.Fatalf("insert-then-delete reached the callback %d times, want 1", len(r.deltas)-2)
	}
	expectDelta(t, r.deltas[2])
	r.check(t, doc, txt, "after insert-then-delete")
	// an empty observer: no initial call content
	empty := doc.GetOrCreateText("empty")
	r2 := &recorder{}
	empty.Observe(r2.callback)
	if len(r2.deltas) != 1 || len(r2.deltas[0]) != 0 {
		t.Fatalf("Observe on an empty text: %v", r2.deltas)
	}
}

// TestObserveRemoteBatchOnce: a remote batch reaches the callback once with
// the batch's delta (inserts and delete spans in one ApplySyncUpdate), a batch
// that only buffers (its dependencies missing) is silent, and the drain that
// integrates the buffered structs reports them.
func TestObserveRemoteBatchOnce(t *testing.T) {
	docA := NewDoc(1)
	txtA := docA.GetOrCreateText("text")
	txtA.Insert(0, "hello")
	txtA.Delete(1, 2) // "hlo"
	ok, structs, deletes := decodeUpdateItems(docA.EncodeUpdate())
	if !ok {
		t.Fatal("the encoded state did not decode")
	}

	docB := NewDoc(2)
	txtB := docB.GetOrCreateText("text")
	r := &recorder{}
	txtB.Observe(r.callback)
	docB.ApplySyncUpdate(structs, deletes)
	if len(r.deltas) != 2 {
		t.Fatalf("one batch reached the callback %d times, want 1", len(r.deltas)-1)
	}
	expectDelta(t, r.deltas[1], insert("hlo"))
	r.check(t, docB, txtB, "after the remote batch")

	// out of order: the tail of a run first (buffered, silent), then its head
	// (the drain integrates everything: one delta)
	docC := NewDoc(3)
	txtC := docC.GetOrCreateText("text")
	txtC.Insert(0, "abcd")
	ok, structsC, _ := decodeUpdateItems(docC.EncodeUpdate())
	if !ok || len(structsC) < 2 {
		t.Fatalf("the encoded state did not decode into several structs: %d", len(structsC))
	}
	docD := NewDoc(4)
	txtD := docD.GetOrCreateText("text")
	rD := &recorder{}
	txtD.Observe(rD.callback)
	docD.ApplySyncUpdate(structsC[1:], nil)
	if len(rD.deltas) != 1 {
		t.Fatalf("a buffered batch reached the callback: %v", rD.deltas[1:])
	}
	docD.ApplySyncUpdate(structsC[:1], nil)
	if len(rD.deltas) != 2 {
		t.Fatalf("the drain reached the callback %d times, want 1", len(rD.deltas)-1)
	}
	expectDelta(t, rD.deltas[1], insert("abcd"))
	rD.check(t, docD, txtD, "after the drain")
}

// TestObserveOtherTextSilent: editing one text leaves the other text's
// observers silent, locally and through a remote batch.
func TestObserveOtherTextSilent(t *testing.T) {
	doc := NewDoc(1)
	a := doc.GetOrCreateText("a")
	b := doc.GetOrCreateText("b")
	ra, rb := &recorder{}, &recorder{}
	a.Observe(ra.callback)
	b.Observe(rb.callback)
	a.Insert(0, "only a")
	if len(ra.deltas) != 2 || len(rb.deltas) != 1 {
		t.Fatalf("callbacks: a %d, b %d", len(ra.deltas), len(rb.deltas))
	}
	doc.Transact(func(tr *Transaction) {
		a.DeleteIn(tr, 0, 1)
		b.InsertIn(tr, 0, "b too")
	})
	if len(ra.deltas) != 3 || len(rb.deltas) != 2 {
		t.Fatalf("callbacks after both: a %d, b %d", len(ra.deltas), len(rb.deltas))
	}
	ra.check(t, doc, a, "a")
	rb.check(t, doc, b, "b")

	// remote: the batch touches a only
	docR := NewDoc(2)
	aR := docR.GetOrCreateText("a")
	bR := docR.GetOrCreateText("b")
	raR, rbR := &recorder{}, &recorder{}
	aR.Observe(raR.callback)
	bR.Observe(rbR.callback)
	docA := NewDoc(3)
	docA.GetOrCreateText("a").Insert(0, "remote a")
	ok, structs, deletes := decodeUpdateItems(docA.EncodeUpdate())
	if !ok {
		t.Fatal("the encoded state did not decode")
	}
	docR.ApplySyncUpdate(structs, deletes)
	if len(raR.deltas) != 2 || len(rbR.deltas) != 1 {
		t.Fatalf("remote callbacks: a %d, b %d", len(raR.deltas), len(rbR.deltas))
	}
	raR.check(t, docR, aR, "remote a")
}

// TestObserveMirrorRandom: a mirror patched by its callback equals the text
// after every public operation, over a random sequence, with a second
// observer registered midway (its initial call is the text at that moment).
func TestObserveMirrorRandom(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("text")
	r := &recorder{}
	txt.Observe(r.callback)
	rng := rand.New(rand.NewSource(206))
	var late *recorder
	for step := 0; step < 400; step++ {
		n := txt.Len()
		switch {
		case n > 0 && rng.Intn(3) == 0:
			at := uint64(rng.Intn(int(n)))
			count := uint64(1 + rng.Intn(int(n-at)))
			txt.Delete(at, count)
		case rng.Intn(5) == 0:
			doc.Transact(func(tr *Transaction) {
				txt.InsertIn(tr, 0, "xy")
				txt.DeleteIn(tr, 1, 1)
			})
		default:
			at := uint64(rng.Intn(int(n) + 1))
			txt.Insert(at, string(rune('a'+rng.Intn(26))))
		}
		if step == 200 {
			late = &recorder{}
			txt.Observe(late.callback)
		}
		r.check(t, doc, txt, fmt.Sprintf("step %d", step))
		if late != nil {
			late.check(t, doc, txt, fmt.Sprintf("late observer, step %d", step))
		}
	}
}

// TestObserveConcurrentEditors: editors on goroutines race Observe and the
// checks; every callback runs under the store lock, so the app state and the
// text agree inside every transaction (the race detector is the check that
// nothing else touches the app state).
func TestObserveConcurrentEditors(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("text")
	txt.Insert(0, "seed")
	var wg sync.WaitGroup
	for g := 0; g < 3; g++ {
		wg.Add(1)
		go func(seed int64) {
			defer wg.Done()
			rng := rand.New(rand.NewSource(seed))
			for i := 0; i < 150; i++ {
				doc.Transact(func(tr *Transaction) {
					s := txt.StringIn(tr)
					at := uint64(rng.Intn(len(s) + 1))
					txt.InsertIn(tr, at, "z")
					if len(s) > 4 && rng.Intn(2) == 0 {
						txt.DeleteIn(tr, 0, 2)
					}
				})
			}
		}(int64(g))
	}
	r := &recorder{}
	txt.Observe(r.callback)
	for i := 0; i < 50; i++ {
		r.check(t, doc, txt, fmt.Sprintf("concurrent check %d", i))
	}
	wg.Wait()
	r.check(t, doc, txt, "after the editors")
	if len(r.deltas) < 2 {
		t.Fatalf("the editors reached the callback %d times", len(r.deltas)-1)
	}
}

// An observer's delta carries non-ASCII bytes as they are (issue #216).
func TestObserverNonASCII(t *testing.T) {
	doc := NewDoc(1)
	txt := doc.GetOrCreateText("text")
	obs := txt.NewObserver()
	txt.Insert(0, "é")
	app := patch(t, "", obs.Poll(), txt)
	txt.Insert(1, "ü")
	patch(t, app, obs.Poll(), txt)
}
