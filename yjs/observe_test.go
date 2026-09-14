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
