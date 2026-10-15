//go:build !goose

package observeapp

import (
	"math/rand"
	"testing"
	"unicode/utf16"

	"github.com/iasakura/cert-yjs/yjs"
)

// mirrorText is the mirror's view as a Go string, for the comparisons below.
func mirrorText(m *Mirror) string {
	return string(utf16.Decode(m.Text()))
}

// TestMirrorTracksText: after every transaction the mirror spells the text,
// through inserts and deletes of every shape (the theorem of
// src/proof/demo/observe_app.v, exercised). Check reads both inside one
// transaction; the plain comparison is sound here because the test is the
// only writer.
func TestMirrorTracksText(t *testing.T) {
	doc := yjs.NewDoc(1)
	txt := doc.GetOrCreateText("text")
	txt.InsertString(0, "before the mirror")
	mirror := NewMirror(doc, txt)

	if !mirror.Check() || mirrorText(mirror) != txt.String() {
		t.Fatalf("initial: mirror %q, text %q", mirrorText(mirror), txt.String())
	}
	txt.InsertString(0, "hello world ")
	if !mirror.Check() || mirrorText(mirror) != txt.String() {
		t.Fatalf("after insert: mirror %q, text %q", mirrorText(mirror), txt.String())
	}
	txt.Delete(5, 6)
	txt.InsertString(5, ", there")
	if !mirror.Check() || mirrorText(mirror) != txt.String() {
		t.Fatalf("after edits: mirror %q, text %q", mirrorText(mirror), txt.String())
	}
	// one transaction of several writes: one delta
	doc.Transact(func(tr *yjs.Transaction) {
		txt.DeleteIn(tr, 0, 3)
		txt.InsertStringIn(tr, 0, "HEL")
		txt.InsertStringIn(tr, uint64(len(txt.StringIn(tr))), "!")
	})
	if !mirror.Check() || mirrorText(mirror) != txt.String() {
		t.Fatalf("after a transaction: mirror %q, text %q", mirrorText(mirror), txt.String())
	}

	rng := rand.New(rand.NewSource(198))
	for step := 0; step < 300; step++ {
		n := txt.Len()
		if n > 0 && rng.Intn(3) == 0 {
			at := uint64(rng.Intn(int(n)))
			count := uint64(1 + rng.Intn(int(n-at)))
			txt.Delete(at, count)
		} else {
			at := uint64(rng.Intn(int(n) + 1))
			txt.InsertString(at, string(rune('a'+rng.Intn(26))))
		}
		if !mirror.Check() || mirrorText(mirror) != txt.String() {
			t.Fatalf("step %d: mirror %q, text %q", step, mirrorText(mirror), txt.String())
		}
	}
}

// The mirror stays equal to a text holding non-ASCII bytes (issue #216).
func TestMirrorTracksNonASCII(t *testing.T) {
	doc := yjs.NewDoc(1)
	txt := doc.GetOrCreateText("text")
	mirror := NewMirror(doc, txt)
	txt.InsertString(0, "héllo")
	txt.Delete(1, 1)
	if !mirror.Check() || mirrorText(mirror) != txt.String() {
		t.Fatalf("mirror %q, text %q", mirrorText(mirror), txt.String())
	}
}
