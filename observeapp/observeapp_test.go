//go:build !goose

package observeapp

import (
	"math/rand"
	"testing"

	"github.com/iasakura/cert-yjs/yjs"
)

// TestMirrorTracksText: after every Sync the mirror spells the text, through
// inserts and deletes of every shape (the theorem of
// src/proof/demo/observe_app.v, exercised).
func TestMirrorTracksText(t *testing.T) {
	doc := yjs.NewDoc(1)
	txt := doc.GetOrCreateText("text")
	observer := txt.NewObserver()
	mirror := NewMirror()

	if !mirror.Sync(observer) || mirror.Text() != "" {
		t.Fatalf("empty sync: ok/text = %q", mirror.Text())
	}
	txt.Insert(0, "hello world")
	if !mirror.Sync(observer) || mirror.Text() != txt.String() {
		t.Fatalf("after insert: mirror %q, text %q", mirror.Text(), txt.String())
	}
	txt.Delete(5, 6)
	txt.Insert(5, ", there")
	if !mirror.Sync(observer) || mirror.Text() != txt.String() {
		t.Fatalf("after edits: mirror %q, text %q", mirror.Text(), txt.String())
	}
	// no change: an empty delta, the mirror stays
	if !mirror.Sync(observer) || mirror.Text() != txt.String() {
		t.Fatalf("idle sync: mirror %q, text %q", mirror.Text(), txt.String())
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
			txt.Insert(at, string(rune('a'+rng.Intn(26))))
		}
		if rng.Intn(4) == 0 {
			if !mirror.Sync(observer) || mirror.Text() != txt.String() {
				t.Fatalf("step %d: mirror %q, text %q", step, mirror.Text(), txt.String())
			}
		}
	}
	if !mirror.Sync(observer) || mirror.Text() != txt.String() {
		t.Fatalf("final: mirror %q, text %q", mirror.Text(), txt.String())
	}
}
