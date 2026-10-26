package yjs

import (
	"testing"
	"unicode/utf16"
)

// TestSnapshotReportsEveryCharWithIdsAndTombstones: Snapshot lists every
// character of the text, tombstoned ones included, with the id it carries
// (its run's head id plus its offset) and its tombstone bit, in document
// order.
func TestSnapshotReportsEveryCharWithIdsAndTombstones(t *testing.T) {
	doc := NewDoc(7)
	text := doc.GetOrCreateText("t")
	text.Insert(0, utf16.Encode([]rune("abc")))
	text.Delete(1, 1)

	got := text.Snapshot()
	want := []SnapshotChar{
		{Client: 7, Clock: 0, Deleted: false, Unit: 'a'},
		{Client: 7, Clock: 1, Deleted: true, Unit: 'b'},
		{Client: 7, Clock: 2, Deleted: false, Unit: 'c'},
	}
	if len(got) != len(want) {
		t.Fatalf("Snapshot() = %v, want %v", got, want)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Fatalf("Snapshot()[%d] = %v, want %v", i, got[i], want[i])
		}
	}
	if s := string(utf16.Decode(text.CodeUnits())); s != "ac" {
		t.Fatalf("CodeUnits() = %q, want %q", s, "ac")
	}
}
