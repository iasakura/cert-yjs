package yjs

import (
	"strings"
	"testing"
)

// itemOrder renders the text character by character in item order, a
// tombstoned character marked with '*'.
func itemOrder(text *Text) string {
	var parts []string
	for _, c := range text.Snapshot() {
		s := decodeContent([]uint16{c.Unit})
		if c.Deleted {
			s = "*" + s
		}
		parts = append(parts, s)
	}
	return strings.Join(parts, " ")
}

// TestInsertLandsAfterTombstones: an insert at a visible index whose position
// has tombstones to its right goes after them, at every index. The expected
// item orders are what Yjs 13.6.33 gives for the same edits (Y.Text insert /
// delete / insert on one document, read off the item list); yrs 0.27.2 has
// the same loop (src/types/text.rs:219-226).
func TestInsertLandsAfterTombstones(t *testing.T) {
	cases := []struct {
		initial     string
		deleteIndex uint64
		deleteLen   uint64
		insertIndex uint64
		wantOrder   string
		wantText    string
	}{
		{"ab", 0, 1, 0, "*a X b", "Xb"},
		{"abc", 1, 1, 1, "a *b X c", "aXc"},
		{"abcd", 1, 2, 1, "a *b *c X d", "aXd"},
		{"ab", 1, 1, 1, "a *b X", "aX"},
	}
	for _, c := range cases {
		doc := NewDoc(1)
		text := doc.GetOrCreateText("t")
		text.InsertString(0, c.initial)
		text.Delete(c.deleteIndex, c.deleteLen)
		text.InsertString(c.insertIndex, "X")
		if got := itemOrder(text); got != c.wantOrder {
			t.Errorf("%q, delete %d+%d, insert at %d: item order %q, want %q",
				c.initial, c.deleteIndex, c.deleteLen, c.insertIndex, got, c.wantOrder)
		}
		if got := text.String(); got != c.wantText {
			t.Errorf("%q, delete %d+%d, insert at %d: text %q, want %q",
				c.initial, c.deleteIndex, c.deleteLen, c.insertIndex, got, c.wantText)
		}
	}
}
