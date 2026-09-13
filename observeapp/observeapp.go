// Package observeapp is the application side of the observe / diff / patch
// pattern (issue #198, docs/plan-issue-198-observe.md section 4): a Mirror
// holds a plain string and keeps it equal to the visible text of the last
// snapshot it observed, by polling a TextObserver and patching with the
// delta it returns. This is what a Yjs application does in its
// ytext.observe(event => apply(event.delta)) handler; here the poll is
// explicit, so the application chooses when to catch up.
package observeapp

import "github.com/iasakura/cert-yjs/yjs"

// Mirror is the application's copy of a text.
type Mirror struct {
	text string
}

// NewMirror is a mirror of the empty text, which is what a fresh observer
// (yjs.Text.NewObserver) has observed.
func NewMirror() *Mirror {
	return &Mirror{text: ""}
}

// Sync catches the mirror up with the observer's text: one poll, one patch.
// It reports whether the patch applied; it always does for a delta the
// observer produced (the mirror was the observed text, and the delta takes
// the observed text to the current one).
func (m *Mirror) Sync(observer *yjs.TextObserver) bool {
	delta := observer.Poll()
	text, ok := yjs.ApplyDelta(m.text, delta)
	if ok {
		m.text = text
	}
	return ok
}

// Text is the mirror's current string.
func (m *Mirror) Text() string {
	return m.text
}
