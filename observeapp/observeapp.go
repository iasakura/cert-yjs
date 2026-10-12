// Package observeapp is the application side of the observe / diff / patch
// pattern (issue #198, docs/plan-issue-198-observe.md sections 4 and 15): a
// Mirror keeps a plain sequence of code units equal to the visible text of
// the last snapshot it was told, by registering a callback on the text
// (yjs.Text.Observe) and patching its view with the delta of every
// transaction that changes the text. This is what a Yjs application does in
// its ytext.observe(event => apply(event.delta)) handler.
package observeapp

import (
	"sync"

	"github.com/iasakura/cert-yjs/yjs"
)

// Mirror is the application's copy of a text: its view, under its own lock.
// The view is UTF-16 code units, the currency of the yjs package's text API
// (yjs/content.go); it is replaced whole at every patch and never written in
// place, so a slice Text hands out stays what it was. The callback runs on
// the writer's goroutine under the document's lock (yjs.Text.Observe); Text
// may be called from anywhere.
type Mirror struct {
	mu   sync.Mutex
	doc  *yjs.Doc
	text *yjs.Text
	view []uint16
}

// NewMirror registers the mirror's callback on t. Observe tells it the
// current text first, so the view starts equal to the text; from then on
// every transaction that changes t patches the view with its delta.
func NewMirror(d *yjs.Doc, t *yjs.Text) *Mirror {
	m := &Mirror{doc: d, text: t, view: nil}
	t.Observe(func(delta []yjs.DeltaOp) {
		m.mu.Lock()
		view, ok := yjs.ApplyDelta(m.view, delta)
		if ok {
			m.view = view
		}
		m.mu.Unlock()
	})
	return m
}

// Text is the mirror's view: the visible text, as code units, of the last
// snapshot the callback was told. The slice is the mirror's own and is never
// written again; the caller must not write to it either.
func (m *Mirror) Text() []uint16 {
	m.mu.Lock()
	view := m.view
	m.mu.Unlock()
	return view
}

// equalCodeUnits reports whether two code unit sequences are the same
// sequence (slices do not compare with ==).
func equalCodeUnits(left []uint16, right []uint16) bool {
	if len(left) != len(right) {
		return false
	}
	for i := 0; i < len(left); i++ {
		if left[i] != right[i] {
			return false
		}
	}
	return true
}

// Check reads the text and the view inside one transaction and reports
// whether they agree. They always do (wp_Mirror__Check,
// src/proof/demo/observe_app.v): inside the transaction nobody else writes
// the text, and the callback has been told every earlier one. Outside a
// transaction the two reads may straddle a remote update, so no such
// guarantee is stated for m.Text() against t.CodeUnits().
func (m *Mirror) Check() bool {
	ok := false
	m.doc.Transact(func(tr *yjs.Transaction) {
		text := m.text.CodeUnitsIn(tr)
		view := m.Text()
		ok = equalCodeUnits(text, view)
	})
	return ok
}
