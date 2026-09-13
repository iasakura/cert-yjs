package yjs

// Observing a Text incrementally (issue #198): the observe / diff / patch
// pattern an application uses to keep its own state in sync with a document.
//
// Yjs exposes it as ytext.observe(event => patch(event.delta)): YTextEvent.delta
// walks the item list and classifies every item against the transaction's
// beforeState (a state vector) and its deleteSet into insert / delete /
// retain entries. y-octo has no positional observe; its DocPublisher polls the
// store every 100 ms and hands subscribers an encoded update, keeping the
// state vector and the delete set of its last wake-up (last_update /
// last_deletes) as the token. This file is Yjs's classification driven by
// y-octo's token, pull-based: a TextObserver remembers what it observed at its
// last Poll, and the next Poll returns the Yjs delta from that snapshot to
// the current one. It is an ADDITION to the y-octo port (Yjs-derived), not a
// port of y-octo code.
//
// Verified model: src/proof/textobserver (text_delta, apply_delta,
// snapshot_grows_to and the patch law apply_text_delta).

// DeltaKind tags one entry of a text delta.
type DeltaKind = uint8

const (
	// DeltaRetain keeps the next Length chars.
	DeltaRetain DeltaKind = 0
	// DeltaInsert emits Content.
	DeltaInsert DeltaKind = 1
	// DeltaDelete drops the next Length chars.
	DeltaDelete DeltaKind = 2
)

// DeltaOp is one entry of a text delta (Yjs YTextEvent.delta, Quill's delta).
// Kind says which of Length (retain / delete) and Content (insert) is
// meaningful.
type DeltaOp struct {
	Kind    DeltaKind
	Length  uint64
	Content string
}

// TextObserver observes one Text incrementally. Its token is what y-octo's
// DocPublisher keeps between wake-ups: stateVector is, per client, one plus
// the largest clock of that client's items in the text at the last Poll
// (Yjs's beforeState); deleted holds the clock spans of the runs that were
// tombstoned at the last Poll (per client, unsorted fragments, the shape of
// y-octo's OrderRange::Fragment; deletedContains scans them). A fresh
// observer has observed nothing, so its first Poll reports the whole visible
// text as inserts.
type TextObserver struct {
	text        *Text
	stateVector map[Client]Clock
	deleted     map[Client][]span[uint64]
}

// NewObserver creates an observer of t that has observed the empty snapshot.
func (t *Text) NewObserver() *TextObserver {
	return &TextObserver{
		text:        t,
		stateVector: make(map[Client]Clock),
		deleted:     make(map[Client][]span[uint64]),
	}
}

// deletedContains reports whether the char (client, clock) was tombstoned at
// the last Poll.
func (o *TextObserver) deletedContains(client Client, clock Clock) bool {
	spans := o.deleted[client]
	for _, sp := range spans {
		if clock >= sp.start && clock < sp.end {
			return true
		}
	}
	return false
}

// deltaSnoc appends op to delta, joining it with the last entry when both are
// of one kind (the merged normal form Yjs produces).
func deltaSnoc(delta []DeltaOp, op DeltaOp) []DeltaOp {
	n := len(delta)
	if n > 0 && delta[n-1].Kind == op.Kind {
		last := delta[n-1]
		if op.Kind == DeltaInsert {
			last.Content = last.Content + op.Content
		} else {
			last.Length = last.Length + op.Length
		}
		delta[n-1] = last
		return delta
	}
	return append(delta, op)
}

// Poll returns the delta from the snapshot observed at the previous Poll (the
// empty snapshot for a fresh observer) to the text's current one, and makes
// the current snapshot the observed one. One walk of the item list under the
// store lock, classifying each char as Yjs's YTextEvent.delta does: a char
// whose clock is below the observed state vector was known; known and
// tombstoned then contributes nothing, known and tombstoned now is a delete,
// known and live is a retain; a new char is an insert when live and nothing
// when already tombstoned. Adjacent entries of one kind merge and a trailing
// retain is dropped. The walk goes char by char (a run of n chars is n
// consecutive clocks), the granularity of the verified model; a run never
// straddles the observed state vector in practice (a client's clocks arrive
// contiguously and runs never merge), but the per-char walk needs no such
// assumption.
//
// Takes the write lock, not the read lock: the proof mints the observed
// snapshot's tombstone certificate through the delete-set authority, which the
// reader side of the lock does not hold (docs/plan-issue-198-observe.md,
// section 6.2); y-octo's publisher only reads.
func (o *TextObserver) Poll() []DeltaOp {
	s := o.text.store
	s.mu.Lock()
	var delta []DeltaOp
	stateVector := make(map[Client]Clock)
	deleted := make(map[Client][]span[uint64])
	cur := o.text.inner.start
	for cur != nil {
		client := cur.id.clientId
		start := cur.id.clock
		length := cur.Len()
		end := start + length
		tombstoned := cur.Deleted()
		// the token of this poll
		if end > stateVector[client] {
			stateVector[client] = end
		}
		if tombstoned {
			deleted[client] = append(deleted[client], span[uint64]{start: start, end: end})
		}
		// the classification against the previous token, char by char
		observedEnd := o.stateVector[client]
		for i := uint64(0); i < length; i++ {
			clock := start + i
			if clock < observedEnd {
				// a known char: invisible before and after when it was
				// already tombstoned (tombstones never clear)
				if !o.deletedContains(client, clock) {
					if tombstoned {
						delta = deltaSnoc(delta, DeltaOp{Kind: DeltaDelete, Length: 1})
					} else {
						delta = deltaSnoc(delta, DeltaOp{Kind: DeltaRetain, Length: 1})
					}
				}
			} else if !tombstoned {
				delta = deltaSnoc(delta, DeltaOp{Kind: DeltaInsert, Content: string(cur.content.content[i])})
			}
		}
		cur = cur.right
	}
	o.stateVector = stateVector
	o.deleted = deleted
	s.mu.Unlock()
	// a trailing retain is implicit
	n := len(delta)
	if n > 0 && delta[n-1].Kind == DeltaRetain {
		delta = delta[:n-1]
	}
	return delta
}

// ApplyDelta patches s with delta, the application side of the pattern:
// retain copies, insert emits, delete skips, and the rest of s after the last
// entry is kept (the implicit trailing retain). It reports false, with an
// empty string, when a retain or a delete runs past the end of s.
func ApplyDelta(s string, delta []DeltaOp) (string, bool) {
	result := ""
	position := uint64(0)
	remaining := uint64(len(s))
	for _, op := range delta {
		if op.Kind == DeltaInsert {
			result = result + op.Content
		} else {
			if op.Length > remaining {
				return "", false
			}
			if op.Kind == DeltaRetain {
				for i := uint64(0); i < op.Length; i++ {
					result = result + string(s[position+i])
				}
			}
			position = position + op.Length
			remaining = remaining - op.Length
		}
	}
	for position < uint64(len(s)) {
		result = result + string(s[position])
		position = position + 1
	}
	return result, true
}
