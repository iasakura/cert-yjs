package yjs

// The inner root type (y-octo: YType in doc/types). In y-octo YType is
// the lock-guarded data structure (inside the Arc<RwLock<DocStore>>), while the
// YText handle lives outside the lock; we mirror that split: a yType and the
// lists reached from its [start] and its [entries] are only ever touched
// while holding store.mu, and the public handles [Text] (text.go) and [Map]
// (map.go) are the unlocked wrappers that take the lock.
//
// These methods are goose-translated (part of the verified model): findPos feeds
// the proven store.Integrate loop (and Text.Delete), so Text.Insert / Text.Delete
// preserve the document invariant is_ytype (see wp_yType__findPos / is_ytype in
// src/proof/ytype/ytype.v).

// yType is a root type the items are integrated into: a list of items and a
// map of entries by key, both in one type as in the references (Yjs
// v14.0.0-rc.18 YType._map and YType._start, src/ytype.js:653 and :657; yrs
// 0.27.2 Branch.start and Branch.map, src/branch.rs:184 and :192). Text (text.go) is a
// handle that uses the list, Map (map.go) one that uses the entries.
type yType struct {
	// start is the head of the doubly linked list of items (parent.start).
	start *item
	// len is the visible (countable, non-deleted) length of the list.
	len uint64
	// entries is, per key, the key's current entry (Yjs YType._map; yrs
	// Branch.map). The items written under one key form a doubly linked
	// list of their own, ordered by the same integration as the type's
	// list, and the entry is the last item of it: the others are deleted
	// (Transaction.integrate). The first item of that list is reached by
	// walking left from the entry (entryStart).
	entries map[string]*item
}

// newYType creates an empty root type.
func newYType() *yType {
	return &yType{start: nil, len: 0, entries: make(map[string]*item)}
}

// entryStart is the first item of the list of the items written under key,
// nil when nothing was: the current entry, walked left to the end (Yjs
// v14.0.0-rc.18 Item.integrate, src/structs/Item.js:191-195 and :245-249;
// yrs 0.27.2 src/block.rs:1040-1048 and :924, the same walk).
func (y *yType) entryStart(key string) *item {
	current := y.entries[key]
	for current != nil && current.left != nil {
		current = current.left
	}
	return current
}

// entryValue is the value of key's entry, and whether there is one: the last
// value of the current entry when it is not deleted (Yjs v14.0.0-rc.18
// typeMapGet, src/ytype.js:1860-1864; yrs 0.27.2 Branch::get,
// src/branch.rs:324-331). An entry whose content is not an any content has no
// value here, where Yjs returns the last element of whatever content it is
// (the last code unit of a string, as a string): the Go's Value is the
// encoding of an any value, and neither reference's API writes another
// content under a key.
func (y *yType) entryValue(key string) (Value, bool) {
	entry := y.entries[key]
	if entry == nil {
		return nil, false
	}
	if entry.Deleted() {
		return nil, false
	}
	values := entry.content.values
	if len(values) == 0 {
		return nil, false
	}
	return values[len(values)-1], true
}

// hasEntry reports whether key has an entry that is not deleted (Yjs
// v14.0.0-rc.18 typeMapHas, src/ytype.js:1974-1978; yrs 0.27.2
// Map::contains_key, src/types/map.rs:379).
func (y *yType) hasEntry(key string) bool {
	entry := y.entries[key]
	if entry == nil {
		return false
	}
	return !entry.Deleted()
}

// entryKeys is the keys that have an entry that is not deleted, in no
// particular order (Yjs v14.0.0-rc.18 YType.attrKeys, src/ytype.js:1426,
// iterates _map in insertion order; yrs 0.27.2 Map::keys, src/types/map.rs:168,
// a HashMap in no order).
func (y *yType) entryKeys() []string {
	var keys []string
	// The range binds the key only and looks the value up: goose translates
	// a range that binds both to a body whose value parameter is misnamed
	// (store.rootName has the same shape).
	for key := range y.entries {
		if !y.entries[key].Deleted() {
			keys = append(keys, key)
		}
	}
	return keys
}

// findPos walks to the visible index and returns the doubly-linked
// neighbours (left, right) straddling that position, plus the offset of the
// position inside [left] when it does not fall on an item boundary (yrs
// 0.27.2 find_position, src/types/text.rs:734, which splits the item there
// itself where this returns the offset; Yjs v14.0.0-rc.18 walks the retain
// that precedes an insert or a delete the same way,
// ItemTextListPosition.formatText, src/ytype.js:141).
//
// The walk starts at the head of the list with no left neighbour, advances
// through tombstones as well as visible items, moving [left] in lockstep
// with [right] (so [right == left.right] on return), spends the budget only
// on visible (Indexable) items and stops as soon as it is spent: the
// tombstones that follow the position are not passed (skipDeleted passes
// them, for an insert). When the budget lands strictly inside an item's run
// (remaining < Len), the offset into that item is recorded and the cursor
// still advances, so on return [left] is the item containing the offset and
// the caller's split rebinds left and right around the split point.
func (y *yType) findPos(index uint64) (*item, *item, uint64) {
	var left *item
	right := y.start

	remaining := index
	offset := uint64(0)
	for remaining > 0 && right != nil {
		if right.Indexable() {
			if remaining < right.Len() {
				// The index lands inside this run: record the offset and
				// stop spending (the cursor advance below makes [left] the
				// containing item).
				offset = remaining
				remaining = 0
			} else {
				remaining = remaining - right.Len()
			}
		}
		left = right
		right = right.right
	}
	return left, right, offset
}

// skipDeleted moves the position (left, right), two neighbours of one list,
// to the right past the deleted items that follow it, and returns the new
// neighbours: an insert at a position that has tombstones to its right goes
// after them. Both references do this before they create the item of a text
// insert: Yjs v14.0.0-rc.18 insertContent calls minimizeAttributeChanges
// (src/ytype.js:338 and :276), which goes right while the item to the right
// is deleted or is a format the insert already has (this package has no
// formats), and yrs 0.27.2 TextRef::insert has the loop inline
// (src/types/text.rs:219-226, "skip over deleted blocks, just like Yjs
// does"). A delete does not call it: it walks forward from the position and
// passes the tombstones itself.
func skipDeleted(left *item, right *item) (*item, *item) {
	for right != nil && right.Deleted() {
		left = right
		right = right.right
	}
	return left, right
}

// Text reads the current visible text, as UTF-16 code units, by walking the
// item list left to right and appending the content of every item that is
// not deleted (yrs 0.27.2 TextRef::get_string, src/types/text.rs:120, is the
// same walk over a String; Yjs v14.0.0-rc.18 YType.toString, src/ytype.js:1366,
// joins toArray()). The result is a fresh slice: the items' own content is
// shared and never written (content.go), so it is copied out rather than
// aliased.
func (parent *yType) Text() []uint16 {
	var result []uint16
	cur := parent.start
	for cur != nil {
		if !cur.Deleted() {
			result = append(result, cur.content.content...)
		}
		cur = cur.right
	}
	return result
}

// Snapshot walks the list and reports every character, tombstoned or not:
// the id it carries (its run's head id plus its offset in the run), its
// run's tombstone bit, and its code unit (Text.Snapshot, issue #239).
func (parent *yType) Snapshot() []SnapshotChar {
	var result []SnapshotChar
	cur := parent.start
	for cur != nil {
		deleted := cur.Deleted()
		units := cur.content.content
		for k := uint64(0); k < uint64(len(units)); k++ {
			result = append(result, SnapshotChar{
				Client:  cur.id.clientId,
				Clock:   cur.id.clock + k,
				Deleted: deleted,
				Unit:    units[k],
			})
		}
		cur = cur.right
	}
	return result
}
