//go:build !goose

package yjs

// Delete and delete-set recording. Kept out of the goose-translated model for
// now (Delete is not yet part of the proof surface; the v1 codec in codec.go is
// likewise //go:build !goose). When Delete is verified, move it into text.go.

// Delete tombstones length visible characters starting at index, recording the
// deletion in the store's delete set (y-octo: ListType::remove_after via
// store::delete_item).
func (t *Text) Delete(index uint64, length uint64) {
	_, right := t.inner.findPos(index)
	remaining := length
	cur := right
	for remaining > 0 && cur != nil {
		if cur.Indexable() {
			cur.flags = cur.flags | itemDeleted
			t.inner.len = t.inner.len - cur.Len()
			t.store.deletedSet.addRange(cur.id, cur.Len())
			remaining = remaining - cur.Len()
		}
		cur = cur.right
	}
}

// addRange records [id.clock, id.clock+length) as deleted for id's client
// (y-octo: DeleteSet::add_range, without the adjacency merging).
func (d *deletedSet) addRange(id id, length uint64) {
	r := span[uint64]{start: id.clock, end: id.clock + length}
	existing, ok := d.deletedSet[id.clientId]
	if !ok {
		d.deletedSet[id.clientId] = fragmentOrderRange{fragment: []span[uint64]{r}}
		return
	}
	if frag, isFrag := existing.(fragmentOrderRange); isFrag {
		frag.fragment = append(frag.fragment, r)
		d.deletedSet[id.clientId] = frag
		return
	}
	if rr, isRange := existing.(rangeOrderRange); isRange {
		d.deletedSet[id.clientId] = fragmentOrderRange{fragment: []span[uint64]{rr.range_, r}}
	}
}
