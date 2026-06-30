//go:build !goose

package yjs

// Delete-set recording for the v1 codec. The Deleted flag on each item is the
// source of truth for visibility (Text.Delete in text.go sets it and shrinks the
// visible length); the codec regenerates the store's DeleteSet from those flags
// at encode time via generateDeleteSet (codec.go), mirroring y-octo's
// store::generate_delete_set. This file holds the per-client range merge addRange
// that both the decoder and generateDeleteSet build on; it is excluded from the
// goose-translated model (//go:build !goose), keeping the verified Delete down to
// flag + visible-length updates.

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
