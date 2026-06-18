package yjs

// orderRange is a set of clocks for a single client, used by the delete set
// (y-octo: common/range.rs orderRange).
type orderRange interface {
	isOrderRange()
	// Contains reports whether the given clock falls inside this range.
	Contains(clock uint64) bool
}

type span[T any] struct {
	start T
	end   T
}

type rangeOrderRange struct {
	range_ span[uint64]
}

type fragmentOrderRange struct {
	fragment []span[uint64]
}

func (rangeOrderRange) isOrderRange() {}

func (fragmentOrderRange) isOrderRange() {}

// deletedSet records, per client, which clocks have been deleted
// (y-octo: codec/delete_set.rs DeleteSet).
type deletedSet struct {
	deletedSet map[Client]orderRange
}

// Contains reports whether the range covers clock (y-octo: orderRange::contains).
func (r rangeOrderRange) Contains(clock uint64) bool {
	return clock >= r.range_.start && clock < r.range_.end
}

// Contains reports whether any fragment covers clock.
func (r fragmentOrderRange) Contains(clock uint64) bool {
	for _, rng := range r.fragment {
		if clock >= rng.start && clock < rng.end {
			return true
		}
	}
	return false
}

// Contains reports whether the id is recorded as deleted
// (y-octo: DeleteSet membership).
func (d deletedSet) Contains(id id) bool {
	rng, ok := d.deletedSet[id.clientId]
	if !ok {
		return false
	}
	return rng.Contains(id.clock)
}
