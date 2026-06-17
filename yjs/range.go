package yjs

// OrderRange is a set of clocks for a single client, used by the delete set
// (y-octo: common/range.rs OrderRange).
type OrderRange interface {
	isOrderRange()
	// Contains reports whether the given clock falls inside this range.
	Contains(clock uint64) bool
}

type Range[T any] struct {
	start T
	end   T
}

type RangeOrderRange struct {
	range_ Range[uint64]
}

type FragmentOrderRange struct {
	fragment []Range[uint64]
}

func (RangeOrderRange) isOrderRange() {}

func (FragmentOrderRange) isOrderRange() {}

// DeletedSet records, per client, which clocks have been deleted
// (y-octo: codec/delete_set.rs DeleteSet).
type DeletedSet struct {
	deletedSet map[Client]OrderRange
}

// Contains reports whether the range covers clock (y-octo: OrderRange::contains).
func (r RangeOrderRange) Contains(clock uint64) bool {
	return clock >= r.range_.start && clock < r.range_.end
}

// Contains reports whether any fragment covers clock.
func (r FragmentOrderRange) Contains(clock uint64) bool {
	for _, rng := range r.fragment {
		if clock >= rng.start && clock < rng.end {
			return true
		}
	}
	return false
}

// Contains reports whether the id is recorded as deleted
// (y-octo: DeleteSet membership).
func (d DeletedSet) Contains(id Id) bool {
	rng, ok := d.deletedSet[id.clientId]
	if !ok {
		return false
	}
	return rng.Contains(id.clock)
}
