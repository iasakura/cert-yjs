package yjs

// Client identifies a replica; Clock is its per-client logical timestamp.
type Client = uint64
type Clock = uint64

// id is a Lamport-style identifier: (client, clock) (y-octo: codec/id.rs).
type id struct {
	clientId Client
	clock    Clock
}

// newId builds an id from a client and clock.
func newId(client Client, clock Clock) id {
	return id{clientId: client, clock: clock}
}

// Add returns the id with its clock advanced by n (y-octo: impl Add for id).
func (i id) Add(n uint64) id {
	return id{clientId: i.clientId, clock: i.clock + n}
}

// Sub returns the id with its clock decreased by n (y-octo: impl Sub for id).
func (i id) Sub(n uint64) id {
	return id{clientId: i.clientId, clock: i.clock - n}
}

// Equal reports whether two ids are componentwise equal.
func (i id) Equal(other id) bool {
	return i.clientId == other.clientId && i.clock == other.clock
}
