package yjs

// Client identifies a replica; Clock is its per-client logical timestamp.
type Client = uint64
type Clock = uint64

// Id is a Lamport-style identifier: (client, clock) (y-octo: codec/id.rs).
type Id struct {
	clientId Client
	clock    Clock
}

// NewId builds an Id from a client and clock.
func NewId(client Client, clock Clock) Id {
	return Id{clientId: client, clock: clock}
}

// Add returns the id with its clock advanced by n (y-octo: impl Add for Id).
func (id Id) Add(n uint64) Id {
	return Id{clientId: id.clientId, clock: id.clock + n}
}

// Sub returns the id with its clock decreased by n (y-octo: impl Sub for Id).
func (id Id) Sub(n uint64) Id {
	return Id{clientId: id.clientId, clock: id.clock - n}
}

// Equal reports whether two ids are componentwise equal.
func (id Id) Equal(other Id) bool {
	return id.clientId == other.clientId && id.clock == other.clock
}
