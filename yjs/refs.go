package yjs

// NodeLen is the (id, len) summary carried by GC and Skip nodes
// (y-octo: codec/refs.rs NodeLen).
type NodeLen struct {
	id  Id
	len uint64
}

// Node is a struct-store entry: an Item, or a GC / Skip tombstone
// (y-octo: codec/refs.rs Node).
type Node interface {
	isNode()
	// nodeId is the start id of the run this node represents.
	nodeId() Id
	// clock is the clock component of nodeId (start of the run).
	clock() Clock
	// length is the number of clocks this node occupies.
	length() uint64
}

type GCNode struct {
	nodeLen NodeLen
}

type SkipNode struct {
	nodeLen NodeLen
}

type ItemNode struct {
	item Item
}

func (GCNode) isNode() {}

func (SkipNode) isNode() {}

func (ItemNode) isNode() {}

func (n GCNode) nodeId() Id       { return n.nodeLen.id }
func (n GCNode) clock() Clock     { return n.nodeLen.id.clock }
func (n GCNode) length() uint64   { return n.nodeLen.len }
func (n SkipNode) nodeId() Id     { return n.nodeLen.id }
func (n SkipNode) clock() Clock   { return n.nodeLen.id.clock }
func (n SkipNode) length() uint64 { return n.nodeLen.len }
func (n ItemNode) nodeId() Id     { return n.item.id }
func (n ItemNode) clock() Clock   { return n.item.id.clock }
func (n ItemNode) length() uint64 { return n.item.Len() }
