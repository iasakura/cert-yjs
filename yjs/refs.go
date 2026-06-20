package yjs

// nodeLen is the (id, len) summary carried by GC and Skip nodes
// (y-octo: codec/refs.rs nodeLen).
type nodeLen struct {
	id  id
	len uint64
}

// node is a struct-store entry: an item, or a GC / Skip tombstone
// (y-octo: codec/refs.rs node).
type node interface {
	isNode()
	// nodeId is the start id of the run this node represents.
	nodeId() id
	// clock is the clock component of nodeId (start of the run).
	clock() Clock
	// length is the number of clocks this node occupies.
	length() uint64
}

type gcNode struct {
	nodeLen nodeLen
}

type skipNode struct {
	nodeLen nodeLen
}

type itemNode struct {
	item item
}

func (gcNode) isNode() {}

func (skipNode) isNode() {}

func (itemNode) isNode() {}

func (n gcNode) nodeId() id       { return n.nodeLen.id }
func (n gcNode) clock() Clock     { return n.nodeLen.id.clock }
func (n gcNode) length() uint64   { return n.nodeLen.len }
func (n skipNode) nodeId() id     { return n.nodeLen.id }
func (n skipNode) clock() Clock   { return n.nodeLen.id.clock }
func (n skipNode) length() uint64 { return n.nodeLen.len }
func (n itemNode) nodeId() id     { return n.item.id }
func (n itemNode) clock() Clock   { return n.item.id.clock }
func (n itemNode) length() uint64 { return n.item.Len() }
