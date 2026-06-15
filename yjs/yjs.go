// Package yjs is a Yjs-style CRDT implementation in Go, intended to be
// translated to Rocq with goose and verified with Perennial.
//
// The data structures and the integrate algorithm are a port of y-octo
// (https://github.com/y-crdt/y-octo), the Rust Yjs implementation by the
// Toeverything / AFFiNE team, used here under the MIT License. See the NOTICE
// file at the repository root for the full y-octo copyright and license.
package yjs

type Client = uint64
type Clock = uint64

type Id struct {
	clientId Client
	clock    Clock
}

// TODO: support more types
type Content struct {
	content string
}

type Flags = uint8

type Item struct {
	id Id
	// null means no left origin when generated
	originLeftId *Id
	// null means no right origin when generated
	originRightId *Id
	left          *Item
	right         *Item
	content       Content
	flags         Flags
}

type NodeLen struct {
	id  Id
	len uint64
}

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

type DeletedSet struct {
	deletedSet map[Client]OrderRange
}

type Store struct {
	client     Client
	items      map[Client][]Node
	deletedSet DeletedSet
}

type Doc struct {
	store *Store
}

// YText is the root sequence type the items are integrated into. In y-octo this
// is a YType with start/map/item/len; the Phase-1 simplification fixes the
// content to a single string type with no parent_sub, so we only need the head
// of the item linked list and the visible length.
type YText struct {
	// start is the head of the doubly linked list of items (parent.start).
	start *Item
	// len is the visible (countable, non-deleted) length.
	len uint64
}

// ---------------------------------------------------------------------------
// Implementation (Phase 1 foundation).
//
// These methods mirror the core data-structure operations of y-octo
// (y-crdt/y-octo, src/doc): Id arithmetic, Item length/flags, the store's
// node lookup by id, and range / delete-set membership. They are written in a
// goose-translatable subset of Go so that build.sh can emit a Rocq model and
// proofs in src/proof can reason about them.
// ---------------------------------------------------------------------------

// Item flag bits (y-octo: src/doc/codec/item_flag.rs).
const (
	ItemKeep      Flags = 0x01
	ItemCountable Flags = 0x02
	ItemDeleted   Flags = 0x04
)

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

// Len is the number of clocks the content occupies (y-octo: Content::clock_len).
func (c Content) Len() uint64 {
	return uint64(len(c.content))
}

// Len is the run length of the item (y-octo: Item::len).
func (i Item) Len() uint64 {
	return i.content.Len()
}

// LastId is the id of the item's final clock (y-octo: Item::last_id).
func (i Item) LastId() Id {
	return Id{clientId: i.id.clientId, clock: i.id.clock + i.Len() - 1}
}

// Deleted reports whether the item carries the deleted flag.
func (i Item) Deleted() bool {
	return i.flags&ItemDeleted != 0
}

// Countable reports whether the item contributes to the parent's length.
func (i Item) Countable() bool {
	return i.flags&ItemCountable != 0
}

// Indexable reports whether the item is visible in the sequence
// (y-octo: Item::indexable = countable && !deleted).
func (i Item) Indexable() bool {
	return i.Countable() && !i.Deleted()
}

// ----- Node interface methods -------------------------------------------------

func (n GCNode) nodeId() Id       { return n.nodeLen.id }
func (n GCNode) clock() Clock     { return n.nodeLen.id.clock }
func (n GCNode) length() uint64   { return n.nodeLen.len }
func (n SkipNode) nodeId() Id     { return n.nodeLen.id }
func (n SkipNode) clock() Clock   { return n.nodeLen.id.clock }
func (n SkipNode) length() uint64 { return n.nodeLen.len }
func (n ItemNode) nodeId() Id     { return n.item.id }
func (n ItemNode) clock() Clock   { return n.item.id.clock }
func (n ItemNode) length() uint64 { return n.item.Len() }

// ----- Store ------------------------------------------------------------------

// NewStore creates an empty store owned by the given client.
func NewStore(client Client) *Store {
	return &Store{
		client:     client,
		items:      make(map[Client][]Node),
		deletedSet: DeletedSet{deletedSet: make(map[Client]OrderRange)},
	}
}

// getNodeIndex finds the index of the node whose run covers clock, by binary
// search over the per-client node list (y-octo: Store::get_node_index).
func getNodeIndex(nodes []Node, clock uint64) (uint64, bool) {
	left := uint64(0)
	right := uint64(len(nodes))
	for left < right {
		middleIndex := left + (right-left)/2
		middle := nodes[middleIndex]
		middleClock := middle.clock()
		middleEnd := middleClock + middle.length()
		if clock < middleClock {
			right = middleIndex
		} else if clock >= middleEnd {
			left = middleIndex + 1
		} else {
			return middleIndex, true
		}
	}
	return 0, false
}

// GetNode returns the node containing id, if any (y-octo: Store::get_node).
func (s *Store) GetNode(id Id) (Node, bool) {
	nodes, ok := s.items[id.clientId]
	if !ok {
		return nil, false
	}
	index, found := getNodeIndex(nodes, id.clock)
	if !found {
		return nil, false
	}
	return nodes[index], true
}

// AddNode appends a node to the run list of the node's owning client.
func (s *Store) AddNode(node Node) {
	client := node.nodeId().clientId
	s.items[client] = append(s.items[client], node)
}

// ----- OrderRange / DeletedSet -----------------------------------------------

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

// ----- Doc --------------------------------------------------------------------

// NewDoc creates a document with a fresh store owned by client.
func NewDoc(client Client) *Doc {
	return &Doc{store: NewStore(client)}
}

// ---------------------------------------------------------------------------
// integrate (Phase 2): the CRDT conflict-resolution + linked-list wiring.
//
// Faithful port of y-octo Store::integrate (src/doc/store.rs) under the
// Phase-2 simplifications:
//   - content is always a 1-char string type (so an item never needs to be
//     split: len == 1, last_id == id), hence the offset>0 path is dropped;
//   - parent_sub is always None (root sequence), so the map branches are dropped;
//   - no concurrency control (single-threaded model), so the unsafe shared-ref
//     dance becomes plain pointer mutation;
//   - the parent type is never deleted.
// ---------------------------------------------------------------------------

// NewYText creates an empty root sequence.
func NewYText() *YText {
	return &YText{start: nil, len: 0}
}

// NewItem builds an item carrying 1-char string content. It is countable
// (y-octo: string content sets ITEM_COUNTABLE) and starts unlinked.
func NewItem(id Id, content string, originLeftId *Id, originRightId *Id) *Item {
	return &Item{
		id:            id,
		originLeftId:  originLeftId,
		originRightId: originRightId,
		left:          nil,
		right:         nil,
		content:       Content{content: content},
		flags:         ItemCountable,
	}
}

// idOptEqual compares two optional ids (Option<Id> in y-octo).
func idOptEqual(a *Id, b *Id) bool {
	if a == nil && b == nil {
		return true
	}
	if a == nil || b == nil {
		return false
	}
	return a.Equal(*b)
}

// itemPtrEqual compares two item references by identity. Items have unique ids,
// so identity coincides with id-equality; this matches the Somr pointer
// comparisons (conflict == right, left.right != right) in y-octo.
func itemPtrEqual(a *Item, b *Item) bool {
	if a == nil && b == nil {
		return true
	}
	if a == nil || b == nil {
		return false
	}
	return a.id.Equal(b.id)
}

// containsId reports membership in an id set represented as a slice.
func containsId(s []Id, id Id) bool {
	for _, x := range s {
		if x.Equal(id) {
			return true
		}
	}
	return false
}

// findById walks the parent's item list and returns the item with the given id,
// or nil. Because contents are 1 char, an item's last_id equals its id, so the
// origin ids resolve by exact match without splitting.
func findById(parent *YText, id Id) *Item {
	cur := parent.start
	for cur != nil {
		if cur.id.Equal(id) {
			return cur
		}
		cur = cur.right
	}
	return nil
}

// Integrate inserts item into parent, resolving origin-based conflicts the same
// way as y-octo's Store::integrate (the Yjs integrate algorithm). On return
// item is spliced into the doubly linked list at its conflict-resolved position
// and parent.len is updated.
// findIntegrationLeft scans the run of concurrent items between left and right
// and returns the conflict-resolved left anchor: the item after which `item`
// integrates (the Yjs integrate conflict resolution). It is the algorithmic
// core; it reads the document but mutates nothing, only choosing the anchor.
func findIntegrationLeft(parent *YText, item *Item, left *Item, right *Item) *Item {
	rightIsNullOrHasLeft := right == nil || right.left != nil
	leftHasOtherRightThanSelf := left != nil && !itemPtrEqual(left.right, right)

	// Walk the run of concurrent items and decide where item belongs.
	if (left == nil && rightIsNullOrHasLeft) || leftHasOtherRightThanSelf {
		var conflict *Item
		if left != nil {
			conflict = left.right
		} else {
			conflict = parent.start
		}

		conflictingItems := []Id{}
		itemsBeforeOrigin := []Id{}

		for conflict != nil {
			if itemPtrEqual(conflict, right) {
				break
			}
			conflictId := conflict.id
			itemsBeforeOrigin = append(itemsBeforeOrigin, conflictId)
			conflictingItems = append(conflictingItems, conflictId)

			if idOptEqual(item.originLeftId, conflict.originLeftId) {
				// Same left origin: the smaller client id goes first.
				if conflict.id.clientId < item.id.clientId {
					left = conflict
					conflictingItems = []Id{}
				} else if idOptEqual(item.originRightId, conflict.originRightId) {
					// Same integration points; item is to the left of conflict.
					break
				}
			} else if conflict.originLeftId != nil && containsId(itemsBeforeOrigin, *conflict.originLeftId) {
				// case 2: conflict's left origin was already scanned.
				col := *conflict.originLeftId
				if !containsId(conflictingItems, col) {
					left = conflict
					conflictingItems = []Id{}
				}
			} else {
				// conflict's left origin is before this run (or absent): the
				// origin connections would cross, so stop (matches yrs).
				break
			}

			conflict = conflict.right
		}
	}
	return left
}

func (s *Store) Integrate(parent *YText, item *Item) {
	// Resolve left/right from the origin ids (y-octo: Store::repair). With
	// 1-char contents there is no split, so this is a direct lookup.
	if item.originLeftId != nil {
		item.left = findById(parent, *item.originLeftId)
	}
	if item.originRightId != nil {
		item.right = findById(parent, *item.originRightId)
	}

	left := item.left
	right := item.right

	// Conflict resolution (the algorithmic core, extracted for verification).
	left = findIntegrationLeft(parent, item, left, right)

	// Reconnect: left <-> item <-> right.
	if left != nil {
		right = left.right
		left.right = item
		item.left = left
	} else {
		right = parent.start
		parent.start = item
		item.left = nil
	}

	if right != nil {
		right.left = item
	}
	item.right = right

	// parent_sub is None and the parent is never deleted, so item is kept and
	// (being countable) contributes to the parent length.
	if item.Countable() {
		parent.len = parent.len + item.Len()
	}
}

// Text reads the current visible string by walking the item list left to right
// (skipping deleted items). Useful for stating/verifying convergence.
func (parent *YText) Text() string {
	result := ""
	cur := parent.start
	for cur != nil {
		if !cur.Deleted() {
			result = result + cur.content.content
		}
		cur = cur.right
	}
	return result
}
