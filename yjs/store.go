package yjs

// ---------------------------------------------------------------------------
// store: the document's struct store (per-client run lists + delete set) and
// the integrate algorithm.
//
// These methods mirror the core data-structure operations of y-octo
// (y-crdt/y-octo, src/doc): the store's node lookup by id and the Yjs integrate
// conflict resolution + linked-list wiring. They are written in a
// goose-translatable subset of Go so that build.sh can emit a Rocq model and
// the proofs in src/proof can reason about them.
// ---------------------------------------------------------------------------

// store is the document's struct store (y-octo: doc/store.rs DocStore).
type store struct {
	client     Client
	items      map[Client][]node
	deletedSet deletedSet
}

// newStore creates an empty store owned by the given client.
func newStore(client Client) *store {
	return &store{
		client:     client,
		items:      make(map[Client][]node),
		deletedSet: deletedSet{deletedSet: make(map[Client]orderRange)},
	}
}

// getNodeIndex finds the index of the node whose run covers clock, by binary
// search over the per-client node list (y-octo: store::get_node_index).
func getNodeIndex(nodes []node, clock uint64) (uint64, bool) {
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

// GetNode returns the node containing id, if any (y-octo: store::get_node).
func (s *store) GetNode(id id) (node, bool) {
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
func (s *store) AddNode(node node) {
	client := node.nodeId().clientId
	s.items[client] = append(s.items[client], node)
}

// idOptEqual compares two optional ids (Option<id> in y-octo).
func idOptEqual(a *id, b *id) bool {
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
func itemPtrEqual(a *item, b *item) bool {
	if a == nil && b == nil {
		return true
	}
	if a == nil || b == nil {
		return false
	}
	return a.id.Equal(b.id)
}

// containsId reports membership in an id set represented as a slice.
func containsId(s []id, id id) bool {
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
func findById(parent *yText, id id) *item {
	cur := parent.start
	for cur != nil {
		if cur.id.Equal(id) {
			return cur
		}
		cur = cur.right
	}
	return nil
}

// scanConflicts walks the run of concurrent items starting at conflict and
// updates the left anchor, stopping at right or when the origin connections
// would cross (y-octo's conflict-resolution loop). It is the operational
// counterpart of setfindIntegratedIndex; extracted from findIntegrationLeft so
// the scan can be verified against the pure set-based loop in isolation.
func scanConflicts(item *item, left *item, conflict *item, right *item) *item {
	conflictingItems := []id{}
	itemsBeforeOrigin := []id{}

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
				conflictingItems = []id{}
			} else if idOptEqual(item.originRightId, conflict.originRightId) {
				// Same integration points; item is to the left of conflict.
				break
			}
		} else if conflict.originLeftId != nil && containsId(itemsBeforeOrigin, *conflict.originLeftId) {
			// case 2: conflict's left origin was already scanned.
			col := *conflict.originLeftId
			if !containsId(conflictingItems, col) {
				left = conflict
				conflictingItems = []id{}
			}
		} else {
			// conflict's left origin is before this run (or absent): the
			// origin connections would cross, so stop (matches yrs).
			break
		}

		conflict = conflict.right
	}
	return left
}

// findIntegrationLeft scans the run of concurrent items between left and right
// and returns the conflict-resolved left anchor: the item after which `item`
// integrates (the Yjs integrate conflict resolution). It is the algorithmic
// core; it reads the document but mutates nothing, only choosing the anchor.
func findIntegrationLeft(parent *yText, it *item, left *item, right *item) *item {
	rightIsNullOrHasLeft := right == nil || right.left != nil
	leftHasOtherRightThanSelf := left != nil && !itemPtrEqual(left.right, right)

	// Walk the run of concurrent items and decide where it belongs.
	if (left == nil && rightIsNullOrHasLeft) || leftHasOtherRightThanSelf {
		var conflict *item
		if left != nil {
			conflict = left.right
		} else {
			conflict = parent.start
		}
		left = scanConflicts(it, left, conflict, right)
	}
	return left
}

// Integrate inserts item into parent, resolving origin-based conflicts the same
// way as y-octo's store::integrate (the Yjs integrate algorithm). On return
// item is spliced into the doubly linked list at its conflict-resolved position
// and parent.len is updated.
//
// Faithful port of y-octo store::integrate (src/doc/store.rs) under the
// Phase-2 simplifications:
//   - content is always a 1-char string type (so an item never needs to be
//     split: len == 1, last_id == id), hence the offset>0 path is dropped;
//   - parent_sub is always None (root sequence), so the map branches are dropped;
//   - no concurrency control (single-threaded model), so the unsafe shared-ref
//     dance becomes plain pointer mutation;
//   - the parent type is never deleted.
func (s *store) Integrate(parent *yText, item *item) {
	// Resolve left/right from the origin ids (y-octo: store::repair). With
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
