package yjs

import "sync"

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

// store is the document's struct store (y-octo: doc/store.rs DocStore). Like
// y-octo's Arc<RwLock<DocStore>>, the store carries everything mutable and
// shared: the lock, the local client's next clock, the per-client run lists, the
// root-type registry, and the delete set. The Doc is just a handle around it.
type store struct {
	// mu guards every other field (and the YTypes' DLLs reached via types):
	// y-octo's RwLock<DocStore>. Writers (Insert/Delete/GetOrCreateText/apply_update)
	// take the write lock (Lock); pure readers (String/Len) take the read lock
	// (RLock) so concurrent reads are allowed, matching Arc<RwLock<DocStore>>.
	mu sync.RWMutex
	// client is the local replica id.
	client Client
	// clock is the next clock for the local client (state-vector head). Each
	// local insert consumes one and bumps it, making generated ids maximal.
	clock Clock
	// items is the per-client run list of every integrated item (y-octo:
	// DocStore.items HashMap<Client, Vec<Node>>); the verified path only ever
	// stores items, so the element type is *item shared with the DLL.
	items map[Client][]*item
	// types is the root-type registry by name (y-octo: DocStore.types).
	types      map[string]*yType
	deletedSet deletedSet
	// pending buffers decoded structs whose dependencies have not arrived yet
	// (y-octo: DocStore.pending Option<Update>); every later applyUpdate
	// re-drains it. Deliberate container deviation from y-octo (reported):
	// y-octo keeps per-client queues (Update.structs
	// ClientMap<VecDeque<Node>>) while this is the decoded flat batch shape
	// store.applyUpdate already consumes; the flattening preserves each
	// client's clock order (see docs/plan-issue-40-pending.md, section 3).
	pending []updateItem
	// pendingDeletes buffers delete spans that were not fully covered when
	// they arrived: their target structs have not been integrated yet
	// (y-octo keeps the whole delete set and re-checks it; ours keeps only
	// the uncovered remainder, mirroring the pending-struct discipline of
	// issue #40). Every later applyDeleteSpans re-drains it, which is sound
	// because tombstoning is idempotent.
	pendingDeletes []deleteSpan
	// observers is, per type, the callbacks Text.Observe registered (issue
	// #198, Part II). The three references keep them in three places: Yjs
	// v14 on the type (YType._eH, src/ytype.js:667), yrs 0.27 on the branch
	// (Branch.observers, src/branch.rs:214), y-octo on a per-document
	// publisher that polls the store (DocPublisher, src/doc/publisher.rs:15).
	// Here they sit on the store, keyed by type, so that the pool's type
	// cells, the heaviest proof machinery, keep their shape (a divergence,
	// docs/plan-issue-198-observe.md section 18). Guarded by mu; notify walks
	// it at the end of every transaction.
	observers map[*yType][]func(delta []DeltaOp)
}

// newStore creates an empty store owned by the given client.
func newStore(client Client) *store {
	return &store{
		client:         client,
		clock:          0,
		items:          make(map[Client][]*item),
		types:          make(map[string]*yType),
		deletedSet:     deletedSet{deletedSet: make(map[Client]orderRange)},
		pending:        nil,
		pendingDeletes: nil,
		observers:      make(map[*yType][]func(delta []DeltaOp)),
	}
}

// getOrCreateYType returns the internal sequence for name, creating it on first
// use (y-octo: DocStore::get_or_create_type). Callers hold s.mu.
func (s *store) getOrCreateYType(name string) *yType {
	y, ok := s.types[name]
	if !ok {
		y = newYType()
		s.types[name] = y
	}
	return y
}

// getNodeIndex finds the index of the node whose run covers clock, by binary
// search over the per-client node list (y-octo: store::get_node_index).
func getNodeIndex(nodes []*item, clock uint64) (uint64, bool) {
	left := uint64(0)
	right := uint64(len(nodes))
	for left < right {
		middleIndex := left + (right-left)/2
		middle := nodes[middleIndex]
		middleClock := middle.id.clock
		middleEnd := middleClock + middle.Len()
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

// GetNode returns the item containing id, if any (y-octo: store::get_node). The
// verified store only holds items, so this returns *item directly.
func (s *store) GetNode(id id) (*item, bool) {
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

// addNode appends an item to the run list of its owning client (y-octo:
// store::add_item), so the store holds the full item set. Takes the items
// map instead of being a *store method as in y-octo (whose &mut self
// borrows the whole store either way): it touches nothing else of the
// store, and the footprint must be visible in the program (CLAUDE.md
// "Spec shape").
func addNode(items map[Client][]*item, it *item) {
	client := it.id.clientId
	items[client] = append(items[client], it)
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

// idSpan is one scanned node's id range: the clock interval
// [id.clock, id.clock+len) of the node's run, at the node's client.
//
// yjs keeps item REFERENCES in itemsBeforeOrigin / conflictingItems and
// resolves origin membership through getItem (an id addresses ANY char of an
// item's run), so membership is clock-range membership. y-octo instead stores
// raw head ids and tests raw-id equality (HashSet<Id>::contains), which
// misses an origin pointing into the middle of a multi-char run (candidate
// upstream bug, see docs/plan-issue-28-runs-split.md); Cert-Yjs follows the
// yjs semantics. The (head id, run length) span carries exactly what the
// range test needs without holding an item reference.
type idSpan struct {
	id  id
	len uint64
}

// containsId reports whether id addresses a char of any span in s
// (yjs: getItem semantics).
func containsId(s []idSpan, id id) bool {
	for _, x := range s {
		if x.id.clientId == id.clientId && x.id.clock <= id.clock && id.clock < x.id.clock+x.len {
			return true
		}
	}
	return false
}

// splitNode splits the run node n at offset diff (0 < diff < n.Len()) into
// (left, right) (y-octo: DocStore::split_node_at): the original node is
// truncated in place to its first diff clocks and a fresh right node covering
// the rest is spliced after it in the doubly linked list and inserted into the
// per-client run list right after n. The right node's left origin is the last
// id of the truncated left half and its right origin is copied from n, so the
// split is invisible to the per-char document (yjs: splitItem).
//
// The right half INHERITS the deleted flag: this deliberately diverges from
// y-octo, whose Item::split_at drops the deleted/keep bits of the right half
// (its inheritance block is a tautological self-check on the freshly built
// halves; yjs's splitItem and yrs's ItemPtr::splice both inherit). Dropping
// the bit resurrects tombstoned content when repair splits a deleted run
// (candidate upstream bug, see docs/plan-issue-28-runs-split.md).
func (s *store) splitNode(n *item, diff uint64) (*item, *item) {
	right := splitItem(n, diff)
	// Insert the right node into the client's run list just after n
	// (y-octo: items.insert(index + 1, right)), keeping it clock-sorted.
	// Built by appending the prefix, the new node, and the suffix into a
	// fresh nil slice (rather than the in-place grow+copy+set idiom, or a
	// pre-sized make): every copy is between DISJOINT backing arrays, and
	// unlike make(len+1) the appends carry no slice-length-fit side
	// condition (goose models append's growth with an overflow assume, the
	// same way addNode's append is handled), so callers such as
	// Text.Delete's range-end split need no externally supplied capacity
	// bound. Same result as items.insert(index+1, right).
	nodes := s.items[n.id.clientId]
	index, _ := getNodeIndex(nodes, n.id.clock)
	var newNodes []*item
	newNodes = append(newNodes, nodes[:index+1]...)
	newNodes = append(newNodes, right)
	newNodes = append(newNodes, nodes[index+1:]...)
	s.items[n.id.clientId] = newNodes
	return n, right
}

// splitItem splits the run node n at offset diff (0 < diff < n.Len()) in
// its type's doubly linked list (y-octo: Item::split_at, the node half of
// DocStore::split_node_at): n is truncated in place to its first diff clocks
// and the fresh right node covering the rest is spliced after it, its left
// origin the last id of the truncated half and its right origin copied from
// n. A free function, not a *store method: it touches only the node and its
// neighbours, and the footprint must be visible in the program (CLAUDE.md
// "Spec shape"); splitNode adds the per-client run-list insertion.
func splitItem(n *item, diff uint64) *item {
	olid := newId(n.id.clientId, n.id.clock+diff-1)
	// Split the content through a []byte round-trip rather than slicing the
	// string directly: Perennial's goose model has no reduction for slicing a
	// Go string (Slice go.string), whereas byte-slice slicing steps normally
	// (same reason Insert uses string(content[i]) instead of content[i:i+1]).
	cb := []byte(n.content.content)
	right := &item{
		id:            newId(n.id.clientId, n.id.clock+diff),
		originLeftId:  &olid,
		originRightId: n.originRightId,
		left:          n,
		right:         n.right,
		parent:        n.parent,
		content:       content{content: string(cb[diff:])},
		flags:         n.flags,
	}
	n.content = content{content: string(cb[:diff])}
	if n.right != nil {
		n.right.left = right
	}
	n.right = right
	return right
}

// splitAtAndGetLeft returns the node ENDING exactly at id (y-octo:
// DocStore::split_at_and_get_left): when id falls before the last clock of
// its node, the node is split just after id and the left half is returned.
// Resolves a decoded item's LEFT origin, which names the element it sits
// after (clean-end semantics, yjs: getItemCleanEnd).
func (s *store) splitAtAndGetLeft(id id) (*item, bool) {
	n, ok := s.GetNode(id)
	if !ok {
		return nil, false
	}
	offset := id.clock - n.id.clock
	if offset != n.Len()-1 {
		left, _ := s.splitNode(n, offset+1)
		return left, true
	}
	return n, true
}

// splitAtAndGetRight returns the node STARTING exactly at id (y-octo:
// DocStore::split_at_and_get_right): when id falls inside its node, the node
// is split at id and the right half is returned. Resolves a decoded item's
// RIGHT origin, which names the element it sits before (clean-start
// semantics, yjs: getItemCleanStart).
func (s *store) splitAtAndGetRight(id id) (*item, bool) {
	n, ok := s.GetNode(id)
	if !ok {
		return nil, false
	}
	offset := id.clock - n.id.clock
	if offset > 0 {
		_, right := s.splitNode(n, offset)
		return right, true
	}
	return n, true
}

// repair resolves a decoded item's references before integration (y-octo:
// DocStore::repair). The origin ids resolve to live items through the store's
// per-client run lists, splitting a run when an origin points inside it
// (split_at_and_get_left/right), and the parent is recovered:
//   - parentName != nil is Parent::String: look up / create the root type by
//     name (y-octo: get_or_create_type);
//   - parentName == nil is Parent::None: borrow the parent from the resolved
//     left (or right) neighbour.
//
// Parent::Id (type-as-item) is out of the verified subset (#43). parentName is
// passed alongside the item because the decoded wire form lives on updateItem,
// not on item (see item.parent). Callers hold s.mu.
func (s *store) repair(it *item, parentName *string) {
	// After the clean-end/clean-start splits the origin ids already sit on
	// node boundaries (the left origin IS the left node's LastId, the right
	// origin IS the right node's id), so y-octo's re-normalization
	// assignments of the origin ids are identities and are omitted here.
	if it.originLeftId != nil {
		left, ok := s.splitAtAndGetLeft(*it.originLeftId)
		if ok {
			it.left = left
		}
	}
	if it.originRightId != nil {
		right, ok := s.splitAtAndGetRight(*it.originRightId)
		if ok {
			it.right = right
		}
	}

	if parentName != nil {
		it.parent = s.getOrCreateYType(*parentName)
	} else if it.left != nil {
		it.parent = it.left.parent
	} else if it.right != nil {
		it.parent = it.right.parent
	}
}

// scanConflicts walks the run of concurrent items starting at conflict and
// updates the left anchor, stopping at right or when the origin connections
// would cross (y-octo's conflict-resolution loop). It is the operational
// counterpart of setfindIntegratedIndex; extracted from findIntegrationLeft so
// the scan can be verified against the pure set-based loop in isolation.
func scanConflicts(item *item, left *item, conflict *item, right *item) *item {
	conflictingItems := []idSpan{}
	itemsBeforeOrigin := []idSpan{}

	for conflict != nil {
		if itemPtrEqual(conflict, right) {
			break
		}
		span := idSpan{id: conflict.id, len: conflict.Len()}
		itemsBeforeOrigin = append(itemsBeforeOrigin, span)
		conflictingItems = append(conflictingItems, span)

		if idOptEqual(item.originLeftId, conflict.originLeftId) {
			// Same left origin: the smaller client id goes first.
			if conflict.id.clientId < item.id.clientId {
				left = conflict
				conflictingItems = []idSpan{}
			} else if idOptEqual(item.originRightId, conflict.originRightId) {
				// Same integration points; item is to the left of conflict.
				break
			}
		} else if conflict.originLeftId != nil && containsId(itemsBeforeOrigin, *conflict.originLeftId) {
			// case 2: conflict's left origin was already scanned.
			col := *conflict.originLeftId
			if !containsId(conflictingItems, col) {
				left = conflict
				conflictingItems = []idSpan{}
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
func findIntegrationLeft(parent *yType, it *item, left *item, right *item) *item {
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

// deleteNode tombstones one whole node: sets its Deleted flag and shrinks its
// type's visible length (y-octo: DocStore::delete_item_inner; Yjs
// v14.0.0-rc.18 Item.delete, src/structs/Item.js:366; yrs 0.27.2
// src/block.rs:635), and reports whether it did: a node that is already
// tombstoned is left alone, which is what makes a re-delivered delete
// idempotent. It records nothing; Transaction.deleteNode records the flip in
// the transaction (Yjs and yrs record at this point, y-octo, having no
// transaction, does not). The node must be integrated (reached through the
// store's run lists); callers hold s.mu. A free function, not a *store
// method as in y-octo (whose &mut self borrows the whole store either way):
// it touches only the node and its parent type, and the footprint must be
// visible in the program.
func deleteNode(it *item) bool {
	if it.Indexable() {
		it.flags = it.flags | itemDeleted
		it.parent.len = it.parent.len - it.Len()
		return true
	}
	return false
}

// integrateCore is y-octo store::integrate up to (but not including) the final
// self.add_node: it resolves origin-based conflicts the same way as the Yjs
// integrate algorithm, splices item into the doubly linked list at its
// conflict-resolved position, and bumps parent.len. It is extracted from
// Integrate so the hard conflict-scan WP proof (wp_Store__integrateCore) stays
// isolated from the item-set bookkeeping added by addNode (mirrors the
// findIntegrationLeft extraction).
//
// Port of y-octo store::integrate (src/doc/store.rs), with these differences:
//   - the offset>0 path, which integrates only the part of a struct past the
//     characters the store already has, is dropped: store.applyUpdate skips a
//     struct whose first character is present, where Yjs, yrs and y-octo
//     integrate the rest of it (Yjs v14.0.0-rc.18 src/structs/Item.js:168;
//     yrs 0.27.2 src/update.rs:341; y-octo 0.1.0 src/doc/store.rs:423; #207).
//     The byte decoder hands over one-character structs, so no such struct
//     arrives today;
//   - parent_sub is always None (root sequence), so the map branches are dropped;
//   - the caller holds the store's write lock, so y-octo's unsafe shared-reference
//     handling becomes plain pointer mutation;
//   - the parent type is never deleted.
//
// item.left / item.right are taken as given (y-octo reads this.left/this.right
// directly): the update path resolves them with store.repair beforehand, the
// local-edit path creates the item already linked to its neighbours.
func (s *store) integrateCore(parent *yType, item *item) {
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

// Integrate inserts item into its parent's sequence and records it in the
// store's per-client item set (y-octo: store::integrate, ending in
// self.add_node(node)). The parent argument mirrors y-octo's
// Option<&mut YType> fast path: local edits pass the type they are already
// working on, while the update path passes nil and the item's own parent
// (resolved by store.repair) is used; an item whose parent did not resolve is
// dropped, as in y-octo. On return item is spliced into the doubly linked
// list at its conflict-resolved position, parent.len is updated and
// s.items[item.id.clientId] holds item at its tail. The result is the parent
// item went into, nil when item was dropped. It records nothing:
// Transaction.integrate records the item in the transaction (Yjs
// v14.0.0-rc.18 Item.integrate, src/structs/Item.js:270-274; yrs 0.27.2
// src/block.rs:1085-1090; y-octo has no transaction and records nothing).
func (s *store) Integrate(parent *yType, item *item) *yType {
	if parent == nil {
		if item.parent == nil {
			return nil
		}
		parent = item.parent
	}
	s.integrateCore(parent, item)
	addNode(s.items, item)
	return parent
}

// hasNode reports whether the struct with the given id has been integrated.
func (s *store) hasNode(id id) bool {
	_, ok := s.GetNode(id)
	return ok
}

// containsUpdateItemId reports whether any queued struct carries id.
func containsUpdateItemId(items []updateItem, id id) bool {
	for i := 0; i < len(items); i++ {
		if items[i].id.Equal(id) {
			return true
		}
	}
	return false
}

// originArrived reports whether an optional origin dependency has been
// integrated; a nil origin imposes none.
func (s *store) originArrived(p *id) bool {
	if p == nil {
		return true
	}
	return s.hasNode(*p)
}

// depsArrived reports whether every dependency of the decoded struct has
// already been integrated: both origins (y-octo: UpdateIterator's
// get_missing_dep, update.rs) and, for clock > 0, the author's preceding
// struct. The predecessor clause is y-octo's per-client state-vector
// contiguity check (state.contains(id)): with gap-free per-client run lists,
// "(c, k-1) integrated" is exactly "state(c) >= k", but phrased as an arrival
// check so the store tracks no state vector. Parents never gate in this
// subset: a parentName resolves by getOrCreateYType (creating on first use)
// and a nil parentName borrows the parent from a resolved origin
// (Parent::Id, which y-octo also gates on, is out of the subset, #43).
func (s *store) depsArrived(ui updateItem) bool {
	if !s.originArrived(ui.originLeftId) {
		return false
	}
	if !s.originArrived(ui.originRightId) {
		return false
	}
	if ui.id.clock > 0 && !s.hasNode(newId(ui.id.clientId, ui.id.clock-1)) {
		return false
	}
	return true
}
