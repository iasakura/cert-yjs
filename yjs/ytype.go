package yjs

// The inner root sequence type (y-octo: YType in doc/types). In y-octo YType is
// the lock-guarded data structure (inside the Arc<RwLock<DocStore>>), while the
// YText handle lives outside the lock; we mirror that split: a yType and the DLL
// reached from its [start] are only ever touched while holding store.mu, and the
// public [Text] handle (text.go) is the unlocked wrapper that takes the lock.
//
// These methods are goose-translated (part of the verified model): findPos feeds
// the proven store.Integrate loop (and Text.Delete), so Text.Insert / Text.Delete
// preserve the document invariant is_ytype (see wp_yType__findPos / is_ytype in
// src/proof/yjs_ytype.v).
//
// Simplifications vs y-octo:
//   - the Phase-1 content is fixed to a single string type with no parent_sub,
//     so we only need the head of the item linked list and the visible length;
//   - every user-visible character becomes its own 1-char internal item, so
//     positions never fall inside an item and no splitting is needed.

// yType is the root sequence type the items are integrated into (y-octo: YType
// in doc/types). The Phase-1 simplification fixes the content to a single string
// type with no parent_sub, so we only need the head of the item linked list and
// the visible length.
type yType struct {
	// start is the head of the doubly linked list of items (parent.start).
	start *item
	// len is the visible (countable, non-deleted) length.
	len uint64
}

// newYType creates an empty root sequence.
func newYType() *yType {
	return &yType{start: nil, len: 0}
}

// findPos walks to the visible character index and returns the doubly-linked
// neighbours (left, right) straddling that position (y-octo: ListType::find_pos
// specialised to 1-char items, so the offset/normalize/split path is gone).
//
// The walk advances through tombstones as well as visible items, moving [left]
// in lockstep with [right] (so [right == left.right] on return) and decrementing
// the budget only on visible (Indexable) items. This mirrors y-octo's
// TextPosition::forward (doc/types/text.rs): a deleted item still becomes the new
// [left], so the returned neighbours are always adjacent in the list and supply a
// consistent origin pair for the inserted item.
func (y *yType) findPos(index uint64) (*item, *item) {
	var left *item
	right := y.start

	// Skip leading tombstones so the cursor starts at the first visible item
	// (y-octo: "avoid the first item being a deleted one"). [left] advances in
	// lockstep with [right], so the returned neighbours stay adjacent in the
	// list (right == left.right) and supply a consistent origin pair.
	for right != nil && right.Deleted() {
		left = right
		right = right.right
	}

	remaining := index
	for remaining > 0 && right != nil {
		if right.Indexable() {
			remaining = remaining - right.Len()
		}
		left = right
		right = right.right
	}
	return left, right
}

// Text reads the current visible string by walking the item list left to right
// (skipping deleted items). Useful for stating/verifying convergence.
func (parent *yType) Text() string {
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
