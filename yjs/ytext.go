package yjs

// yText is the root sequence type the items are integrated into. In y-octo this
// is a YType with start/map/item/len; the Phase-1 simplification fixes the
// content to a single string type with no parent_sub, so we only need the head
// of the item linked list and the visible length.
type yText struct {
	// start is the head of the doubly linked list of items (parent.start).
	start *item
	// len is the visible (countable, non-deleted) length.
	len uint64
}

// newYText creates an empty root sequence.
func newYText() *yText {
	return &yText{start: nil, len: 0}
}

// Text reads the current visible string by walking the item list left to right
// (skipping deleted items). Useful for stating/verifying convergence.
func (parent *yText) Text() string {
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
