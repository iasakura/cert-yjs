package yjs

type Flags = uint8

// Item is a single CRDT insertion (y-octo: codec/item.rs). The Phase-1/2
// simplification drops the parent / parent_sub fields (root sequence only) and
// keeps the content to a single 1-char string, so an item never needs to split
// (len == 1, last_id == id).
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

// Item flag bits (y-octo: src/doc/codec/item_flag.rs).
const (
	ItemKeep      Flags = 0x01
	ItemCountable Flags = 0x02
	ItemDeleted   Flags = 0x04
)

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
