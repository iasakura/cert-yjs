package yjs

type flags = uint8

// item is a single CRDT insertion (y-octo: codec/item.rs): a run of one or
// more consecutive characters of one client, which the store splits when an
// edit or an origin lands inside it. Local inserts and the byte decoder create
// one-character items for now (Text.InsertIn in text.go, splitStructs in
// codec.go), where Yjs, yrs and y-octo keep a run typed or sent together as
// one item. parent_sub is dropped (sequence types only).
type item struct {
	id id
	// null means no left origin when generated
	originLeftId *id
	// null means no right origin when generated
	originRightId *id
	left          *item
	right         *item
	// parent is the resolved type the item lives in (y-octo:
	// Some(Parent::Type)): set at creation for local edits (store::create_item)
	// and by store.repair for decoded items. The unresolved wire forms
	// (Parent::String, and None = borrow the neighbour's parent) live on
	// updateItem (update.go) and are consumed by repair; Parent::Id
	// (type-as-item) is out of the verified subset (#43).
	parent  *yType
	content content
	flags   flags
}

// item flag bits (y-octo: src/doc/codec/item_flag.rs).
const (
	itemKeep      flags = 0x01
	itemCountable flags = 0x02
	itemDeleted   flags = 0x04
)

// newItem builds an item carrying the string content str. It is countable
// (y-octo: string content sets ITEM_COUNTABLE) and starts unlinked and
// parentless: the update path resolves left/right/parent with store.repair,
// the local-edit path fills them in at creation (y-octo: store::create_item).
func newItem(id id, str string, originLeftId *id, originRightId *id) *item {
	return &item{
		id:            id,
		originLeftId:  originLeftId,
		originRightId: originRightId,
		left:          nil,
		right:         nil,
		parent:        nil,
		content:       content{content: str},
		flags:         itemCountable,
	}
}

// Len is the run length of the item (y-octo: item::len).
func (i item) Len() uint64 {
	return i.content.Len()
}

// LastId is the id of the item's final clock (y-octo: item::last_id).
func (i item) LastId() id {
	return id{clientId: i.id.clientId, clock: i.id.clock + i.Len() - 1}
}

// Deleted reports whether the item carries the deleted flag.
func (i item) Deleted() bool {
	return i.flags&itemDeleted != 0
}

// Countable reports whether the item contributes to the parent's length.
func (i item) Countable() bool {
	return i.flags&itemCountable != 0
}

// Indexable reports whether the item is visible in the sequence
// (y-octo: item::indexable = countable && !deleted).
func (i item) Indexable() bool {
	return i.Countable() && !i.Deleted()
}
