//go:build !goose

package yjs

import "sort"

// v1 update codec: a port of y-octo's src/doc/codec for the cert-yjs subset.
//
// Layout mirrors y-octo:
//   - encoder / decoder            <- codec/io/{writer,reader}.rs (lib0 varint)
//   - encodeItem / item read       <- codec/item.rs (info byte, origins, parent)
//   - encodeNode / node read       <- codec/refs.rs (GC=0, Skip=10, else item)
//   - EncodeUpdate / ApplyUpdate   <- codec/update.rs (clients -> structs, then
//                                     the delete set)
//   - delete set                   <- codec/delete_set.rs
//
// Subset assumptions: the only content type is String (tag 4); parents are
// always root types referenced by name (never Parent::id, never parent_sub);
// content is single-byte (ASCII). Multi-char runs in an incoming update are
// split into 1-char items on decode (chained left origins, shared right
// origin), then integrated in dependency order.
//
// Excluded from goose translation (`//go:build !goose`): runtime interop, not
// part of the verified core.

// item info-byte flags (y-octo: codec/item_flag.rs) and the String content tag.
const (
	infoHasParentSub  = 0x20
	infoHasRightID    = 0x40
	infoHasLeftID     = 0x80
	infoHasSibling    = 0xC0
	contentTypeString = 4
	nodeTagGC         = 0
	nodeTagSkip       = 10
)

// ----- low-level writer / reader (lib0 unsigned LEB128 varint) ---------------

type encoder struct {
	buf []byte
}

func (e *encoder) writeU8(b byte) { e.buf = append(e.buf, b) }

func (e *encoder) writeVarUint(n uint64) {
	for n > 0x7f {
		e.buf = append(e.buf, byte(n&0x7f)|0x80)
		n >>= 7
	}
	e.buf = append(e.buf, byte(n&0x7f))
}

func (e *encoder) writeVarString(s string) {
	e.writeVarUint(uint64(len(s)))
	e.buf = append(e.buf, s...)
}

func (e *encoder) writeItemID(id id) {
	e.writeVarUint(id.clientId)
	e.writeVarUint(id.clock)
}

type decoder struct {
	buf []byte
	pos int
}

func (d *decoder) eof() bool { return d.pos >= len(d.buf) }

func (d *decoder) readU8() byte {
	b := d.buf[d.pos]
	d.pos++
	return b
}

func (d *decoder) readVarUint() uint64 {
	var x uint64
	var s uint
	for {
		b := d.buf[d.pos]
		d.pos++
		x |= uint64(b&0x7f) << s
		if b < 0x80 {
			return x
		}
		s += 7
	}
}

func (d *decoder) readVarString() string {
	n := int(d.readVarUint())
	s := string(d.buf[d.pos : d.pos+n])
	d.pos += n
	return s
}

func (d *decoder) readItemID() id {
	client := d.readVarUint()
	clock := d.readVarUint()
	return newId(client, clock)
}

// ----- encode ----------------------------------------------------------------

// EncodeUpdate serializes the whole document state as a Yjs v1 update.
func (doc *Doc) EncodeUpdate() []byte {
	e := &encoder{}

	// item id -> owning root-type name, for head items' parent field.
	name := map[id]string{}
	for nm, y := range doc.types {
		for cur := y.start; cur != nil; cur = cur.right {
			name[cur.id] = nm
		}
	}

	// structs, grouped by client (store.items is per-client clock-sorted).
	clients := sortedClientsDesc(doc.store.items)
	e.writeVarUint(uint64(len(clients)))
	for _, client := range clients {
		nodes := doc.store.items[client]
		e.writeVarUint(uint64(len(nodes)))
		e.writeVarUint(client)
		e.writeVarUint(nodes[0].clock())
		for _, node := range nodes {
			encodeNode(e, node, name)
		}
	}

	// delete set.
	delClients := sortedClientsDesc(doc.store.deletedSet.deletedSet)
	e.writeVarUint(uint64(len(delClients)))
	for _, client := range delClients {
		e.writeVarUint(client)
		encodeOrderRange(e, doc.store.deletedSet.deletedSet[client])
	}

	return e.buf
}

func encodeNode(e *encoder, node node, name map[id]string) {
	switch n := node.(type) {
	case itemNode:
		encodeItem(e, n.item, name)
	case gcNode:
		e.writeU8(nodeTagGC)
		e.writeVarUint(n.nodeLen.len)
	case skipNode:
		e.writeU8(nodeTagSkip)
		e.writeVarUint(n.nodeLen.len)
	}
}

func encodeItem(e *encoder, item item, name map[id]string) {
	info := byte(contentTypeString)
	if item.originLeftId != nil {
		info |= infoHasLeftID
	}
	if item.originRightId != nil {
		info |= infoHasRightID
	}
	e.writeU8(info)

	if item.originLeftId != nil {
		e.writeItemID(*item.originLeftId)
	}
	if item.originRightId != nil {
		e.writeItemID(*item.originRightId)
	}

	// a head item (no sibling origins) carries its parent: the root type name.
	if info&infoHasSibling == 0 {
		e.writeVarUint(1) // 1 => Parent::String
		e.writeVarString(name[item.id])
	}

	e.writeVarString(item.content.content)
}

func encodeOrderRange(e *encoder, r orderRange) {
	ranges := rangesOf(r)
	e.writeVarUint(uint64(len(ranges)))
	for _, rg := range ranges {
		e.writeVarUint(rg.start)
		e.writeVarUint(rg.end - rg.start)
	}
}

func rangesOf(r orderRange) []span[uint64] {
	switch rr := r.(type) {
	case rangeOrderRange:
		return []span[uint64]{rr.range_}
	case fragmentOrderRange:
		return rr.fragment
	}
	return nil
}

func sortedClientsDesc[V any](m map[Client]V) []Client {
	cs := make([]Client, 0, len(m))
	for c := range m {
		cs = append(cs, c)
	}
	sort.Slice(cs, func(i, j int) bool { return cs[i] > cs[j] })
	return cs
}

// ----- decode + apply --------------------------------------------------------

// decodedStruct is one struct read from an update, before run-splitting.
type decodedStruct struct {
	id            id
	originLeftId  *id
	originRightId *id
	parentName    string // set only for head structs (no origins)
	content       string
	isItem        bool // false => GC / Skip (no content, not integrated)
	length        uint64
}

type pendingDelete struct {
	client Client
	clock  uint64
	length uint64
}

// ApplyUpdate decodes a Yjs v1 update and integrates it into the document.
// It assumes the update is well-formed and self-contained (every referenced
// origin is present); items whose dependencies are missing are dropped.
func (doc *Doc) ApplyUpdate(data []byte) {
	d := &decoder{buf: data}

	// structs
	var structs []decodedStruct
	numClients := d.readVarUint()
	for c := uint64(0); c < numClients; c++ {
		numStructs := d.readVarUint()
		client := d.readVarUint()
		clock := d.readVarUint()
		for s := uint64(0); s < numStructs; s++ {
			ds := readStruct(d, client, clock)
			clock += ds.length
			structs = append(structs, ds)
		}
	}

	// delete set
	var deletes []pendingDelete
	numDelClients := d.readVarUint()
	for c := uint64(0); c < numDelClients; c++ {
		client := d.readVarUint()
		numRanges := d.readVarUint()
		for r := uint64(0); r < numRanges; r++ {
			clock := d.readVarUint()
			length := d.readVarUint()
			deletes = append(deletes, pendingDelete{client: client, clock: clock, length: length})
		}
	}

	doc.integrateStructs(structs)
	doc.applyDeletes(deletes)
}

func readStruct(d *decoder, client Client, clock uint64) decodedStruct {
	info := d.readU8()
	first5 := info & 0x1f

	if first5 == nodeTagGC || first5 == nodeTagSkip {
		length := d.readVarUint()
		return decodedStruct{id: newId(client, clock), isItem: false, length: length}
	}

	hasLeft := info&infoHasLeftID != 0
	hasRight := info&infoHasRightID != 0
	hasParentSub := info&infoHasParentSub != 0
	hasNotSibling := info&infoHasSibling == 0

	var originLeftId *id
	var originRightId *id
	if hasLeft {
		v := d.readItemID()
		originLeftId = &v
	}
	if hasRight {
		v := d.readItemID()
		originRightId = &v
	}

	name := ""
	if hasNotSibling {
		if d.readVarUint() == 1 {
			name = d.readVarString()
		} else {
			// Parent::id: this subset routes by origin instead, so ignore it.
			d.readItemID()
		}
	}
	if hasNotSibling && hasParentSub {
		d.readVarString() // parent_sub: unused in this subset
	}

	content := d.readVarString()
	return decodedStruct{
		id:            newId(client, clock),
		originLeftId:  originLeftId,
		originRightId: originRightId,
		parentName:    name,
		content:       content,
		isItem:        true,
		length:        uint64(len(content)),
	}
}

// pendingItem is a single 1-char item awaiting integration.
type pendingItem struct {
	id            id
	originLeftId  *id
	originRightId *id
	parentName    string // meaningful only when both origins are nil
	content       string
}

// integrateStructs splits each item struct into 1-char items and integrates
// them in dependency order: an item is integrated once both of its origins are
// already integrated (so findById can resolve them). Repeated passes process
// the remainder until no progress is made.
func (doc *Doc) integrateStructs(structs []decodedStruct) {
	var pending []pendingItem
	for _, ds := range structs {
		if !ds.isItem {
			// GC / Skip: register for the state vector, do not integrate.
			doc.store.AddNode(gcNode{nodeLen: nodeLen{id: ds.id, len: ds.length}})
			continue
		}
		runLen := len(ds.content)
		for j := 0; j < runLen; j++ {
			subID := newId(ds.id.clientId, ds.id.clock+uint64(j))
			var originLeftId *id
			if j == 0 {
				originLeftId = ds.originLeftId
			} else {
				prev := newId(ds.id.clientId, ds.id.clock+uint64(j-1))
				originLeftId = &prev
			}
			pending = append(pending, pendingItem{
				id:            subID,
				originLeftId:  originLeftId,
				originRightId: ds.originRightId,
				parentName:    ds.parentName,
				content:       ds.content[j : j+1],
			})
		}
	}

	idToText := map[id]*yText{}
	for len(pending) > 0 {
		progressed := false
		var next []pendingItem
		for _, pi := range pending {
			leftOK := pi.originLeftId == nil || hasIDKey(idToText, *pi.originLeftId)
			rightOK := pi.originRightId == nil || hasIDKey(idToText, *pi.originRightId)
			if !(leftOK && rightOK) {
				next = append(next, pi)
				continue
			}

			var txt *yText
			if pi.originLeftId != nil {
				txt = idToText[*pi.originLeftId]
			} else if pi.originRightId != nil {
				txt = idToText[*pi.originRightId]
			} else {
				txt = doc.getOrCreateYText(pi.parentName)
			}

			item := newItem(pi.id, pi.content, pi.originLeftId, pi.originRightId)
			doc.store.Integrate(txt, item)
			doc.store.AddNode(itemNode{item: *item})
			idToText[pi.id] = txt
			progressed = true
		}
		pending = next
		if !progressed {
			break // missing dependencies: drop the remainder (minimal codec)
		}
	}

	// integration order may differ from clock order; keep store.items sorted so
	// get_node_index (binary search) and re-encoding stay correct.
	for client := range doc.store.items {
		nodes := doc.store.items[client]
		sort.Slice(nodes, func(i, j int) bool { return nodes[i].clock() < nodes[j].clock() })
	}
}

// applyDeletes records each range in the delete set and tombstones the matching
// items across all root types.
func (doc *Doc) applyDeletes(deletes []pendingDelete) {
	for _, del := range deletes {
		doc.store.deletedSet.addRange(newId(del.client, del.clock), del.length)
		end := del.clock + del.length
		for clock := del.clock; clock < end; clock++ {
			target := newId(del.client, clock)
			item, y := doc.findItem(target)
			if item != nil && !item.Deleted() {
				item.flags = item.flags | itemDeleted
				if item.Countable() {
					y.len = y.len - item.Len()
				}
			}
		}
	}
}

// findItem locates the item with id across the document's root types.
func (doc *Doc) findItem(id id) (*item, *yText) {
	for _, y := range doc.types {
		if it := findById(y, id); it != nil {
			return it, y
		}
	}
	return nil, nil
}

func hasIDKey[V any](m map[id]V, k id) bool {
	_, ok := m[k]
	return ok
}
