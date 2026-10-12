//go:build !goose

package yjs

import (
	"sort"
	"unicode/utf16"
)

// v1 update codec: a port of y-octo's src/doc/codec for the Cert-Yjs subset.
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
// always root types referenced by name (never Parent::id, never parent_sub).
// Multi-unit runs in an incoming update are split into 1-unit items on decode
// (chained left origins, shared right origin), then integrated in dependency
// order.
//
// Text encoding. The document holds UTF-16 code units (content.go) and the
// wire holds UTF-8 strings (lib0 writeVarString), so this file is where the
// two meet: decodeWireString turns a wire string into code units and
// encodeWireString turns a run's code units back into a string. Because local
// inserts create one item per code unit, a surrogate pair is two items; the
// encoder joins adjacent items of one client into runs (joinable, below)
// before writing a string, so that the pair's halves leave as one struct and
// one code point. A half that cannot be joined (a concurrent insert landed
// between the halves) is a lone surrogate, which encodeWireString replaces by
// U+FFFD, one code unit for one, so the clock count on the wire is unchanged.
// The three references split a pair differently: Yjs v14.0.0-rc.18 replaces
// both halves by U+FFFD in memory the moment a split lands between them
// (ContentString.splice, src/structs/Item.js:1326-1341); yrs 0.27.2
// (ItemContent::splice, src/block.rs:2006-2033, over split_str,
// src/block.rs:1669) and y-octo 0.1.0 (Content::split,
// src/doc/codec/content.rs:218-224, over utf16_offset_to_utf8,
// src/doc/common/algorithm.rs:28-42) map the UTF-16 offset to a byte offset
// one whole character at a time and stop once the offset is reached, so a
// split inside a pair moves to the end of the pair: the left half keeps the
// whole pair and one code unit more than its clock range (yrs's U+FFFD
// replacement is commented out, "TODO: do we need that in Rust?"). The Go
// follows Yjs: it never produces a lone surrogate from a split that is not
// one, and what it has to write as a lone surrogate becomes U+FFFD, as
// Yjs's own encoder would write it (TextEncoder replaces lone surrogates).
// Unlike Yjs the replacement happens at encode time, not in the document,
// so the document keeps the exact code units it was given.
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

// encodeWireString is the wire string of a run's code units: the UTF-8 of
// the text they spell, a lone surrogate replaced by U+FFFD (utf16.Decode),
// which keeps one code unit per clock on the wire; see the file comment.
func encodeWireString(units []uint16) string {
	return string(utf16.Decode(units))
}

// decodeWireString is the code units of a wire string, one clock each.
func decodeWireString(s string) []uint16 {
	return utf16.Encode([]rune(s))
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

// generateDeleteSet derives the document's delete set from the items' Deleted
// flags, walking each root sequence's item list (y-octo:
// DocStore::generate_delete_set). The verified Delete keeps only the flags and
// the visible length up to date; the codec regenerates this serialization cache
// on demand, so the store's DeleteSet need not be mirrored by Delete.
func generateDeleteSet(doc *Doc) map[Client]orderRange {
	ds := deletedSet{deletedSet: make(map[Client]orderRange)}
	for _, y := range doc.store.store.types {
		for cur := y.start; cur != nil; cur = cur.right {
			if cur.Deleted() {
				ds.addRange(cur.id, cur.Len())
			}
		}
	}
	return ds.deletedSet
}

// EncodeUpdate serializes the whole document state as a Yjs v1 update.
func (doc *Doc) EncodeUpdate() []byte {
	e := &encoder{}

	// Gather the live items from the document's sequences -- the DLLs are the
	// source of truth (Insert no longer mirrors into the struct store). Record
	// each item's owning root-type name (for head items' parent field) and group
	// by client, then sort each client's run by clock.
	name := map[id]string{}
	byClient := map[Client][]*item{}
	for nm, y := range doc.store.store.types {
		for cur := y.start; cur != nil; cur = cur.right {
			name[cur.id] = nm
			byClient[cur.id.clientId] = append(byClient[cur.id.clientId], cur)
		}
	}
	for c := range byClient {
		runItems := byClient[c]
		sort.Slice(runItems, func(i, j int) bool { return runItems[i].id.clock < runItems[j].id.clock })
	}

	clients := sortedClientsDesc(byClient)
	e.writeVarUint(uint64(len(clients)))
	for _, client := range clients {
		// Adjacent items of this client that Yjs would hold as one item are
		// written as one struct (joinable): a surrogate pair typed locally is
		// two one-unit items, and only joined do its halves encode as one code
		// point (see the file comment).
		runs := joinRuns(byClient[client])
		e.writeVarUint(uint64(len(runs)))
		e.writeVarUint(client)
		e.writeVarUint(runs[0][0].id.clock)
		for _, run := range runs {
			encodeRun(e, run, name)
		}
	}

	// delete set, derived from the items' Deleted flags (y-octo:
	// DocStore::generate_delete_set). The flag is the source of truth for
	// visibility, so the verified Delete only sets flags + visible length and the
	// serialization cache is regenerated here at encode time.
	deletedSet := generateDeleteSet(doc)
	delClients := sortedClientsDesc(deletedSet)
	e.writeVarUint(uint64(len(delClients)))
	for _, client := range delClients {
		e.writeVarUint(client)
		encodeOrderRange(e, deletedSet[client])
	}

	return e.buf
}

func encodeNode(e *encoder, node node, name map[id]string) {
	switch n := node.(type) {
	case itemNode:
		encodeRun(e, []*item{&n.item}, name)
	case gcNode:
		e.writeU8(nodeTagGC)
		e.writeVarUint(n.nodeLen.len)
	case skipNode:
		e.writeU8(nodeTagSkip)
		e.writeVarUint(n.nodeLen.len)
	}
}

// joinable reports whether next continues the run of prev as one item, the
// conditions under which the references merge two items into one (Yjs
// v14.0.0-rc.18 Item.mergeWith, src/structs/Item.js:321-334; yrs 0.27.2
// ItemPtr::try_squash, src/block.rs:688-698; y-octo 0.1.0 Node::merge,
// src/doc/codec/refs.rs:243-254): same client, consecutive clocks, next's
// left origin is prev's last id, the same right origin, adjacent in the
// list, and the same deleted flag. Yjs and yrs also require no redo and
// (yrs) no link, which this subset has no notion of. The two halves of a
// split run are always joinable (splitItem, store.go), and so are the items
// of one local insert (Text.InsertIn).
func joinable(prev *item, next *item) bool {
	return prev.id.clientId == next.id.clientId &&
		prev.id.clock+prev.Len() == next.id.clock &&
		next.originLeftId != nil && *next.originLeftId == prev.LastId() &&
		idOptEqual(prev.originRightId, next.originRightId) &&
		prev.right == next &&
		prev.Deleted() == next.Deleted()
}

// joinRuns groups a client's clock-sorted items into maximal joinable runs,
// each written as one struct.
func joinRuns(items []*item) [][]*item {
	var runs [][]*item
	for _, it := range items {
		n := len(runs)
		if n > 0 && joinable(runs[n-1][len(runs[n-1])-1], it) {
			runs[n-1] = append(runs[n-1], it)
			continue
		}
		runs = append(runs, []*item{it})
	}
	return runs
}

// encodeRun writes one struct for a joinable run of items: the head's info
// byte, origins and parent, then the string the run's code units spell.
func encodeRun(e *encoder, run []*item, name map[id]string) {
	head := run[0]
	info := byte(contentTypeString)
	if head.originLeftId != nil {
		info |= infoHasLeftID
	}
	if head.originRightId != nil {
		info |= infoHasRightID
	}
	e.writeU8(info)

	if head.originLeftId != nil {
		e.writeItemID(*head.originLeftId)
	}
	if head.originRightId != nil {
		e.writeItemID(*head.originRightId)
	}

	// a head item (no sibling origins) carries its parent: the root type name.
	if info&infoHasSibling == 0 {
		e.writeVarUint(1) // 1 => Parent::String
		e.writeVarString(name[head.id])
	}

	var units []uint16
	for _, it := range run {
		units = append(units, it.content.content...)
	}
	e.writeVarString(encodeWireString(units))
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
	parentName    string   // set only for head structs (no origins)
	content       []uint16 // the wire string's code units, one clock each
	isItem        bool     // false => GC / Skip (no content, not integrated)
	length        uint64
}

type pendingDelete struct {
	client Client
	clock  uint64
	length uint64
}

// ApplyUpdate decodes a Yjs v1 update and integrates it into the document.
// The update may arrive in any order and need not be self-contained: structs
// whose dependencies have not arrived yet are buffered in the store's pending
// buffer by the verified store.applyUpdate and drained by later updates
// (issue #40).
func (doc *Doc) ApplyUpdate(data []byte) {
	d := &decoder{buf: data}

	// structs
	structs := readStructSection(d)

	// delete set
	var deletes []pendingDelete
	for _, sp := range readDeleteSection(d) {
		deletes = append(deletes, pendingDelete{client: sp.client, clock: sp.clock, length: sp.length})
	}

	doc.integrateStructs(structs)
	doc.store.wlock()
	doc.applyDeletes(deletes)
	doc.store.wunlock()
}

// readDeleteSection parses the delete set of an update into the decoded
// spans the verified store.applyDeleteSpans consumes (y-octo:
// DeleteSet::read). The decoder must be positioned right after the structs.
func readDeleteSection(d *decoder) []deleteSpan {
	var spans []deleteSpan
	numDelClients := d.readVarUint()
	for c := uint64(0); c < numDelClients; c++ {
		client := d.readVarUint()
		numRanges := d.readVarUint()
		for r := uint64(0); r < numRanges; r++ {
			clock := d.readVarUint()
			length := d.readVarUint()
			spans = append(spans, deleteSpan{client: client, clock: clock, length: length})
		}
	}
	return spans
}

// readStructSection parses the structs section of an update (the client
// runs and their structs), leaving the decoder at the delete set.
func readStructSection(d *decoder) []decodedStruct {
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
	return structs
}

// WireCodec is the deployment's Codec (the type is in doc.go): the v1 decode
// of an update's structs section, split into 1-unit items exactly as
// ApplyUpdate splits them, and of its delete set, as the spans that
// Doc.ApplySyncUpdate applies after the structs. Malformed input
// reports ok=false (the wire protocol makes that branch dead for the
// verified server, but the codec is total either way).
func WireCodec() Codec {
	return decodeUpdateItems
}

func decodeUpdateItems(data []byte) (ok bool, items []updateItem, deletes []deleteSpan) {
	// The low-level reader indexes without bounds checks (it is only ever fed
	// self-produced updates elsewhere); at this trust boundary a malformed
	// update must come back as ok=false instead.
	defer func() {
		if recover() != nil {
			ok, items, deletes = false, nil, nil
		}
	}()
	d := &decoder{buf: data}
	structs := readStructSection(d)
	items = splitStructs(structs)
	return true, items, readDeleteSection(d)
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

	content := decodeWireString(d.readVarString())
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

// integrateStructs hands the split batch to the verified total update path
// in one locked call: Doc.applyUpdate buffers structs whose dependencies are
// missing in the store's pending, so no ordering or self-containedness is
// assumed here (issue #40).
func (doc *Doc) integrateStructs(structs []decodedStruct) {
	doc.applyUpdate(splitStructs(structs))
}

// splitStructs splits each item struct into 1-unit updateItems (chained left
// origins, shared right origin), each holding a one-unit subslice of the
// struct's code units (never written afterwards, content.go).
func splitStructs(structs []decodedStruct) []updateItem {
	var items []updateItem
	for _, ds := range structs {
		if !ds.isItem {
			// GC / Skip: nothing to integrate (the DLLs hold only items).
			continue
		}
		runLen := len(ds.content)
		for j := 0; j < runLen; j++ {
			subID := newId(ds.id.clientId, ds.id.clock+uint64(j))
			var originLeftId *id
			var parentName *string
			if j == 0 {
				originLeftId = ds.originLeftId
				if ds.originLeftId == nil && ds.originRightId == nil {
					nm := ds.parentName
					parentName = &nm
				}
			} else {
				prev := newId(ds.id.clientId, ds.id.clock+uint64(j-1))
				originLeftId = &prev
			}
			items = append(items, updateItem{
				id:            subID,
				originLeftId:  originLeftId,
				originRightId: ds.originRightId,
				parentName:    parentName,
				content:       ds.content[j : j+1],
			})
		}
	}

	return items
}

// applyDeletes records each range in the delete set and tombstones the matching
// items; the owning type comes from the item's own parent.
func (doc *Doc) applyDeletes(deletes []pendingDelete) {
	for _, del := range deletes {
		doc.store.store.deletedSet.addRange(newId(del.client, del.clock), del.length)
		end := del.clock + del.length
		for clock := del.clock; clock < end; clock++ {
			target := newId(del.client, clock)
			item, ok := doc.store.store.GetNode(target)
			if ok && !item.Deleted() {
				item.flags = item.flags | itemDeleted
				if item.Countable() {
					item.parent.len = item.parent.len - item.Len()
				}
			}
		}
	}
}
