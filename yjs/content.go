package yjs

// content is the payload of an item: a run of UTF-16 code units, the string
// content of the three references (Yjs v14.0.0-rc.18 ContentString,
// src/structs/Item.js:1283; yrs 0.27.2 ItemContent::String, src/block.rs:1717;
// y-octo 0.1.0 Content::String, src/doc/codec/content.rs:35) and the only one
// of their content variants implemented here. Yjs holds a JavaScript string,
// which IS a sequence of UTF-16 code units; yrs and y-octo hold a Rust UTF-8
// string and convert offsets to UTF-16 at every length and split. The Go holds
// the code units themselves, so no conversion happens inside the verified
// code; the byte codec (codec.go) converts to and from the wire's UTF-8 at the
// boundary.
//
// The slice is never written after the item is created: a split hands each
// half a subslice of the same backing array (splitItem, store.go), and every
// reader shares it. The proofs hold the content as persistent, read-only
// slice ownership (is_content, src/proof/item/heap.v), which is what makes
// that sharing sound.
//
// TODO: support more types
type content struct {
	content []uint16
}

// Len is the number of clocks the content occupies (y-octo: content::clock_len):
// its number of code units, one clock per unit, which is how all three
// references count (Yjs v14.0.0-rc.18 ContentString.getLength, src/structs/Item.js:1297;
// yrs 0.27.2 src/block.rs:1583; y-octo 0.1.0 src/doc/codec/content.rs:203).
func (c content) Len() uint64 {
	return uint64(len(c.content))
}
