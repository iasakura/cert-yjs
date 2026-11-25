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
// A second variant holds the values of a map entry or of a list of values:
// the any content of the references (Yjs v14.0.0-rc.18 ContentAny,
// src/structs/Item.js:603; yrs 0.27.2 ItemContent::Any, src/block.rs:1694),
// a list of values with one clock per value. Exactly one of the two fields
// is not empty: content for a string content, values for an any content.
// The other content variants of the references (binary, embed, format, type,
// doc, deleted) are not implemented.
type content struct {
	content []uint16
	values  []Value
}

// Value is one value of an any content: the lib0 encoding of a JSON-like
// value (null, a boolean, a number, a string, an array, an object, bytes),
// the form an update carries it in (lib0 0.2.119 encoding.writeAny, which Yjs
// v14.0.0-rc.18 ContentAny.write calls per value, src/structs/Item.js:680-687).
// Yjs keeps the JavaScript value itself and yrs 0.27.2 a value of its Any
// enum (src/any.rs), and both encode it when they write an update. The Go
// keeps the encoding: the CRDT never looks inside a value, so nothing is
// decoded or re-encoded inside the verified code, and a value written by
// another implementation is relayed byte for byte. EncodeValue and
// DecodeValue (value.go) convert from and to Go values outside the verified
// code. Like the code units of a string content, a value is never written
// after its item is created.
type Value = []byte

// Len is the number of clocks the content occupies (y-octo: content::clock_len):
// its number of code units or of values, one clock each, which is how the
// references count (Yjs v14.0.0-rc.18 ContentString.getLength,
// src/structs/Item.js:1297, and ContentAny.getLength, :618; yrs 0.27.2
// src/block.rs:1583; y-octo 0.1.0 src/doc/codec/content.rs:203).
func (c content) Len() uint64 {
	return uint64(len(c.content)) + uint64(len(c.values))
}

// slice is the part [start, stop) of the content, in clocks from its first:
// subslices of the same backing arrays (see above; Yjs v14.0.0-rc.18
// ContentString.splice and ContentAny.splice slice the string and the array
// the same way, src/structs/Item.js:1326 and :647). The caller passes
// 0 <= start <= stop <= c.Len().
func (c content) slice(start uint64, stop uint64) content {
	if len(c.values) > 0 {
		return content{content: nil, values: c.values[start:stop]}
	}
	return content{content: c.content[start:stop], values: nil}
}

// contentOfUnits is the string content of the code units units.
func contentOfUnits(units []uint16) content {
	return content{content: units, values: nil}
}

// contentOfValue is the any content of the one value value.
func contentOfValue(value Value) content {
	return content{content: nil, values: []Value{value}}
}
