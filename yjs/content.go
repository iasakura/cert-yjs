package yjs

// content is the payload of an item: a string, the only one of y-octo's content
// variants (codec/content.rs) implemented here.
//
// TODO: support more types
type content struct {
	content string
}

// Len is the number of clocks the content occupies (y-octo: content::clock_len).
// It counts bytes, one clock per byte, where Yjs, yrs and y-octo count UTF-16
// code units (Yjs v14.0.0-rc.18 ContentString.getLength, src/structs/Item.js:1297;
// yrs 0.27.2 src/block.rs:699; y-octo 0.1.0 src/doc/codec/content.rs:203), so
// the two agree on ASCII text only.
func (c content) Len() uint64 {
	return uint64(len(c.content))
}

// byteString returns the one-byte string holding b. It is built from a byte
// slice because Go's string(b) of a byte is the integer-to-string conversion:
// it takes b as a code point and returns its UTF-8 encoding, two bytes from
// 0x80 up (issue #216). Slicing a string (s[i:i+1]) would do, but goose has no
// rule for it (see splitItem).
func byteString(b byte) string {
	return string([]byte{b})
}
