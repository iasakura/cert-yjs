package yjs

// content is the payload of an item. The Phase-1 simplification fixes this to a
// single string type (y-octo's codec/content.rs has many variants).
//
// TODO: support more types
type content struct {
	content string
}

// Len is the number of clocks the content occupies (y-octo: content::clock_len).
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
