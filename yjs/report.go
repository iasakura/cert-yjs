package yjs

// A report is what a replica writes to the trace about one root text
// (issue #239): the root's name and the text as Text.Snapshot sees it,
// character by character with ids and tombstone bits. It is verification
// tooling, not part of the Yjs protocol (none of Yjs, yrs or y-octo has
// it), so its layout is the simplest one a Rocq decoder reads back: every
// field is a little-endian uint64.
//
//	len(name)  u64
//	name       bytes
//	len(chars) u64
//	per char:  client u64, clock u64, deleted u64 (0 or 1), unit u64

// appendUint64 appends x to buf in little-endian order (the layout of
// encoding/binary.LittleEndian, spelled out so that the yjs package does
// not depend on another package's initialization).
func appendUint64(buf []byte, x uint64) []byte {
	return append(buf,
		byte(x), byte(x>>8), byte(x>>16), byte(x>>24),
		byte(x>>32), byte(x>>40), byte(x>>48), byte(x>>56))
}

// EncodeReport lays the report of root name out as bytes.
func EncodeReport(name string, chars []SnapshotChar) []byte {
	var buf []byte
	buf = appendUint64(buf, uint64(len(name)))
	buf = append(buf, []byte(name)...)
	buf = appendUint64(buf, uint64(len(chars)))
	for i := uint64(0); i < uint64(len(chars)); i++ {
		c := chars[i]
		buf = appendUint64(buf, c.Client)
		buf = appendUint64(buf, c.Clock)
		if c.Deleted {
			buf = appendUint64(buf, 1)
		} else {
			buf = appendUint64(buf, 0)
		}
		buf = appendUint64(buf, uint64(c.Unit))
	}
	return buf
}
