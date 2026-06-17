package yjs

// Content is the payload of an item. The Phase-1 simplification fixes this to a
// single string type (y-octo's codec/content.rs has many variants).
//
// TODO: support more types
type Content struct {
	content string
}

// Len is the number of clocks the content occupies (y-octo: Content::clock_len).
func (c Content) Len() uint64 {
	return uint64(len(c.content))
}
