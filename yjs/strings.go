//go:build !goose

package yjs

import "unicode/utf16"

// The Go-string view of the text API. The verified API (text.go, observe.go)
// works on UTF-16 code units and converts nothing; these wrappers are the
// convenience layer for Go callers and the tests, converting between a Go
// string (UTF-8) and code units with the standard library. Outside the goose
// translation: nothing here is verified, and nothing verified depends on it.
//
// The conversion is lossy only on lone surrogates, which a Go string cannot
// hold: utf16.Decode maps them to U+FFFD (the same replacement the codec
// writes on the wire, codec.go).

// encodeContent is the code units of the Go string s.
func encodeContent(s string) []uint16 {
	return utf16.Encode([]rune(s))
}

// decodeContent is the Go string of the code units units, lone surrogates
// replaced by U+FFFD.
func decodeContent(units []uint16) string {
	return string(utf16.Decode(units))
}

// String returns the current visible text as a Go string (Text.CodeUnits
// decoded).
func (t *Text) String() string {
	return decodeContent(t.CodeUnits())
}

// StringIn returns the visible text inside the transaction tr as a Go string
// (Text.CodeUnitsIn decoded).
func (t *Text) StringIn(tr *Transaction) string {
	return decodeContent(t.CodeUnitsIn(tr))
}

// InsertString inserts the Go string s at the visible index, counted in code
// units (Text.Insert of its code units).
func (t *Text) InsertString(index uint64, s string) {
	t.Insert(index, encodeContent(s))
}

// InsertStringIn inserts the Go string s at the visible index inside the
// transaction tr (Text.InsertIn of its code units).
func (t *Text) InsertStringIn(tr *Transaction, index uint64, s string) {
	t.InsertIn(tr, index, encodeContent(s))
}

// ApplyDeltaString patches the Go string s with delta (ApplyDelta over its
// code units) and returns the patched Go string.
func ApplyDeltaString(s string, delta []DeltaOp) (string, bool) {
	result, ok := ApplyDelta(encodeContent(s), delta)
	if !ok {
		return "", false
	}
	return decodeContent(result), true
}
