//go:build !goose

package yjs

import (
	"encoding/binary"
	"math"
	"sort"
	"unicode/utf8"
)

// The Go-value view of a Value. The verified code (content.go, map.go)
// carries a value as the bytes of its lib0 "any" encoding and never looks
// inside; this file converts between those bytes and Go values, for Go
// callers and the tests, as strings.go does for text. Outside the goose
// translation: nothing here is verified, and nothing verified depends on it.
//
// The encoding is lib0 0.2.119 encoding.writeAny / decoding.readAny
// (encoding.js:544, decoding.js:531), one tag byte and a payload:
//
//	127 undefined              121 false / 120 true
//	126 null                   119 string (varUint byte length, UTF-8)
//	125 integer (varInt)       118 object (varUint count, then key string
//	124 float32 (big endian)       and value per entry)
//	123 float64 (big endian)   117 array (varUint count, then the values)
//	122 bigint (int64, b.e.)   116 bytes (varUint length, the bytes)
//
// Go values: nil is null, Undefined is undefined, bool, a number is a
// float64 or any Go integer type, an int64 or uint64 outside the range
// where a float64 is exact is a bigint, string, []byte, []any and
// map[string]any. DecodeValue gives back nil, Undefined, bool, float64 (for
// the three number tags), int64 (for a bigint), string, []byte, []any and
// map[string]any: every number of the wire is a JavaScript number, which is
// what a float64 is.

// undefinedValue is the type of Undefined.
type undefinedValue struct{}

// Undefined is the Go value of JavaScript's undefined, which lib0 encodes
// apart from null.
var Undefined = undefinedValue{}

// lib0 "any" tags.
const (
	anyTagUndefined = 127
	anyTagNull      = 126
	anyTagInteger   = 125
	anyTagFloat32   = 124
	anyTagFloat64   = 123
	anyTagBigInt    = 122
	anyTagFalse     = 121
	anyTagTrue      = 120
	anyTagString    = 119
	anyTagObject    = 118
	anyTagArray     = 117
	anyTagBytes     = 116
)

// EncodeValue is the Value of the Go value v, and whether v is one of the
// Go values listed above (a string must be valid UTF-8).
func EncodeValue(v any) (Value, bool) {
	e := &encoder{}
	if !writeAny(e, v) {
		return nil, false
	}
	return e.buf, true
}

// DecodeValue is the Go value that value encodes, and whether value is the
// encoding of exactly one value.
func DecodeValue(value Value) (decoded any, ok bool) {
	defer func() {
		if recover() != nil {
			decoded, ok = nil, false
		}
	}()
	d := &decoder{buf: value}
	decoded = readAny(d)
	if d.pos != len(d.buf) {
		return nil, false
	}
	return decoded, true
}

// SetValue writes the Go value v under key (Map.Set of its encoding), and
// reports whether v could be encoded.
func (m *Map) SetValue(key string, v any) bool {
	value, ok := EncodeValue(v)
	if !ok {
		return false
	}
	m.Set(key, value)
	return true
}

// SetValueIn writes the Go value v under key inside the transaction tr.
func (m *Map) SetValueIn(tr *Transaction, key string, v any) bool {
	value, ok := EncodeValue(v)
	if !ok {
		return false
	}
	m.SetIn(tr, key, value)
	return true
}

// GetValue returns the Go value under key and whether there is one
// (Map.Get decoded).
func (m *Map) GetValue(key string) (any, bool) {
	value, ok := m.Get(key)
	if !ok {
		return nil, false
	}
	return DecodeValue(value)
}

// Entries returns the Go values of every key that has one (Yjs v13
// ymap.toJSON for a map of plain values).
func (m *Map) Entries() map[string]any {
	entries := map[string]any{}
	for _, key := range m.Keys() {
		if v, ok := m.GetValue(key); ok {
			entries[key] = v
		}
	}
	return entries
}

// writeNumber writes a JavaScript number as lib0 does (encoding.js:551-563):
// an integer of at most 31 bits as a varInt, otherwise a float32 when it is
// one exactly, otherwise a float64.
func writeNumber(e *encoder, n float64) {
	if n == math.Trunc(n) && math.Abs(n) <= 0x7fffffff {
		e.writeU8(anyTagInteger)
		writeVarInt(e, n)
		return
	}
	if float64(float32(n)) == n {
		e.writeU8(anyTagFloat32)
		e.buf = binary.BigEndian.AppendUint32(e.buf, math.Float32bits(float32(n)))
		return
	}
	e.writeU8(anyTagFloat64)
	e.buf = binary.BigEndian.AppendUint64(e.buf, math.Float64bits(n))
}

// writeVarInt writes an integer as lib0's writeVarInt (encoding.js:273-290):
// the sign in bit 6 of the first byte, six bits there and seven in every
// later byte, bit 7 saying that another byte follows. n is an integer of at
// most 31 bits; negative zero keeps its sign, as in lib0.
func writeVarInt(e *encoder, n float64) {
	negative := math.Signbit(n)
	magnitude := uint64(math.Abs(n))
	first := byte(magnitude & 0x3f)
	if negative {
		first |= 0x40
	}
	if magnitude > 0x3f {
		first |= 0x80
	}
	e.writeU8(first)
	magnitude >>= 6
	for magnitude > 0 {
		b := byte(magnitude & 0x7f)
		if magnitude > 0x7f {
			b |= 0x80
		}
		e.writeU8(b)
		magnitude >>= 7
	}
}

// maxExactInteger is the largest integer up to which a float64 holds every
// integer exactly (JavaScript's Number.MAX_SAFE_INTEGER).
const maxExactInteger = 1<<53 - 1

func writeInteger(e *encoder, n int64) {
	if n >= -maxExactInteger && n <= maxExactInteger {
		writeNumber(e, float64(n))
		return
	}
	e.writeU8(anyTagBigInt)
	e.buf = binary.BigEndian.AppendUint64(e.buf, uint64(n))
}

func writeAny(e *encoder, v any) bool {
	switch x := v.(type) {
	case nil:
		e.writeU8(anyTagNull)
	case undefinedValue:
		e.writeU8(anyTagUndefined)
	case bool:
		if x {
			e.writeU8(anyTagTrue)
		} else {
			e.writeU8(anyTagFalse)
		}
	case float64:
		writeNumber(e, x)
	case float32:
		writeNumber(e, float64(x))
	case int:
		writeInteger(e, int64(x))
	case int8:
		writeInteger(e, int64(x))
	case int16:
		writeInteger(e, int64(x))
	case int32:
		writeInteger(e, int64(x))
	case int64:
		writeInteger(e, x)
	case uint8:
		writeInteger(e, int64(x))
	case uint16:
		writeInteger(e, int64(x))
	case uint32:
		writeInteger(e, int64(x))
	case uint:
		if uint64(x) > math.MaxInt64 {
			return false
		}
		writeInteger(e, int64(x))
	case uint64:
		if x > math.MaxInt64 {
			return false
		}
		writeInteger(e, int64(x))
	case string:
		if !utf8.ValidString(x) {
			return false
		}
		e.writeU8(anyTagString)
		e.writeVarString(x)
	case []byte:
		e.writeU8(anyTagBytes)
		e.writeVarUint(uint64(len(x)))
		e.buf = append(e.buf, x...)
	case []any:
		e.writeU8(anyTagArray)
		e.writeVarUint(uint64(len(x)))
		for _, element := range x {
			if !writeAny(e, element) {
				return false
			}
		}
	case map[string]any:
		// lib0 writes the keys in the object's own order; a Go map has
		// none, so they are written sorted. A reader does not depend on
		// the order.
		keys := make([]string, 0, len(x))
		for key := range x {
			if !utf8.ValidString(key) {
				return false
			}
			keys = append(keys, key)
		}
		sort.Strings(keys)
		e.writeU8(anyTagObject)
		e.writeVarUint(uint64(len(keys)))
		for _, key := range keys {
			e.writeVarString(key)
			if !writeAny(e, x[key]) {
				return false
			}
		}
	default:
		return false
	}
	return true
}

// readVarInt reads an integer written by writeVarInt (lib0 decoding.js
// readVarInt, :287).
func readVarInt(d *decoder) float64 {
	first := d.readU8()
	magnitude := uint64(first & 0x3f)
	negative := first&0x40 != 0
	shift := uint(6)
	more := first&0x80 != 0
	for more {
		b := d.readU8()
		magnitude |= uint64(b&0x7f) << shift
		shift += 7
		more = b&0x80 != 0
		if shift > 70 {
			panic("varInt out of range")
		}
	}
	if negative {
		if magnitude == 0 {
			return math.Copysign(0, -1)
		}
		return -float64(magnitude)
	}
	return float64(magnitude)
}

// readBytes reads n bytes; out of range panics, as the reader's other
// methods do (the decoders recover).
func readBytes(d *decoder, n uint64) []byte {
	if n > uint64(len(d.buf)-d.pos) {
		panic("out of range")
	}
	b := d.buf[d.pos : d.pos+int(n)]
	d.pos += int(n)
	return b
}

func readAny(d *decoder) any {
	switch tag := d.readU8(); tag {
	case anyTagUndefined:
		return Undefined
	case anyTagNull:
		return nil
	case anyTagInteger:
		return readVarInt(d)
	case anyTagFloat32:
		return float64(math.Float32frombits(binary.BigEndian.Uint32(readBytes(d, 4))))
	case anyTagFloat64:
		return math.Float64frombits(binary.BigEndian.Uint64(readBytes(d, 8)))
	case anyTagBigInt:
		return int64(binary.BigEndian.Uint64(readBytes(d, 8)))
	case anyTagFalse:
		return false
	case anyTagTrue:
		return true
	case anyTagString:
		return string(readBytes(d, d.readVarUint()))
	case anyTagObject:
		count := d.readVarUint()
		object := map[string]any{}
		for i := uint64(0); i < count; i++ {
			key := string(readBytes(d, d.readVarUint()))
			object[key] = readAny(d)
		}
		return object
	case anyTagArray:
		count := d.readVarUint()
		array := []any{}
		for i := uint64(0); i < count; i++ {
			array = append(array, readAny(d))
		}
		return array
	case anyTagBytes:
		return append([]byte{}, readBytes(d, d.readVarUint())...)
	default:
		panic("unknown any tag")
	}
}

// readAnyBytes reads one any value and returns the bytes it occupies: the
// Value an any content keeps (content.go).
func readAnyBytes(d *decoder) Value {
	start := d.pos
	readAny(d)
	return append(Value{}, d.buf[start:d.pos]...)
}
