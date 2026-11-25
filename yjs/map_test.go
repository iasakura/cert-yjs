package yjs

import (
	"encoding/hex"
	"reflect"
	"sort"
	"testing"
)

// unhex is the bytes of a hexadecimal fixture.
func unhex(t *testing.T, s string) []byte {
	t.Helper()
	b, err := hex.DecodeString(s)
	if err != nil {
		t.Fatalf("bad fixture %q: %v", s, err)
	}
	return b
}

// observedUpdates registers an update observer on doc and returns the list
// its updates are appended to, as hexadecimal.
func observedUpdates(doc *Doc) *[]string {
	var updates []string
	doc.ObserveUpdate(WireEncoder(), func(update []byte, origin Origin) {
		updates = append(updates, hex.EncodeToString(update))
	})
	return &updates
}

// Set, Get, Has, Delete, Keys and Len on one replica.
func TestMapSetGetDelete(t *testing.T) {
	doc := NewDoc(1)
	m := doc.GetOrCreateMap("root")
	if _, ok := m.GetValue("k"); ok || m.Has("k") || m.Len() != 0 {
		t.Fatal("an empty map has an entry")
	}
	m.SetValue("k", "v")
	m.SetValue("other", 1.5)
	if v, ok := m.GetValue("k"); !ok || v != "v" {
		t.Fatalf("Get(k) = %v, %v, want v, true", v, ok)
	}
	m.SetValue("k", 2)
	if v, ok := m.GetValue("k"); !ok || v != 2.0 {
		t.Fatalf("after the overwrite Get(k) = %v, %v, want 2, true", v, ok)
	}
	keys := m.Keys()
	sort.Strings(keys)
	if !reflect.DeepEqual(keys, []string{"k", "other"}) || m.Len() != 2 {
		t.Fatalf("Keys() = %v, Len() = %d", keys, m.Len())
	}
	m.Delete("k")
	m.Delete("absent")
	if _, ok := m.GetValue("k"); ok || m.Has("k") || m.Len() != 1 {
		t.Fatal("a deleted key still has an entry")
	}
	m.SetValue("k", nil)
	if v, ok := m.GetValue("k"); !ok || v != nil {
		t.Fatalf("after set-delete-set Get(k) = %v, %v, want nil, true", v, ok)
	}
	if want := map[string]any{"k": nil, "other": 1.5}; !reflect.DeepEqual(m.Entries(), want) {
		t.Fatalf("Entries() = %v, want %v", m.Entries(), want)
	}
}

// The updates of map writes are byte for byte what Yjs 13.6.33 emits for the
// same edits (doc.on('update') on a document with clientID 1, gc off, a
// Y.Map named root): set k to "v", set k to 2, delete k, set k to null. The
// overwrite carries the delete of the entry it replaces.
func TestMapUpdateBytesMatchYjs(t *testing.T) {
	doc := NewDoc(1)
	m := doc.GetOrCreateMap("root")
	updates := observedUpdates(doc)
	m.SetValue("k", "v")
	m.SetValue("k", 2)
	m.Delete("k")
	m.SetValue("k", nil)
	want := []string{
		"01010100280104726f6f74016b0177017600",
		"01010101a80100017d020101010001",
		"000101010101",
		"01010102a80101017e00",
	}
	if !reflect.DeepEqual(*updates, want) {
		t.Fatalf("updates:\n got %v\nwant %v", *updates, want)
	}

	// a replica that applies them, in order or with the first one last,
	// reads the same entries
	for _, order := range [][]int{{0, 1, 2, 3}, {1, 2, 3, 0}, {3, 2, 1, 0}} {
		other := NewDoc(2)
		for _, i := range order {
			if !other.ApplyEncodedUpdate(WireCodec(), unhex(t, want[i]), "provider") {
				t.Fatalf("order %v: update %d did not decode", order, i)
			}
		}
		if got, wantEntries := other.GetOrCreateMap("root").Entries(), (map[string]any{"k": nil}); !reflect.DeepEqual(got, wantEntries) {
			t.Fatalf("order %v: entries %v, want %v", order, got, wantEntries)
		}
	}
}

// One update per kind of value, as Yjs 13.6.33 emits it for ymap.set(key,
// value) (clientID 1, a Y.Map named root, the keys in this order), and the
// Go value it reads back as. The Go writes the same bytes for the same
// values.
func TestMapValueBytesMatchYjs(t *testing.T) {
	cases := []struct {
		key    string
		value  any
		update string
	}{
		{"t", true, "01010100280104726f6f740174017800"},
		{"f", false, "01010101280104726f6f740166017900"},
		{"n", nil, "01010102280104726f6f74016e017e00"},
		{"i", 7, "01010103280104726f6f740169017d0700"},
		{"neg", -3, "01010104280104726f6f74036e6567017d4300"},
		{"big", float64(1 << 40), "01010105280104726f6f7403626967017c5380000000"},
		{"fl", 1.5, "01010106280104726f6f7402666c017c3fc0000000"},
		{"dbl", 0.1, "01010107280104726f6f740364626c017b3fb999999999999a00"},
		{"s", "こんにちは😀", "01010108280104726f6f740173017713e38193e38293e381abe381a1e381aff09f988000"},
		{"a", []any{1, "x", nil}, "01010109280104726f6f7401610175037d017701787e00"},
		{"o", map[string]any{"a": []any{true}}, ""},
		{"e", "", "0101010b280104726f6f74016501770000"},
		{"z", 0, "0101010c280104726f6f74017a017d0000"},
		{"m31", 1<<31 - 1, "0101010d280104726f6f74036d3331017dbfffffff0f00"},
		{"p31", 1 << 31, "0101010e280104726f6f7403703331017c4f00000000"},
	}
	doc := NewDoc(1)
	m := doc.GetOrCreateMap("root")
	updates := observedUpdates(doc)
	for _, c := range cases {
		if !m.SetValue(c.key, c.value) {
			t.Fatalf("SetValue(%q, %v) refused the value", c.key, c.value)
		}
	}
	for i, c := range cases {
		if c.update != "" && (*updates)[i] != c.update {
			t.Errorf("update of %q:\n got %s\nwant %s", c.key, (*updates)[i], c.update)
		}
	}

	// the Yjs updates, applied to a fresh replica (the object's update is
	// Yjs's own, with its two keys in Yjs's order)
	other := NewDoc(2)
	for i, c := range cases {
		update := c.update
		if c.key == "o" {
			update = "0101010a280104726f6f74016f01760201627d01016175017800"
		}
		if !other.ApplyEncodedUpdate(WireCodec(), unhex(t, update), "provider") {
			t.Fatalf("update %d (%q) did not decode", i, c.key)
		}
	}
	want := map[string]any{
		"t": true, "f": false, "n": nil, "i": 7.0, "neg": -3.0, "big": float64(1 << 40),
		"fl": 1.5, "dbl": 0.1, "s": "こんにちは😀", "a": []any{1.0, "x", nil},
		"o": map[string]any{"b": 1.0, "a": []any{true}}, "e": "", "z": 0.0,
		"m31": float64(1<<31 - 1), "p31": float64(1 << 31),
	}
	if got := other.GetOrCreateMap("root").Entries(); !reflect.DeepEqual(got, want) {
		t.Fatalf("entries:\n got %v\nwant %v", got, want)
	}
}

// Concurrent writes of one key: the updates are Yjs 13.6.33's (clients 1, 2
// and 3), and whatever order a replica applies them in, it reads the value
// Yjs reads. First both set k from an empty map (the higher client id wins);
// then both overwrite the result while a third replica deletes it.
func TestMapConcurrentSetsMatchYjs(t *testing.T) {
	first := []string{
		"01010100280104726f6f74016b01770666726f6d203100",
		"01010200280104726f6f74016b01770666726f6d203200",
	}
	second := []string{
		"01010101a80200017707616761696e20310102010001",
		"01010201a80200017707616761696e20320102010001",
		"000102010001",
	}
	apply := func(doc *Doc, updates []string, order []int) {
		for _, i := range order {
			if !doc.ApplyEncodedUpdate(WireCodec(), unhex(t, updates[i]), "provider") {
				t.Fatalf("update %d did not decode", i)
			}
		}
	}
	for _, firstOrder := range [][]int{{0, 1}, {1, 0}} {
		for _, secondOrder := range [][]int{{0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}} {
			doc := NewDoc(9)
			m := doc.GetOrCreateMap("root")
			apply(doc, first, firstOrder)
			if v, ok := m.GetValue("k"); !ok || v != "from 2" {
				t.Fatalf("first round in order %v: Get(k) = %v, %v, want from 2", firstOrder, v, ok)
			}
			apply(doc, second, secondOrder)
			if v, ok := m.GetValue("k"); !ok || v != "again 2" {
				t.Fatalf("orders %v then %v: Get(k) = %v, %v, want again 2", firstOrder, secondOrder, v, ok)
			}
			if m.Len() != 1 {
				t.Fatalf("orders %v then %v: Len() = %d, want 1", firstOrder, secondOrder, m.Len())
			}
		}
	}

	// the second round before the first: its structs wait for the entry
	// they were written next to
	doc := NewDoc(9)
	apply(doc, second, []int{2, 1, 0})
	if doc.GetOrCreateMap("root").Len() != 0 {
		t.Fatal("writes whose left origin has not arrived were applied")
	}
	apply(doc, first, []int{1, 0})
	if v, ok := doc.GetOrCreateMap("root").GetValue("k"); !ok || v != "again 2" {
		t.Fatalf("second round first: Get(k) = %v, %v, want again 2", v, ok)
	}
}

// Two Go replicas that write one key concurrently and exchange their update
// events read the same value, the one the Yjs fixture above has for the
// same client ids, and so does a replica that loads the whole state.
func TestMapConcurrentSetsConverge(t *testing.T) {
	docA, docB := NewDoc(1), NewDoc(2)
	mapA, mapB := docA.GetOrCreateMap("root"), docB.GetOrCreateMap("root")
	updatesA, updatesB := observedUpdates(docA), observedUpdates(docB)
	mapA.SetValue("k", "from 1")
	mapB.SetValue("k", "from 2")
	mapA.SetValue("only A", true)
	fromA, fromB := append([]string{}, *updatesA...), append([]string{}, *updatesB...)
	for _, update := range fromB {
		docA.ApplyEncodedUpdate(WireCodec(), unhex(t, update), "provider")
	}
	for _, update := range fromA {
		docB.ApplyEncodedUpdate(WireCodec(), unhex(t, update), "provider")
	}
	want := map[string]any{"k": "from 2", "only A": true}
	if a, b := mapA.Entries(), mapB.Entries(); !reflect.DeepEqual(a, want) || !reflect.DeepEqual(b, want) {
		t.Fatalf("A %v, B %v, want %v", a, b, want)
	}

	fresh := NewDoc(3)
	if !fresh.ApplyEncodedUpdate(WireCodec(), docA.EncodeUpdate(), "provider") {
		t.Fatal("the whole state did not decode")
	}
	if got := fresh.GetOrCreateMap("root").Entries(); !reflect.DeepEqual(got, want) {
		t.Fatalf("after loading the whole state: %v, want %v", got, want)
	}
}

// A text and a map in one document, and under one name: the list and the
// entries of a type do not disturb each other. The update bytes of the two
// writes under different names are Yjs 13.6.33's.
func TestMapAndTextInOneDocument(t *testing.T) {
	doc := NewDoc(1)
	updates := observedUpdates(doc)
	doc.GetOrCreateText("note").InsertString(0, "hi")
	doc.GetOrCreateMap("meta").SetValue("title", "x")
	want := []string{
		"010101000401046e6f746502686900",
		"010101022801046d657461057469746c650177017800",
	}
	if !reflect.DeepEqual(*updates, want) {
		t.Fatalf("updates:\n got %v\nwant %v", *updates, want)
	}

	text, entries := doc.GetOrCreateText("both"), doc.GetOrCreateMap("both")
	text.InsertString(0, "abc")
	entries.SetValue("k", 1)
	text.Delete(1, 1)
	entries.SetValue("k", 2)
	if got := text.String(); got != "ac" || text.Len() != 2 {
		t.Fatalf("text %q of length %d, want ac of length 2", got, text.Len())
	}
	if v, ok := entries.GetValue("k"); !ok || v != 2.0 {
		t.Fatalf("Get(k) = %v, %v, want 2", v, ok)
	}

	other := NewDoc(2)
	if !other.ApplyEncodedUpdate(WireCodec(), doc.EncodeUpdate(), "provider") {
		t.Fatal("the whole state did not decode")
	}
	if got := other.GetOrCreateText("both").String(); got != "ac" {
		t.Fatalf("the other replica reads text %q, want ac", got)
	}
	if v, ok := other.GetOrCreateMap("both").GetValue("k"); !ok || v != 2.0 {
		t.Fatalf("the other replica reads Get(k) = %v, %v, want 2", v, ok)
	}
	if v, ok := other.GetOrCreateMap("meta").GetValue("title"); !ok || v != "x" {
		t.Fatalf("the other replica reads Get(title) = %v, %v, want x", v, ok)
	}
}

// The whole state of a Yjs 13.6.33 document after set, overwrite, delete and
// set again: Yjs has merged the two replaced entries into one struct of two
// values, which the decoder splits. The key has the last value.
func TestMapReadsYjsStateWithMergedEntries(t *testing.T) {
	state := "01020100280104726f6f74016b027701767d02a80101017e0101010002"
	doc := NewDoc(2)
	if !doc.ApplyEncodedUpdate(WireCodec(), unhex(t, state), "provider") {
		t.Fatal("the state did not decode")
	}
	m := doc.GetOrCreateMap("root")
	if v, ok := m.GetValue("k"); !ok || v != nil || m.Len() != 1 {
		t.Fatalf("Get(k) = %v, %v with Len() = %d, want nil, true and 1", v, ok, m.Len())
	}
}

// EncodeValue and DecodeValue round-trip the Go values, and refuse what is
// not one.
func TestValueRoundTrip(t *testing.T) {
	values := []any{
		nil, Undefined, true, false, 0.0, -1.0, 1e100, int64(1) << 60, "", "a😀",
		[]byte{1, 2, 3}, []any{}, []any{[]any{nil}}, map[string]any{}, map[string]any{"a": map[string]any{"b": 1.0}},
	}
	for _, v := range values {
		encoded, ok := EncodeValue(v)
		if !ok {
			t.Fatalf("EncodeValue(%v) refused the value", v)
		}
		decoded, ok := DecodeValue(encoded)
		if !ok || !reflect.DeepEqual(decoded, v) {
			t.Fatalf("round trip of %v (%T): %v (%T), %v", v, v, decoded, decoded, ok)
		}
	}
	if _, ok := EncodeValue(struct{}{}); ok {
		t.Fatal("EncodeValue accepted a struct")
	}
	if _, ok := EncodeValue("\xff"); ok {
		t.Fatal("EncodeValue accepted a string that is not UTF-8")
	}
	for _, bad := range [][]byte{nil, {119, 5, 'a'}, {126, 126}, {1}} {
		if _, ok := DecodeValue(bad); ok {
			t.Fatalf("DecodeValue accepted %v", bad)
		}
	}
}
