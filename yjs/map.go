package yjs

// Map-type API: a root type used as a map from keys to values. The
// references name it differently. Yjs v14.0.0-rc.18 has one type with a list
// and a map, and the map's operations are that type's attribute methods
// (YType.setAttr / getAttr / deleteAttr / hasAttr / attrKeys / attrSize,
// src/ytype.js:1169, :1182, :1153, :1194, :1426, :1453, over typeMapSet /
// typeMapGet / typeMapDelete / typeMapHas, :1818, :1860, :1802, :1974); in
// Yjs v13 the same operations were Y.Map's set / get / delete / has / keys /
// size. yrs 0.27.2 keeps a handle per use of the type, MapRef, with the Map
// trait's insert / get / remove / contains_key / keys / len
// (src/types/map.rs:189, :308, :290, :379, :168, :154). The Go follows yrs
// in having a handle, as Text is one (text.go), and takes the method names of
// Yjs v13's Y.Map.
//
// A value is the encoding of a JSON-like value (Value, content.go). Nested
// types and documents as values, which both references accept, are not
// implemented, and neither are the map's events (Yjs YEvent keys, yrs
// MapEvent): Text.Observe is not told of a change to the entries.
//
// These methods are goose-translated like Text's: SetIn creates one item
// with the key and integrates it through the same Transaction.integrate as
// a text insert.

// Map is the public handle for a root type used as a map. It carries the
// store (for the lock, the client and the clock) and the inner yType whose
// entries it reads and writes, as Text does for the list.
type Map struct {
	store *storeRef
	inner *yType
}

// Set writes value under key as one transaction (Yjs ymap.set outside a
// transact; yrs MapRef::insert with a transact_mut).
func (m *Map) Set(key string, value Value) {
	transact(m.store, NoOrigin, func(tr *Transaction) {
		m.SetIn(tr, key, value)
	})
}

// SetIn writes value under key inside the transaction tr (Yjs v14.0.0-rc.18
// typeMapSet, src/ytype.js:1818-1848; yrs 0.27.2 Map::insert,
// src/types/map.rs:189-215): one item with the key and the one value as an
// any content, created to the right of the key's current entry, with that
// entry's last id as its left origin and no right origin. Integrating it
// makes it the key's entry and deletes the one it replaces
// (Transaction.integrate). The value is kept, so the caller must not write to
// it afterwards (content.go).
func (m *Map) SetIn(tr *Transaction, key string, value Value) {
	s := tr.store
	// Guard against clock overflow, as Text.InsertIn does: refuse the write
	// and leave the document unchanged.
	if s.clock+1 < s.clock {
		return
	}
	left := m.inner.entries[key]
	var originLeftId *id
	if left != nil {
		leftId := left.LastId()
		originLeftId = &leftId
	}
	clock := s.clock
	s.clock = clock + 1

	entryKey := key
	entry := newItem(newId(s.client, clock), contentOfValue(value), originLeftId, nil)
	entry.left = left
	entry.parent = m.inner
	entry.parentSub = &entryKey
	tr.integrate(m.inner, entry)
}

// Get returns the value under key and whether there is one (Yjs ymap.get,
// which returns undefined when there is none; yrs MapRef::get, an Option). A
// pure read under the read lock. The value is the entry's own and must not
// be written to.
func (m *Map) Get(key string) (Value, bool) {
	s := m.store
	s.rlock()
	value, ok := m.inner.entryValue(key)
	s.runlock()
	return value, ok
}

// GetIn returns the value under key inside the transaction tr, which holds
// the store's write lock.
func (m *Map) GetIn(tr *Transaction, key string) (Value, bool) {
	return m.inner.entryValue(key)
}

// Delete removes the entry under key as one transaction (Yjs ymap.delete;
// yrs MapRef::remove).
func (m *Map) Delete(key string) {
	transact(m.store, NoOrigin, func(tr *Transaction) {
		m.DeleteIn(tr, key)
	})
}

// DeleteIn removes the entry under key inside the transaction tr: the key's
// current entry is deleted, and stays the key's entry (Yjs v14.0.0-rc.18
// typeMapDelete, src/ytype.js:1802-1807; yrs 0.27.2 Branch::remove,
// src/branch.rs:357). A key with no entry is left alone.
func (m *Map) DeleteIn(tr *Transaction, key string) {
	entry := m.inner.entries[key]
	if entry != nil {
		tr.deleteNode(entry)
	}
}

// Has reports whether key has a value (Yjs ymap.has; yrs
// MapRef::contains_key). A pure read under the read lock.
func (m *Map) Has(key string) bool {
	s := m.store
	s.rlock()
	has := m.inner.hasEntry(key)
	s.runlock()
	return has
}

// Keys returns the keys that have a value, in no particular order (Yjs
// ymap.keys; yrs MapRef::keys). A pure read under the read lock.
func (m *Map) Keys() []string {
	s := m.store
	s.rlock()
	keys := m.inner.entryKeys()
	s.runlock()
	return keys
}

// Len returns the number of keys that have a value (Yjs ymap.size, counted
// over the entries that are not deleted, YType.attrSize, src/ytype.js:1453;
// yrs MapRef::len, src/types/map.rs:154). A pure read under the read lock.
func (m *Map) Len() uint64 {
	s := m.store
	s.rlock()
	count := uint64(len(m.inner.entryKeys()))
	s.runlock()
	return count
}
