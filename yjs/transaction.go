package yjs

// The transaction: the scope of one write to the document (issue #206, T1;
// docs/plan-issue-198-observe.md, Part II).
//
// References (issue #208): Yjs v14.0.0-rc.18 src/utils/Transaction.js (the
// Transaction class :45, transact :391); yrs 0.27.2 src/transaction.rs
// (TransactionMut :445, commit :1031) and src/transact.rs (transact_mut :131);
// y-octo 0.1.0 has no transaction, each operation takes the store's RwLock on
// its own (doc/types/text.rs). Where the three differ, the Go follows Yjs and
// the difference is noted at the spot.

// Transaction is the scope of one write to the document (Yjs v14 Transaction,
// src/utils/Transaction.js:45; yrs TransactionMut, src/transaction.rs:445;
// y-octo has none): created by store.transact under the store's write lock,
// passed to every write made inside, closed by transact, which notifies the
// observers of the types the transaction changed (issue #198, Part II C2).
//
// Of Yjs's fields this milestone keeps the three the observer reads:
// insertSet and deleteSet record what the transaction integrated and
// tombstoned (Yjs transaction.insertSet / deleteSet, Transaction.js:60-69;
// yrs insert_set / delete_set), changed the types it wrote (Yjs
// transaction.changed, Transaction.js:86; yrs changed). Yjs's _mergeStructs,
// the merge / gc / update emit of its cleanup (#206 T3) and origin / local
// (#206 T5) come later. The two id sets are store.go's []idSpan (a head id
// and a length per span, membership by containsId), where Yjs's IdSet and
// yrs's IdSet keep per-client sorted ranges: the flat unsorted list is what
// scanConflicts already keeps its candidate sets in, and the sets are only
// appended to and queried while a transaction is open.
//
// The value is the proof of being inside the transaction: Go has no
// goroutine identity, so Yjs's doc._transaction reentrancy check
// (Transaction.js:398) has no counterpart, and the internal API takes tr
// explicitly, as Yjs's internals and yrs do (#206, item 2).
type Transaction struct {
	insertSet []idSpan
	deleteSet []idSpan
	changed   map[*yType]bool
}

// recordInsert records a freshly integrated node: its ids join the
// transaction's insert set and its parent type is marked changed (Yjs
// Item.integrate, src/structs/Item.js:270-274; yrs src/block.rs:1085-1090).
func (tr *Transaction) recordInsert(parent *yType, it *item) {
	tr.insertSet = append(tr.insertSet, idSpan{id: it.id, len: it.Len()})
	tr.changed[parent] = true
}

// recordDelete records a node this transaction tombstoned: its ids join the
// delete set and its parent type is marked changed (Yjs Item.delete,
// src/structs/Item.js:366-375; yrs src/block.rs:635).
func (tr *Transaction) recordDelete(it *item) {
	tr.deleteSet = append(tr.deleteSet, idSpan{id: it.id, len: it.Len()})
	tr.changed[it.parent] = true
}

// transact runs f as one transaction: lock, f, unlock (Yjs transact,
// src/utils/Transaction.js:391-422, without the reentrant branch; yrs
// transact_mut takes the store's write guard and commits on drop,
// src/transact.rs:131, src/transaction.rs:488). The store's write lock is the
// transaction's critical section. Go has no goroutine identity, so a nested
// transact cannot be recognised and deadlocks (#206, item 2): f uses the
// In-variants (Text.InsertIn / DeleteIn / StringIn) and never locks the
// document. The observers of the changed types are notified here before the
// unlock once they exist (issue #198, Part II C2).
func (s *store) transact(f func(tr *Transaction)) {
	s.mu.Lock()
	tr := newTransaction()
	f(tr)
	s.mu.Unlock()
}

// newTransaction is an empty transaction record (Yjs's Transaction
// constructor, src/utils/Transaction.js:51). Only transact opens one; the
// tests call the store's internals with a fresh record where a transaction
// would have handed theirs.
func newTransaction() *Transaction {
	return &Transaction{insertSet: nil, deleteSet: nil, changed: make(map[*yType]bool)}
}

// Transact runs f as one transaction on the document (Yjs doc.transact,
// src/utils/Doc.js:179; yrs Doc::transact_mut): every write inside is one
// unit, and the observers of the types it changed are called once at its end.
// f must not lock the document again (no Transact, Insert, Delete,
// ApplySyncUpdate, String or Len on the same document: deadlock, #206 item
// 2); it uses the In-variants with tr.
func (d *Doc) Transact(f func(tr *Transaction)) {
	d.store.transact(f)
}
