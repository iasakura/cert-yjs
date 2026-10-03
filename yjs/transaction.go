package yjs

// The transaction: the scope of one write to the document (issue #206, T1;
// docs/plan-issue-198-observe.md, Part II).
//
// References (issue #208): Yjs v14.0.0-rc.18 src/utils/Transaction.js (the
// Transaction class :45, transact :391); yrs 0.27.2 src/transaction.rs
// (TransactionMut :445, commit :1031) and src/transact.rs (transact_mut :131);
// y-octo 0.1.0 has no transaction, each operation takes the store's RwLock on
// its own (doc/types/text.rs). Where the three differ, the difference is
// noted at the spot. The methods that record into the transaction (integrate,
// deleteNode, the delete and update loops) are the transaction's, as yrs
// has them (TransactionMut::integrate src/block.rs:984, apply_update
// src/transaction.rs:820, apply_delete :633, delete :732); Yjs passes the
// transaction and the store to free functions (integrateStructs,
// src/utils/encoding.js:97) and y-octo's are store methods that record
// nothing. The store (store.go) keeps the structural primitives, which record
// nothing, so that it knows nothing of transactions.

// Transaction is the scope of one write to the document (Yjs v14 Transaction,
// src/utils/Transaction.js:45; yrs TransactionMut, src/transaction.rs:445;
// y-octo has none): created by transact under the store's write lock, passed
// to every write made inside, closed by transact, which notifies the
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
// explicitly, as Yjs's internals and yrs do (#206, item 2). It carries the
// store it is a transaction of (Yjs transaction.doc, Transaction.js:56; yrs
// TransactionMut.store, the write guard itself): a write inside the
// transaction reaches the store's clock and run lists through tr, and the
// type it edits through its Text handle. Nothing checks that the two belong
// to the same document (Yjs and yrs do not either).
//
// The record is written at the two mutation points, where Yjs and yrs write
// it: integrate (Item.integrate, src/structs/Item.js:270-274; yrs
// src/block.rs:1085-1090) and deleteNode (Item.delete, src/structs/Item.js:366-375;
// yrs src/block.rs:635). A split (store.splitNode) records nothing: the right
// half carries ids that were already integrated (Yjs pushes it to
// _mergeStructs, #206 T3).
type Transaction struct {
	store     *store
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

// integrate integrates item into parent and records it (yrs
// TransactionMut::integrate, src/block.rs:984; Yjs Item.integrate records
// into the transaction it is handed, src/structs/Item.js:270-274): the
// store's Integrate, then recordInsert for the parent it went into. A nil
// parent means the item's own, as resolved by store.repair; an item whose
// parent did not resolve is dropped by the store and records nothing.
func (tr *Transaction) integrate(parent *yType, item *item) {
	p := tr.store.Integrate(parent, item)
	if p != nil {
		tr.recordInsert(p, item)
	}
}

// deleteNode tombstones one node and records it when it was live (yrs
// TransactionMut::delete, src/transaction.rs:732; Yjs Item.delete,
// src/structs/Item.js:366-375): the store's deleteNode, then recordDelete.
func (tr *Transaction) deleteNode(it *item) {
	if deleteNode(it) {
		tr.recordDelete(it)
	}
}

// deleteRange tombstones every integrated char of the half-open clock range
// [clock, clock+length) in client's clock space (y-octo:
// DocStore::delete_range, store.rs). Each step resolves the current char to
// the node STARTING at it (splitAtAndGetRight, splitting when the range starts
// inside a run), truncates that node at the range end when it would overrun
// (splitAtAndGetLeft on the range's last char), and tombstones it whole, so
// the deletion covers exactly the requested chars and never spills over. Both
// splits are the same clean-start / clean-end helpers store.repair resolves
// origins with.
//
// A char with no integrated node is skipped: its struct has not arrived, and
// the caller re-applies the span later (the pending discipline of issue #40).
// An already-tombstoned node is skipped too, which is what makes
// re-application harmless. Runs inside the transaction, which holds the
// store's write lock and records what gets tombstoned (deleteNode).
func (tr *Transaction) deleteRange(client Client, clock uint64, length uint64) bool {
	s := tr.store
	covered := true
	end := clock + length
	cur := clock
	for cur < end {
		// The lookup and the clean-start split search the run list twice
		// (y-octo searches once and keeps the index); the redundant lookup
		// is what lets the two steps be verified independently.
		_, found := s.GetNode(newId(client, cur))
		if !found {
			// not integrated yet: leave it for a later re-application.
			covered = false
			cur = cur + 1
		} else {
			// clean start: after this, [it] begins exactly at [cur].
			it, _ := s.splitAtAndGetRight(newId(client, cur))
			next := it.id.clock + it.Len()
			if end < next {
				// clean end: the range stops inside [it], so truncate it in
				// place at the range's last char. [it] is the left half, so
				// it now covers exactly [cur, end).
				s.splitAtAndGetLeft(newId(client, end-1))
				next = end
			}
			tr.deleteNode(it)
			cur = next
		}
	}
	return covered
}

// applyDeleteSpans applies a batch of decoded delete spans on top of the
// buffered ones, keeping the spans that did not land in full because their
// target structs have not arrived (y-octo: the pending half of
// Update::delete_set). Re-applying a span that already landed is harmless:
// deleteRange skips tombstoned nodes. Runs inside the transaction, which
// holds the store's write lock.
func (tr *Transaction) applyDeleteSpans(spans []deleteSpan) {
	s := tr.store
	all := s.pendingDeletes
	// Take the buffer out before retrying it (y-octo's mem::take of the
	// pending set): while the retry loop runs, the store holds no buffered
	// spans, and the ones that did not land are installed at the end.
	s.pendingDeletes = nil
	for i := 0; i < len(spans); i++ {
		all = append(all, spans[i])
	}
	rest := []deleteSpan{}
	for i := 0; i < len(all); i++ {
		sp := all[i]
		if !tr.deleteRange(sp.client, sp.clock, sp.length) {
			rest = append(rest, sp)
		}
	}
	s.pendingDeletes = rest
}

// integrateDecoded builds, repairs and integrates one decoded struct whose
// dependencies have arrived: the ready branch of applyUpdate's drain,
// extracted so the per-struct integration contract is provable in isolation
// (mirrors the findIntegrationLeft / integrateCore extractions).
func (tr *Transaction) integrateDecoded(ui updateItem) {
	s := tr.store
	it := newItem(ui.id, ui.content, ui.originLeftId, ui.originRightId)
	s.repair(it, ui.parentName)
	tr.integrate(nil, it)
}

// applyUpdate integrates a decoded batch of insert structs, in any order and
// under no causal-closure assumption, buffering what cannot integrate yet
// (issue #40; y-octo: the Doc::apply_update fixpoint over UpdateIterator and
// DocStore.pending, document.rs / codec/update.rs). The `pending` local is the store's
// pending buffer plus the new batch. A struct whose id is already integrated
// is dropped (a re-delivery; y-octo's offset >= len case). A struct whose
// dependencies have all arrived (depsArrived) is repaired and integrated
// (integrateDecoded); the rest is retried, pass after pass, until a
// pass integrates nothing, and the remainder becomes the new pending buffer,
// drained by later calls. Structs that can never resolve a parent (no
// origins and no parentName, which the wire format never produces) are
// dropped inside Integrate, as in y-octo.
//
// Structural deviations from y-octo (deliberate, reported; see
// docs/plan-issue-40-pending.md, section 3):
//   - the round-based fixpoint replaces UpdateIterator's stack-based
//     dependency chase; both integrate exactly the least
//     structural-dependency closure of the pending over the store, the chase
//     being a within-pass shortcut for the later passes;
//   - the pending buffer is re-drained on every call instead of gated on
//     missing_state thresholds; the threshold is a retry optimization, and
//     y-octo drops the stored thresholds when merging pending updates
//     (document.rs merge branch), a liveness defect this port avoids;
//   - pending re-deliveries are dropped by id on requeue rather than by
//     merge_into's structural comparison (certified ids determine their
//     struct);
//   - the loop lives on the transaction rather than on Doc (yrs
//     TransactionMut::apply_update, src/transaction.rs:820), so the verified
//     core stays self-contained; Doc.applyUpdate (doc.go) is the transaction
//     wrapper and the codec-level Doc.ApplyUpdate (codec.go) the decode rind.
//
// Runs inside the transaction, which holds the store's write lock and records
// every struct this call integrates.
func (tr *Transaction) applyUpdate(structs []updateItem) {
	s := tr.store
	pending := s.pending
	for i := 0; i < len(structs); i++ {
		pending = append(pending, structs[i])
	}
	s.pending = nil
	progress := true
	for progress {
		progress = false
		rest := []updateItem{}
		for i := 0; i < len(pending); i++ {
			ui := pending[i]
			if s.hasNode(ui.id) {
				// already integrated: a duplicate delivery, dropped.
				continue
			}
			if s.depsArrived(ui) {
				tr.integrateDecoded(ui)
				progress = true
			} else if !containsUpdateItemId(rest, ui.id) {
				rest = append(rest, ui)
			}
		}
		pending = rest
	}
	s.pending = pending
}

// transact runs f as one transaction: lock, f, notify, unlock (Yjs transact,
// src/utils/Transaction.js:391-422, without the reentrant branch; yrs
// transact_mut takes the store's write guard and commits on drop,
// src/transact.rs:131, src/transaction.rs:488). The store's write lock is the
// transaction's critical section. A free function over the store, since the
// transaction is created inside. Go has no goroutine identity, so a nested
// transact cannot be recognised and deadlocks (#206, item 2): f uses the
// In-variants (Text.InsertIn / DeleteIn / StringIn) with tr and never locks
// the document, and the callbacks notify runs receive their delta and must
// not touch the document at all (Text.Observe).
func transact(s *store, f func(tr *Transaction)) {
	s.mu.Lock()
	tr := newTransaction(s)
	f(tr)
	tr.notify()
	s.mu.Unlock()
}

// notify is the end of the transaction, the observer half of Yjs's
// cleanupTransactions (src/utils/Transaction.js:231-236; yrs commit's
// call_observers, src/transaction.rs:978): for every type the transaction
// changed and somebody observes, one walk yields the delta (textDelta),
// shared by that type's callbacks. Go map order: the types are notified in no
// particular order (Yjs: the insertion order of changed). Runs under the
// store's write lock, which the callbacks inherit (Text.Observe).
func (tr *Transaction) notify() {
	s := tr.store
	for ty := range tr.changed {
		callbacks := s.observers[ty]
		if len(callbacks) > 0 {
			delta := textDelta(ty, tr.insertSet, tr.deleteSet)
			for i := 0; i < len(callbacks); i++ {
				callbacks[i](delta)
			}
		}
	}
}

// newTransaction is an empty transaction record (Yjs's Transaction
// constructor, src/utils/Transaction.js:51). Only transact opens one; the
// tests call the transaction's internals on a fresh record where a
// transaction would have handed theirs.
func newTransaction(s *store) *Transaction {
	return &Transaction{store: s, insertSet: nil, deleteSet: nil, changed: make(map[*yType]bool)}
}

// Transact runs f as one transaction on the document (Yjs doc.transact,
// src/utils/Doc.js:179; yrs Doc::transact_mut): every write inside is one
// unit, and the observers of the types it changed are called once at its end.
// f must not lock the document again (no Transact, Insert, Delete,
// ApplySyncUpdate, String or Len on the same document: deadlock, #206 item
// 2); it uses the In-variants with tr.
func (d *Doc) Transact(f func(tr *Transaction)) {
	transact(d.store, f)
}
