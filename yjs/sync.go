package yjs

// Sync-protocol execution core (y-octo: doc/store.rs get_state_vector /
// diff_state_vector; y-protocols/sync). This file holds the *verified* heart of
// the Yjs sync protocol: given the document's items already materialized as a
// decoded struct list (the input), it computes the state vector and the diff a
// peer is missing (the output). The byte-level message codec (state-vector /
// update (de)serialization and the Step1/Step2/Update framing) and the store ->
// struct-list snapshot are the unverified rind in protocol.go
// (//go:build !goose); codec verification is future work (#43).
//
// Splitting the pure decision logic out here mirrors how scanConflicts /
// findIntegrationLeft were extracted from Integrate so the hard part is provable
// in isolation (proofs: src/proof/yjs_sync.v). The three protocol messages map
// onto this core:
//   - Step1(sv):  execution = computeDiff(items, sv) -> the structs the peer is
//                 missing, returned to it as a Step2 update;
//   - Step2(u):   execution = store.applyUpdate (the proven integrate loop);
//   - Update(u):  execution = store.applyUpdate (same path as Step2).
// computeStateVector produces this replica's own Step1 payload.
//
// Deliberate divergence from y-octo (reported): both functions take a
// pre-materialized decoded item list (the snapshot) and scan it linearly, where
// y-octo walks the DocStore's per-client run map in place -- items_as_state_vector
// reads only each client's last struct (O(clients)), and diff_structs binary
// searches (get_node_index) then copies a tail. The result is identical (the same
// state vector, the same set of missing structs); the linear-over-a-snapshot shape
// is what makes the core a pure, codec-free function provable in isolation.

// svGet reads the clock a state vector records for client c, defaulting to 0 for
// a client the peer has never seen (y-octo: StateVector::get). A struct with id
// (c, k) is one the peer already holds iff k < svGet(sv, c); it is missing (must
// be sent) iff k >= svGet(sv, c).
func svGet(sv map[Client]Clock, c Client) Clock {
	v, ok := sv[c]
	if ok {
		return v
	}
	return 0
}

// svSetMax raises sv[c] to clk when clk is larger, leaving it unchanged
// otherwise (y-octo: StateVector::set_max). Folding each item's next clock
// through svSetMax builds the document's state vector.
func svSetMax(sv map[Client]Clock, c Client, clk Clock) {
	if svGet(sv, c) < clk {
		sv[c] = clk
	}
}

// computeStateVector builds the document's state vector from its decoded item
// list: for each client it records one past the largest clock that client owns
// (y-octo: DocStore::items_as_state_vector, back().clock()+len()). Items are
// 1-char in this subset, so each contributes id.clock+1. The result is the
// Step1 payload advertising what this replica already has.
func computeStateVector(items []updateItem) map[Client]Clock {
	sv := make(map[Client]Clock)
	for i := 0; i < len(items); i++ {
		itemId := items[i].id
		svSetMax(sv, itemId.clientId, itemId.clock+1)
	}
	return sv
}

// computeDiff selects the structs a peer with state vector sv is missing: every
// item whose clock is at or beyond what sv records for its client (y-octo:
// DocStore::diff_state_vectors + diff_structs, restricted to the 1-char subset
// where a struct never needs splitting at an offset, so the boundary check is a
// plain clock comparison). This is the execution of an incoming Step1; its
// output is the Step2 update sent back to the peer.
func computeDiff(items []updateItem, sv map[Client]Clock) []updateItem {
	diff := []updateItem{}
	for i := 0; i < len(items); i++ {
		itemId := items[i].id
		if svGet(sv, itemId.clientId) <= itemId.clock {
			diff = append(diff, items[i])
		}
	}
	return diff
}
