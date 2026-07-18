package yjs

import "testing"

// helper: one decoded insert struct with sibling origins (its parent is
// borrowed from a neighbour, as on the wire).
func mkUpdateItem(client, clock uint64, content string, oL, oR *id) updateItem {
	return updateItem{id: newId(client, clock), originLeftId: oL, originRightId: oR, content: content}
}

// helper: one decoded head insert struct (no origins), carrying its root type
// name (Parent::String on the wire).
func mkHeadUpdateItem(client, clock uint64, content string, name string) updateItem {
	return updateItem{id: newId(client, clock), parentName: &name, content: content}
}

// applyUpdateTo integrates a decoded update (any order, issue #40) into a
// fresh store via the verified core store.applyUpdate — each struct resolves
// its own parent — and returns the visible text of the root type "text".
func applyUpdateTo(structs []updateItem) string {
	s := newStore(0)
	u := Update{structs: structs}
	s.applyUpdate(u.structs)
	return s.getOrCreateYType("text").Text()
}

// Sequential update "HI": H at head, then I with originLeft = H.
func TestApplyUpdateSequential(t *testing.T) {
	h := mkHeadUpdateItem(1, 0, "H", "text")
	i := mkUpdateItem(1, 1, "I", mkIdp(1, 0), nil)
	if got := applyUpdateTo([]updateItem{h, i}); got != "HI" {
		t.Fatalf("expected HI, got %q", got)
	}
}

// Concurrent middle insert delivered as an update: base "AC" (client 1), then
// clients 2 and 3 both insert between A and C. Any causal delivery order must
// converge (X before Y by client-id tie-break) to "AXYC".
func TestApplyUpdateConcurrentMiddleConverges(t *testing.T) {
	a := mkHeadUpdateItem(1, 0, "A", "text")
	c := mkUpdateItem(1, 1, "C", mkIdp(1, 0), nil)
	x := mkUpdateItem(2, 0, "X", mkIdp(1, 0), mkIdp(1, 1))
	y := mkUpdateItem(3, 0, "Y", mkIdp(1, 0), mkIdp(1, 1))

	g0 := applyUpdateTo([]updateItem{a, c, x, y})
	g1 := applyUpdateTo([]updateItem{a, c, y, x})
	if g0 != g1 {
		t.Fatalf("divergence across causal orders: %q vs %q", g0, g1)
	}
	if g0 != "AXYC" {
		t.Fatalf("expected AXYC, got %q", g0)
	}
}

// Concurrent head insert delivered as an update: two clients insert at the head
// (both origins nil, so both carry the type name). Tie-break by client id gives
// "AB" regardless of order.
func TestApplyUpdateConcurrentHeadConverges(t *testing.T) {
	a := mkHeadUpdateItem(1, 0, "A", "text")
	b := mkHeadUpdateItem(2, 0, "B", "text")
	if got := applyUpdateTo([]updateItem{a, b}); got != "AB" {
		t.Fatalf("expected AB, got %q", got)
	}
	if got := applyUpdateTo([]updateItem{b, a}); got != "AB" {
		t.Fatalf("expected AB (reversed), got %q", got)
	}
}

// Reversed order within one update (issue #40): the batch violates causal
// order (I's origin H comes later in the list) and still applies fully.
func TestApplyUpdateOutOfOrderWithinUpdate(t *testing.T) {
	h := mkHeadUpdateItem(1, 0, "H", "text")
	i := mkUpdateItem(1, 1, "I", mkIdp(1, 0), nil)
	if got := applyUpdateTo([]updateItem{i, h}); got != "HI" {
		t.Fatalf("expected HI, got %q", got)
	}
}

// Missing dependency across updates (issue #40): the dependent struct pends
// in the store and drains when the dependency arrives later.
func TestApplyUpdatePendingDrain(t *testing.T) {
	s := newStore(0)
	h := mkHeadUpdateItem(1, 0, "H", "text")
	i := mkUpdateItem(1, 1, "I", mkIdp(1, 0), nil)

	s.applyUpdate([]updateItem{i})
	if got := s.getOrCreateYType("text").Text(); got != "" {
		t.Fatalf("expected empty text while pending, got %q", got)
	}
	if len(s.pending) != 1 {
		t.Fatalf("expected 1 pending struct, got %d", len(s.pending))
	}

	s.applyUpdate([]updateItem{h})
	if got := s.getOrCreateYType("text").Text(); got != "HI" {
		t.Fatalf("expected HI after drain, got %q", got)
	}
	if len(s.pending) != 0 {
		t.Fatalf("expected empty pending after drain, got %d", len(s.pending))
	}
}

// Per-client contiguity gate (issue #40): K's origins are present but its
// author's preceding struct (1,1) has not arrived, so K pends despite the
// resolvable origins (y-octo's state-vector contiguity, as an arrival check);
// it drains once (1,1) arrives.
//
// History: client 1 types "H", client 2 appends "X" (doc "HX"), client 1
// appends "I" after X (doc "HXI") and then inserts "K" between H and X
// (doc "HKXI").
func TestApplyUpdateOwnPredecessorGate(t *testing.T) {
	h := mkHeadUpdateItem(1, 0, "H", "text")
	x := mkUpdateItem(2, 0, "X", mkIdp(1, 0), nil)
	i := mkUpdateItem(1, 1, "I", mkIdp(2, 0), nil)
	k := mkUpdateItem(1, 2, "K", mkIdp(1, 0), mkIdp(2, 0))

	s := newStore(0)
	s.applyUpdate([]updateItem{h, x, k})
	if got := s.getOrCreateYType("text").Text(); got != "HX" {
		t.Fatalf("expected HX while K pends, got %q", got)
	}
	if len(s.pending) != 1 {
		t.Fatalf("expected K pending, got %d structs", len(s.pending))
	}
	s.applyUpdate([]updateItem{i})
	if got := s.getOrCreateYType("text").Text(); got != "HKXI" {
		t.Fatalf("expected HKXI after drain, got %q", got)
	}
	if len(s.pending) != 0 {
		t.Fatalf("expected empty pending, got %d structs", len(s.pending))
	}
}

// Duplicate deliveries (issue #40): re-applying the same update, and
// duplicates within one batch, integrate once. Pending re-deliveries are
// deduplicated too.
func TestApplyUpdateDuplicatesDropped(t *testing.T) {
	h := mkHeadUpdateItem(1, 0, "H", "text")
	i := mkUpdateItem(1, 1, "I", mkIdp(1, 0), nil)

	s := newStore(0)
	s.applyUpdate([]updateItem{h, i, h, i})
	s.applyUpdate([]updateItem{h, i})
	if got := s.getOrCreateYType("text").Text(); got != "HI" {
		t.Fatalf("expected HI, got %q", got)
	}

	// an unappliable struct re-delivered while pending stays a single entry
	s2 := newStore(0)
	orphan := mkUpdateItem(1, 1, "I", mkIdp(1, 0), nil)
	s2.applyUpdate([]updateItem{orphan})
	s2.applyUpdate([]updateItem{orphan})
	if len(s2.pending) != 1 {
		t.Fatalf("expected 1 pending struct after re-delivery, got %d", len(s2.pending))
	}
}

// A struct whose dependency never arrives pends forever without blocking
// later, unrelated updates (issue #40: applyUpdate is total).
func TestApplyUpdateUnresolvableStaysPending(t *testing.T) {
	s := newStore(0)
	ghostDep := mkUpdateItem(3, 5, "G", mkIdp(9, 9), nil)
	h := mkHeadUpdateItem(1, 0, "H", "text")

	s.applyUpdate([]updateItem{ghostDep})
	s.applyUpdate([]updateItem{h})
	if got := s.getOrCreateYType("text").Text(); got != "H" {
		t.Fatalf("expected H, got %q", got)
	}
	if len(s.pending) != 1 {
		t.Fatalf("expected the unresolvable struct to stay pending, got %d", len(s.pending))
	}
}

// Convergence across fragmented, permuted deliveries (issue #40): the same
// four structs delivered as singleton updates in several permutations (some
// forcing pending buffering) converge to the in-order document.
func TestApplyUpdateFragmentedDeliveryConverges(t *testing.T) {
	a := mkHeadUpdateItem(1, 0, "A", "text")
	c := mkUpdateItem(1, 1, "C", mkIdp(1, 0), nil)
	x := mkUpdateItem(2, 0, "X", mkIdp(1, 0), mkIdp(1, 1))
	y := mkUpdateItem(3, 0, "Y", mkIdp(1, 0), mkIdp(1, 1))

	orders := [][]updateItem{
		{a, c, x, y},
		{y, x, c, a},
		{x, y, a, c},
		{c, y, a, x},
		{y, c, x, a},
	}
	want := applyUpdateTo([]updateItem{a, c, x, y})
	for oi, ord := range orders {
		s := newStore(0)
		for _, ui := range ord {
			s.applyUpdate([]updateItem{ui})
		}
		if got := s.getOrCreateYType("text").Text(); got != want {
			t.Fatalf("order %d diverged: %q vs %q", oi, got, want)
		}
		if len(s.pending) != 0 {
			t.Fatalf("order %d left %d structs pending", oi, len(s.pending))
		}
	}
}

// One update touching two root types: each struct resolves its own parent, so
// a single doc-level batch fills both texts (issue #49).
func TestApplyUpdateMultipleRoots(t *testing.T) {
	s := newStore(0)
	h := mkHeadUpdateItem(1, 0, "H", "title")
	i := mkUpdateItem(1, 1, "I", mkIdp(1, 0), nil)
	b := mkHeadUpdateItem(1, 2, "B", "body")
	s.applyUpdate([]updateItem{h, i, b})
	if got := s.getOrCreateYType("title").Text(); got != "HI" {
		t.Fatalf("title: expected HI, got %q", got)
	}
	if got := s.getOrCreateYType("body").Text(); got != "B" {
		t.Fatalf("body: expected B, got %q", got)
	}
}
