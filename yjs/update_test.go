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

// applyUpdateTo integrates a decoded update (in causal order) into a fresh
// store via the verified core store.applyUpdate — each struct resolves its own
// parent — and returns the visible text of the root type "text".
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
