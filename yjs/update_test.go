package yjs

import "testing"

// helper: one decoded insert struct for an update.
func mkUpdateItem(client, clock uint64, content string, oL, oR *id) updateItem {
	return updateItem{id: newId(client, clock), originLeftId: oL, originRightId: oR, content: content}
}

// applyUpdateTo integrates a decoded update (in causal order) into a fresh root
// text via the verified core store.applyUpdate, and returns the visible text.
func applyUpdateTo(structs []updateItem) string {
	s := newStore(0)
	parent := newYType()
	u := Update{structs: structs}
	s.applyUpdate(parent, u.structs)
	return parent.Text()
}

// Sequential update "HI": H at head, then I with originLeft = H.
func TestApplyUpdateSequential(t *testing.T) {
	h := mkUpdateItem(1, 0, "H", nil, nil)
	i := mkUpdateItem(1, 1, "I", mkIdp(1, 0), nil)
	if got := applyUpdateTo([]updateItem{h, i}); got != "HI" {
		t.Fatalf("expected HI, got %q", got)
	}
}

// Concurrent middle insert delivered as an update: base "AC" (client 1), then
// clients 2 and 3 both insert between A and C. Any causal delivery order must
// converge (X before Y by client-id tie-break) to "AXYC".
func TestApplyUpdateConcurrentMiddleConverges(t *testing.T) {
	a := mkUpdateItem(1, 0, "A", nil, nil)
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
// (both origins nil). Tie-break by client id gives "AB" regardless of order.
func TestApplyUpdateConcurrentHeadConverges(t *testing.T) {
	a := mkUpdateItem(1, 0, "A", nil, nil)
	b := mkUpdateItem(2, 0, "B", nil, nil)
	if got := applyUpdateTo([]updateItem{a, b}); got != "AB" {
		t.Fatalf("expected AB, got %q", got)
	}
	if got := applyUpdateTo([]updateItem{b, a}); got != "AB" {
		t.Fatalf("expected AB (reversed), got %q", got)
	}
}
