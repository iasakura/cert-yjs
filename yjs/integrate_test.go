package yjs

import "testing"

// helper: integrate a sequence of items into a fresh YText and return the text.
func runIntegrate(items []*Item) string {
	s := NewStore(0)
	parent := NewYText()
	for _, it := range items {
		s.Integrate(parent, it)
	}
	return parent.Text()
}

func id(client, clock uint64) Id { return NewId(client, clock) }

func idp(client, clock uint64) *Id {
	v := NewId(client, clock)
	return &v
}

// Two clients insert concurrently at the head (both origins nil). The Yjs
// integrate algorithm breaks the tie by client id (smaller first), so every
// integration order converges to "AB".
func TestConcurrentHeadInsertConverges(t *testing.T) {
	mk := func() (*Item, *Item) {
		a := NewItem(id(1, 0), "A", nil, nil)
		b := NewItem(id(2, 0), "B", nil, nil)
		return a, b
	}

	a1, b1 := mk()
	got1 := runIntegrate([]*Item{a1, b1})
	a2, b2 := mk()
	got2 := runIntegrate([]*Item{b2, a2})

	if got1 != "AB" || got2 != "AB" {
		t.Fatalf("expected both AB, got %q and %q", got1, got2)
	}
}

// Sequential typing "HI": H at head, then I with originLeft = H.
func TestSequentialInsert(t *testing.T) {
	h := NewItem(id(1, 0), "H", nil, nil)
	i := NewItem(id(1, 1), "I", idp(1, 0), nil)
	if got := runIntegrate([]*Item{h, i}); got != "HI" {
		t.Fatalf("expected HI, got %q", got)
	}
	// reverse application order must still converge
	h2 := NewItem(id(1, 0), "H", nil, nil)
	i2 := NewItem(id(1, 1), "I", idp(1, 0), nil)
	if got := runIntegrate([]*Item{i2, h2}); got != "HI" {
		t.Fatalf("expected HI (reversed), got %q", got)
	}
}

// Concurrent insert in the middle: base "AC" (client 1), then clients 2 and 3
// both insert between A and C (originLeft=A, originRight=C). Must converge
// regardless of order.
func TestConcurrentMiddleInsertConverges(t *testing.T) {
	build := func(order int) string {
		a := NewItem(id(1, 0), "A", nil, nil)
		c := NewItem(id(1, 1), "C", idp(1, 0), nil)
		x := NewItem(id(2, 0), "X", idp(1, 0), idp(1, 1))
		y := NewItem(id(3, 0), "Y", idp(1, 0), idp(1, 1))
		if order == 0 {
			return runIntegrate([]*Item{a, c, x, y})
		}
		return runIntegrate([]*Item{a, c, y, x})
	}
	g0 := build(0)
	g1 := build(1)
	if g0 != g1 {
		t.Fatalf("divergence: %q vs %q", g0, g1)
	}
	// X (client 2) < Y (client 3) at the same origins, so X comes first.
	if g0 != "AXYC" {
		t.Fatalf("expected AXYC, got %q", g0)
	}
}
