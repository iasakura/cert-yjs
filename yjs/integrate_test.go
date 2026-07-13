package yjs

import "testing"

// helper: integrate a causally ordered sequence of items into a fresh store's
// root type "text" via the update path (store.repair resolves each item's
// neighbours and parent, then store.Integrate splices it in).
func runIntegrate(items []*item) string {
	s := newStore(0)
	name := "text"
	for _, it := range items {
		var parentName *string
		if it.originLeftId == nil && it.originRightId == nil {
			parentName = &name
		}
		s.repair(it, parentName)
		s.Integrate(nil, it)
	}
	return s.getOrCreateYType(name).Text()
}

func mkId(client, clock uint64) id { return newId(client, clock) }

func mkIdp(client, clock uint64) *id {
	v := newId(client, clock)
	return &v
}

// Two clients insert concurrently at the head (both origins nil). The Yjs
// integrate algorithm breaks the tie by client id (smaller first), so every
// integration order converges to "AB".
func TestConcurrentHeadInsertConverges(t *testing.T) {
	mk := func() (*item, *item) {
		a := newItem(mkId(1, 0), "A", nil, nil)
		b := newItem(mkId(2, 0), "B", nil, nil)
		return a, b
	}

	a1, b1 := mk()
	got1 := runIntegrate([]*item{a1, b1})
	a2, b2 := mk()
	got2 := runIntegrate([]*item{b2, a2})

	if got1 != "AB" || got2 != "AB" {
		t.Fatalf("expected both AB, got %q and %q", got1, got2)
	}
}

// Sequential typing "HI": H at head, then I with originLeft = H. (Delivery
// out of causal order is the pending machinery's job — integrateStructs in
// codec.go retries until dependencies resolve — so at the raw repair +
// Integrate level the input is always causally ordered.)
func TestSequentialInsert(t *testing.T) {
	h := newItem(mkId(1, 0), "H", nil, nil)
	i := newItem(mkId(1, 1), "I", mkIdp(1, 0), nil)
	if got := runIntegrate([]*item{h, i}); got != "HI" {
		t.Fatalf("expected HI, got %q", got)
	}
}

// Concurrent insert in the middle: base "AC" (client 1), then clients 2 and 3
// both insert between A and C (originLeft=A, originRight=C). Must converge
// regardless of order.
func TestConcurrentMiddleInsertConverges(t *testing.T) {
	build := func(order int) string {
		a := newItem(mkId(1, 0), "A", nil, nil)
		c := newItem(mkId(1, 1), "C", mkIdp(1, 0), nil)
		x := newItem(mkId(2, 0), "X", mkIdp(1, 0), mkIdp(1, 1))
		y := newItem(mkId(3, 0), "Y", mkIdp(1, 0), mkIdp(1, 1))
		if order == 0 {
			return runIntegrate([]*item{a, c, x, y})
		}
		return runIntegrate([]*item{a, c, y, x})
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

// TestSplitNode exercises the run-split machinery directly (the public API
// only mints 1-char items until multi-element updates land, so the split
// paths are otherwise unreachable): id/origin arithmetic, DLL splicing, run
// list insertion, and the deleted-flag inheritance of the right half (where
// y-octo diverges; see docs/plan-issue-28-runs-split.md).
func TestSplitNode(t *testing.T) {
	s := newStore(1)
	y := s.getOrCreateYType("text")
	it := newItem(newId(1, 0), "abc", nil, nil)
	it.parent = y
	s.Integrate(y, it)

	left, right := s.splitNode(it, 1)
	if got := y.Text(); got != "abc" {
		t.Fatalf("split changed the document: %q", got)
	}
	if left.content.content != "a" || right.content.content != "bc" {
		t.Fatalf("bad contents: %q / %q", left.content.content, right.content.content)
	}
	if right.id != newId(1, 1) {
		t.Fatalf("bad right id: %+v", right.id)
	}
	if right.originLeftId == nil || *right.originLeftId != left.LastId() {
		t.Fatalf("right originLeft is not left.LastId")
	}
	if left.right != right || right.left != left {
		t.Fatalf("DLL not rewired around the split")
	}
	if len(s.items[1]) != 2 || s.items[1][0] != left || s.items[1][1] != right {
		t.Fatalf("run list not updated: %v", s.items[1])
	}

	// clean-start split of the remaining "bc" run via the repair-side helper
	mid, ok := s.splitAtAndGetRight(newId(1, 2))
	if !ok || mid.content.content != "c" || mid.id != newId(1, 2) {
		t.Fatalf("splitAtAndGetRight: %v %+v", ok, mid)
	}
	if got := y.Text(); got != "abc" {
		t.Fatalf("second split changed the document: %q", got)
	}

	// the right half of a tombstoned run stays deleted (y-octo drops the flag)
	s2 := newStore(2)
	y2 := s2.getOrCreateYType("text")
	dead := newItem(newId(2, 0), "xy", nil, nil)
	dead.parent = y2
	s2.Integrate(y2, dead)
	dead.flags = dead.flags | itemDeleted
	y2.len = y2.len - dead.Len()
	_, r2 := s2.splitNode(dead, 1)
	if !r2.Deleted() {
		t.Fatalf("right half of a tombstoned run lost the deleted flag")
	}
	if got := y2.Text(); got != "" {
		t.Fatalf("tombstoned content resurrected: %q", got)
	}
}
