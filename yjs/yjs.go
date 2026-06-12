// Package yjs will hold a Yjs-style CRDT implementation to be verified
// with Perennial. Counter is a placeholder that exercises the full
// goose/proof pipeline; replace it with the real data structures.
package yjs

type Counter struct {
	value uint64
}

func (c *Counter) Inc() {
	c.value++
}

func (c *Counter) Get() uint64 {
	return c.value
}
