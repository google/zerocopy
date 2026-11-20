package liveprobe

import "runtime"

//go:noinline
func alloc() *int { return new(int) }

//go:noinline
func use(p *int) { _ = *p }

//go:noinline
func safepoint() {}

// L1: heap pointer held in a register/stack slot; last use before safepoint.
func L1() {
	p := alloc()
	use(p)
	safepoint() // is p in the live set here?
}

// L2: same, but the pointer is used after the safepoint.
func L2() {
	p := alloc()
	safepoint()
	use(p)
}

// L3: runtime.KeepAlive extends the reference's liveness past its last use.
func L3() {
	p := alloc()
	use(p)
	safepoint()
	runtime.KeepAlive(p)
}

type box struct{ q *int }

//go:noinline
func fill(b *box) { b.q = alloc() }

// L4: address-taken local containing a pointer (a "stack object").
func L4() {
	var b box
	fill(&b)
	use(b.q)
	safepoint() // b's last direct use is above
}
