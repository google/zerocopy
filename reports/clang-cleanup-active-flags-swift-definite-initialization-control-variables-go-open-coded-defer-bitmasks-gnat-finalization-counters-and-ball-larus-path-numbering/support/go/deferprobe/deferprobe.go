// Package deferprobe measures Go's three defer implementations
// (open-coded, stack-allocated record, heap-allocated record) on small
// functions whose deferred calls are owed on only some paths.
package deferprobe

var sink int

//go:noinline
func work(x int) int { sink += x; return x }

//go:noinline
func release(x int) { sink -= x }

//go:noinline
func boom(p bool) {
	if p {
		panic("boom")
	}
}

// Baseline: explicit release, no defer.
//
//go:noinline
func NoDefer(x int) int { r := work(x); release(x); return r }

// One unconditional defer.
//
//go:noinline
func DeferUncond(x int) int {
	defer release(x)
	return work(x)
}

// One defer owed only if c is true (a pending-call bit decides at exit).
//
//go:noinline
func DeferCond(c bool, x int) int {
	if c {
		defer release(x)
	}
	return work(x)
}

// Hand-duplicated equivalent of DeferCond (normal path only; not panic-safe
// in the same way, because release is not run if work panics).
//
//go:noinline
func ManualCond(c bool, x int) int {
	if c {
		r := work(x)
		release(x)
		return r
	}
	return work(x)
}

// Eight defers: the maximum the one-byte pending-call mask can record.
//
//go:noinline
func Defer8(x int) int {
	defer release(1)
	defer release(2)
	defer release(3)
	defer release(4)
	defer release(5)
	defer release(6)
	defer release(7)
	defer release(8)
	return work(x)
}

// Nine defers: one more than the mask can record.
//
//go:noinline
func Defer9(x int) int {
	defer release(1)
	defer release(2)
	defer release(3)
	defer release(4)
	defer release(5)
	defer release(6)
	defer release(7)
	defer release(8)
	defer release(9)
	return work(x)
}

// A defer inside a loop (executed once here, but the compiler cannot know).
//
//go:noinline
func DeferLoop(n, x int) int {
	for i := 0; i < n; i++ {
		defer release(i)
	}
	return work(x)
}

// Four defers and three explicit returns: 4*3 = 12 <= 15.
//
//go:noinline
func Defer4Ret3(c, x int) int {
	defer release(1)
	defer release(2)
	defer release(3)
	defer release(4)
	switch c {
	case 1:
		return work(x)
	case 2:
		return work(x + 1)
	}
	return work(x + 2)
}

// Four defers and four explicit returns: 4*4 = 16 > 15.
//
//go:noinline
func Defer4Ret4(c, x int) int {
	defer release(1)
	defer release(2)
	defer release(3)
	defer release(4)
	switch c {
	case 1:
		return work(x)
	case 2:
		return work(x + 1)
	case 3:
		return work(x + 2)
	}
	return work(x + 3)
}

// Panic path through an open-coded defer that recovers.
//
//go:noinline
func PanicOpen(x int) (r int) {
	defer func() {
		if recover() != nil {
			r = -1
		}
	}()
	boom(true)
	return x
}

// Panic path through a defer record (the defer is inside a loop).
//
//go:noinline
func PanicLoop(x int) (r int) {
	for i := 0; i < 1; i++ {
		defer func() {
			if recover() != nil {
				r = -1
			}
		}()
	}
	boom(true)
	return x
}
