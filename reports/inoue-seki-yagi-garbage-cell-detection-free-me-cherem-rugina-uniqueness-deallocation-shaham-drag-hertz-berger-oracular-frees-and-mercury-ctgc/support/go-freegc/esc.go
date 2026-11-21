package main

import (
	"fmt"
	"os"
	"runtime"
	"strconv"
	"time"
)

type T struct{ a, b int }

var sink *T
var sinkAny any

//go:noinline
func local() int { t := &T{1, 2}; return t.a + t.b } // expected: stays in frame

//go:noinline
func global() { t := &T{1, 2}; sink = t } // stored into a global: heap

//go:noinline
func retPtr() *T { return &T{3, 4} } // outlives frame: heap

//go:noinline
func iface(t T) { sinkAny = t } // conversion to interface stored globally

// build: append-growth loop whose slice is never aliased inside the loop.
//go:noinline
func build(n int) []int {
	var s []int
	for i := 0; i < n; i++ {
		s = append(s, i)
	}
	return s
}

// buildAliased: same loop, but the slice is copied into an outer variable each iteration.
var keep []int

//go:noinline
func buildAliased(n int) []int {
	var s []int
	for i := 0; i < n; i++ {
		s = append(s, i)
		keep = s
	}
	return s
}

func main() {
	mode := "build"
	if len(os.Args) > 1 {
		mode = os.Args[1]
	}
	iters := 200000
	n := 1000
	if len(os.Args) > 2 {
		iters, _ = strconv.Atoi(os.Args[2])
	}
	_ = local()
	global()
	_ = retPtr()
	iface(T{})
	runtime.GC()
	var m0, m1 runtime.MemStats
	runtime.ReadMemStats(&m0)
	t0 := time.Now()
	total := 0
	for k := 0; k < iters; k++ {
		var s []int
		if mode == "aliased" {
			s = buildAliased(n)
		} else {
			s = build(n)
		}
		total += len(s)
	}
	el := time.Since(t0)
	runtime.ReadMemStats(&m1)
	fmt.Printf("mode=%s iters=%d n=%d total=%d wall_ms=%d mallocs=%d total_alloc_MiB=%.1f num_gc=%d pause_total_ms=%.2f\n",
		mode, iters, n, total, el.Milliseconds(), m1.Mallocs-m0.Mallocs,
		float64(m1.TotalAlloc-m0.TotalAlloc)/(1<<20), m1.NumGC-m0.NumGC,
		float64(m1.PauseTotalNs-m0.PauseTotalNs)/1e6)
}
