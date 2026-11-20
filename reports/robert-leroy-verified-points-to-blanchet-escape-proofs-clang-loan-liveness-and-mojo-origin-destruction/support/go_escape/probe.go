package escprobe

import "reflect"

type Sizer interface{ Size(p *int) int }

type impl struct{}

//go:noinline
func (impl) Size(p *int) int { return *p }

var sink *int

// E1: address returned to caller -> must outlive frame.
func E1() *int { x := 1; return &x }

// E2: address used only locally -> may stay on stack.
func E2() int { x := 2; p := &x; return *p }

// E3: pointer declared outside a loop receives a per-iteration allocation.
func E3(n int) *int {
	var l *int
	for i := 0; i < n; i++ {
		l = new(int)
		*l = i
	}
	return nil
}

// E3b: allocation inside the loop, pointer also declared inside the loop.
func E3b(n int) int {
	s := 0
	for i := 0; i < n; i++ {
		l := new(int)
		*l = i
		s += *l
	}
	return s
}

// E4: pointer passed through an interface (dynamic) call.
func E4(s Sizer) int { x := 4; return s.Size(&x) }

// E5: same callee, static call.
func E5() int { x := 5; return impl{}.Size(&x) }

// E6: pointer stored into a global.
func E6() { x := 6; sink = &x }

// E7: reflect.
func E7() reflect.Value { x := 7; return reflect.ValueOf(&x) }

// E8: closure called immediately vs. returned.
func E8a() int { x := 8; f := func() int { return x + 1 }; return f() }
func E8b() func() int { x := 8; return func() int { x++; return x } }

// E9: size thresholds (explicit var vs. implicit new).
func E9a() byte { var a [200000]byte; return a[7] }
func E9b() byte { p := new([70000]byte); return p[7] }
func E9c() byte { p := new([60000]byte); return p[7] }

// E10: non-constant make.
func E10(n int) int { s := make([]int, n); return len(s) }
func E10c() int { s := make([]int, 8); return len(s) }
