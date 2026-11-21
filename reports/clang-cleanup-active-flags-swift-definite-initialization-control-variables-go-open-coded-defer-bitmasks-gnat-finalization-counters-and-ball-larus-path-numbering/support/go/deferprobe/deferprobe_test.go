package deferprobe

import "testing"

func BenchmarkNoDefer(b *testing.B) {
	for i := 0; i < b.N; i++ {
		NoDefer(i)
	}
}
func BenchmarkDeferUncond(b *testing.B) {
	for i := 0; i < b.N; i++ {
		DeferUncond(i)
	}
}
func BenchmarkDeferCondTrue(b *testing.B) {
	for i := 0; i < b.N; i++ {
		DeferCond(true, i)
	}
}
func BenchmarkDeferCondFalse(b *testing.B) {
	for i := 0; i < b.N; i++ {
		DeferCond(false, i)
	}
}
func BenchmarkManualCondTrue(b *testing.B) {
	for i := 0; i < b.N; i++ {
		ManualCond(true, i)
	}
}
func BenchmarkDefer8(b *testing.B) {
	for i := 0; i < b.N; i++ {
		Defer8(i)
	}
}
func BenchmarkDefer9(b *testing.B) {
	for i := 0; i < b.N; i++ {
		Defer9(i)
	}
}
func BenchmarkDeferLoop1(b *testing.B) {
	for i := 0; i < b.N; i++ {
		DeferLoop(1, i)
	}
}
func BenchmarkDefer4Ret3(b *testing.B) {
	for i := 0; i < b.N; i++ {
		Defer4Ret3(i&3, i)
	}
}
func BenchmarkDefer4Ret4(b *testing.B) {
	for i := 0; i < b.N; i++ {
		Defer4Ret4(i&3, i)
	}
}
func BenchmarkPanicOpen(b *testing.B) {
	for i := 0; i < b.N; i++ {
		PanicOpen(i)
	}
}
func BenchmarkPanicLoop(b *testing.B) {
	for i := 0; i < b.N; i++ {
		PanicLoop(i)
	}
}
