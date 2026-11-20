// 1: no lifetimes
fn a(x: u32) -> u32 { x }
// 2: elided in, elided out, rule 2 (one input lifetime)
fn b(x: &str) -> &str { x }
// 3: two inputs, named output -> must annotate, written named
fn c<'a>(x: &'a str, y: &str) -> &'a str { let _ = y; x }
// 4: method with &self, elided output -> rule 3
struct S<'a> { s: &'a str }
impl<'a> S<'a> {
    fn d(&self) -> &str { self.s }
    // 5: method returning 'a explicitly (elidable shape, named output)
    fn e(&self) -> &'a str { self.s }
}
// 6: anon lifetime in path, rule 2 via '_
fn f(x: std::str::Chars<'_>) -> usize { x.count() }
// 7: static output, zero inputs
fn g() -> &'static str { "x" }
// 8: fn pointer argument: nested scope skipped, no input lifetimes counted -> output 'static only
fn h(cb: fn(&u8) -> &u8) -> u8 { *cb(&1) }
// 9: typed receiver `self: Pin<&mut Self>` with a second reference input -> rule 3, not must-annotate
struct P;
impl P { fn i(self: std::pin::Pin<&mut Self>, cx: &mut u8) -> &u8 { let _ = cx; &0 } }
