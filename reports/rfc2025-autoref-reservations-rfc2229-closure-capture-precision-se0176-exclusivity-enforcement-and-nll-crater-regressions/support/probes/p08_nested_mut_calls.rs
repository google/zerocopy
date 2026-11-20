// Expect: rejected (RFC 2025: a second two-phase borrow cannot be taken while the first is reserved).
pub struct I(i32);
impl I { fn increment(&mut self, v: i32) -> i32 { self.0 += v; self.0 } }
pub fn f() -> i32 {
    let mut x = I(0);
    x.increment(x.increment(1))
}
