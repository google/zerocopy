// Rust analogue of SE-0176's `x.assignResultOf { x + 1 }` CONFLICT example.
pub struct X(i32);
impl X { fn assign_result_of(&mut self, f: impl FnOnce() -> i32) { self.0 = f(); } }
pub fn f() {
    let mut x = X(0);
    x.assign_result_of(|| x.0 + 1);
}
