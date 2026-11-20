// Expect: accepted (binary assignment operators on overloaded types use two-phase borrows).
use std::ops::AddAssign;
pub struct W(Vec<usize>);
impl W { fn len(&self) -> usize { self.0.len() } }
impl AddAssign<usize> for W { fn add_assign(&mut self, n: usize) { self.0.push(n) } }
pub fn f() -> W {
    let mut w = W(vec![]);
    w += w.len();
    w
}
