use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};
struct Guard<'a>(&'a Cell<u32>);
impl Drop for Guard<'_> { fn drop(&mut self) { self.0.set(self.0.get()+1); } }
struct Bomb;
impl Drop for Bomb { fn drop(&mut self) { panic!("OWNED_EXPECTED_DROP_UNWIND"); } }
fn main() {
 let n=Cell::new(0);
 let caught=catch_unwind(AssertUnwindSafe(|| { let _guard=Guard(&n); let _bomb=Bomb; }));
 assert!(caught.is_err()); assert!(n.get() == 1);
}
