use std::cell::Cell;
struct Guard<'a>(&'a Cell<u32>);
impl Drop for Guard<'_> { fn drop(&mut self) { self.0.set(self.0.get()+1); } }
fn main() { let n=Cell::new(0); { let _a=Guard(&n); let _b=Guard(&n); } assert!(n.get() == 2); }
