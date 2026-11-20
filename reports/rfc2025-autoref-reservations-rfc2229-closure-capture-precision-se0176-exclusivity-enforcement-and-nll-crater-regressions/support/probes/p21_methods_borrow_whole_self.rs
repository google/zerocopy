// Disjoint fields through `&mut self` methods.
pub struct T { a: Vec<u32>, b: Vec<u32> }
impl T {
    fn push_a(&mut self, x: u32) { self.a.push(x) }
    fn len_b(&self) -> u32 { self.b.len() as u32 }
    // Expect accepted: two-phase reservation of `self` permits the shared borrow in the argument.
    pub fn nested(&mut self) { self.push_a(self.len_b()); }
    // Expect accepted: direct field paths are disjoint.
    pub fn fields(&mut self) { let b = &mut self.b; self.a.push(1); b.push(2); }
    // Expect rejected (E0499): a method call borrows all of `self`; signatures cannot name a field subset.
    pub fn through_method(&mut self) { let b = &mut self.b; self.push_a(1); b.push(2); }
}
