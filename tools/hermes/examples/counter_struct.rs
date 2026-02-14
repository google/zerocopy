/// ```lean, hermes
/// isValid self := self.val <= self.max
/// ```
pub struct Counter {
    val: u32,
    #[allow(dead_code)]
    max: u32,
}

impl Counter {
    /// ```lean, hermes, spec
    /// requires self.val < self.max
    /// ensures self.val = old(self.val) + 1
    ///   -- Preservation of invariant is implicit but checked
    /// ensures self.val = old(self.val) + 1
    /// proof
    ///   unfold inc
    ///   simp_all
    /// ```
    pub fn inc(&mut self) {
        self.val += 1;
    }
}

fn main() {}
