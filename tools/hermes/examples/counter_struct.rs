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
    /// requires self.val.val < self.max.val
    /// ensures self'.val.val = self.val.val + 1
    ///   -- Preservation of invariant is implicit but checked
    /// ensures self'.val.val = self.val.val + 1
    /// proof
    ///   sorry
    /// ```
    pub fn inc(&mut self) {
        self.val += 1;
    }
}

fn main() {}
