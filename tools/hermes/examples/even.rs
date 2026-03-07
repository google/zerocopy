/// ```hermes
/// isValid self := 2 ∣ self.val.val
/// ```
pub struct Even {
    val: u32,
}

impl Even {
    /// ```hermes, spec
    /// ensures self'.val.val = 2
    /// proof
    ///   simp [Even.inc, Hermes.IsValid.isValid]
    /// ```
    pub fn inc(&mut self) {
        self.val = 2;
    }
}

fn main() {}
