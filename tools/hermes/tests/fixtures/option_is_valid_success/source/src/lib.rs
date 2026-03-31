/// ```hermes
/// isValid self := self.x > 0
/// ```
pub struct Positive {
    pub x: u32,
}

/// ```hermes
/// proof (h_ret_is_valid):
///   have h_ret : some { x := 1#u32 } = ret := by
///     simpa [valid_option] using h_returns
///   rw [← h_ret]
///   simp [Hermes.IsValid.isValid]
///   decide
/// ```
pub fn valid_option() -> Option<Positive> {
    Some(Positive { x: 1 })
}
