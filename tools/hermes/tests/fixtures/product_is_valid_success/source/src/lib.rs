/// ```hermes
/// isValid self := self.x > 0
/// ```
pub struct Positive {
    pub x: u32,
}

/// ```hermes
/// proof (h_ret_is_valid):
///   have h_ret : ({ x := 1#u32 }, 0#u32) = ret := by
///     simpa [valid_pair] using h_returns
///   rw [← h_ret]
///   simp [Hermes.IsValid.isValid]
///   decide
/// ```
pub fn valid_pair() -> (Positive, u32) {
    (Positive { x: 1 }, 0)
}
