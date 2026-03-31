/// ```hermes
/// isValid self := self.x > 0
/// ```
pub struct Positive {
    pub x: u32,
}

/// ```hermes
/// ```
pub fn invalid_pair() -> (Positive, u32) {
    (Positive { x: 0 }, 0)
}
