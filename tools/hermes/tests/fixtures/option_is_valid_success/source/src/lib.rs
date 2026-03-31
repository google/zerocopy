/// ```hermes
/// isValid self := self.x > 0
/// ```
pub struct Positive {
    pub x: u32,
}

/// ```hermes
/// ```
pub fn valid_option() -> Option<Positive> {
    Some(Positive { x: 1 })
}
