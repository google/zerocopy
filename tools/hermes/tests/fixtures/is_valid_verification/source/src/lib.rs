/// ```hermes
/// isValid self := self.x > 0
/// ```
pub struct Positive {
    pub x: u32,
}

/// ```hermes
/// context
/// -- No context
/// requires true
/// ensures Positive.x result > 0
/// proof
///   simp [make_valid]; decide
/// ```
pub fn make_valid() -> Positive {
    Positive { x: 1 }
}

/// ```hermes
/// context
/// -- No context
/// requires true
/// ensures Positive.x result > 0
/// proof
///   simp [make_bad]; decide
/// ```
pub fn make_bad() -> Positive {
    Positive { x: 0 }
}
