/// ```anneal
/// isValid self := self.x > 0
/// ```
pub struct Positive {
    pub x: u32,
}

/// ```anneal
/// context:
/// -- No context
/// ensures:
///   Positive.x ret > 0
/// proof context:
/// proof:
///   simp [make_valid, Anneal.IsValid.isValid]; decide
/// ```
pub fn make_valid() -> Positive {
    Positive { x: 1 }
}

/// ```anneal
/// context:
/// -- No context
/// ensures:
///   Positive.x ret > 0
/// proof context:
/// proof:
///   simp [make_bad, Anneal.IsValid.isValid]; decide
/// ```
pub fn make_bad() -> Positive {
    Positive { x: 0 }
}
