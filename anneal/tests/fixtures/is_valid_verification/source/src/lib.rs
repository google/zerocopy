/// ```lean, anneal
/// def isValid (self : Positive) : Prop := self.x.val > 0
/// ```
pub struct Positive {
    pub x: u32,
}

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (make_valid) (fun ret_ => ret_.x.val > 0) := by
///   unfold make_valid
///   simp [Positive.isValid]
/// ```
pub fn make_valid() -> Positive {
    Positive { x: 1 }
}

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (make_bad) (fun ret_ => ret_.x.val > 0) := by
///   unfold make_bad
///   simp [Positive.isValid]
///   decide
/// ```
pub fn make_bad() -> Positive {
    Positive { x: 0 }
}
