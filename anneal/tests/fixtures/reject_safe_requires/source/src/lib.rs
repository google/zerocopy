/// ```lean, anneal, spec
/// theorem spec (h_req : True) :
///   Aeneas.Std.WP.spec (safe_with_requires) (fun ret_ => True) := by
///   trivial
/// ```
pub fn safe_with_requires() {}

/// ```lean, anneal, spec
/// theorem spec (x y : Std.U32) (h_req1 : x.val > 0) (h_req2 : y.val > 0) :
///   Aeneas.Std.WP.spec (multiple_requires_safe x y) (fun ret_ => True) := by
///   trivial
/// ```
pub fn multiple_requires_safe(x: u32, y: u32) {}
