
use std::collections::HashMap;

/// ```lean, anneal, spec
/// theorem spec (m : HashMap Std.U32 Std.U32) :
///   Aeneas.Std.WP.spec (use_external_type m) (fun ret_ => True) := by
///   sorry
/// ```
pub fn use_external_type(m: HashMap<u32, u32>) -> usize {
    m.len()
}
