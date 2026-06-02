use std::vec::Vec as MyVec;

/// ```lean, anneal, spec
/// theorem spec (v : MyVec Std.U32) :
///   Aeneas.Std.WP.spec (use_alias v) (fun ret_ => True) := by
///   sorry
/// ```
pub fn use_alias(v: MyVec<u32>) -> usize {
    v.len()
}
