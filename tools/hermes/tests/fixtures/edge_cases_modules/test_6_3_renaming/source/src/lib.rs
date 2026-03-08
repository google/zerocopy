use std::vec::Vec as MyVec;

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold use_alias at *
///   simp_all
/// ```
pub fn use_alias(v: MyVec<u32>) -> usize {
    v.len()
}
