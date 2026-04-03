use std::vec::Vec as MyVec;

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn use_alias(v: MyVec<u32>) -> usize {
    v.len()
}
