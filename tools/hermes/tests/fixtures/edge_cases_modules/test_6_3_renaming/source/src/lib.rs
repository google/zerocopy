use std::vec::Vec as MyVec;

/// ```lean, hermes
/// proof context:
///   unfold use_alias
///   simp_all
/// ```
pub fn use_alias(v: MyVec<u32>) -> usize {
    v.len()
}
