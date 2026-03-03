use std::vec::Vec as MyVec;

/// ```lean, hermes
/// proof
///   sorry
/// ```
pub fn use_alias(v: MyVec<u32>) -> usize {
    v.len()
}
