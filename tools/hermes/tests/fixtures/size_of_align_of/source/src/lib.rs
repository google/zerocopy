/// ```hermes
/// ensures ret.val = 0
/// proof
///   unfold get_size_of_empty_tuple
///   simp [Hermes.IsValid.isValid]
/// ```
pub fn get_size_of_empty_tuple() -> usize {
    core::mem::size_of::<()>()
}

/// ```hermes
/// ensures ret.val = 1
/// proof
///   unfold get_align_of_empty_tuple
///   simp [Hermes.IsValid.isValid]
/// ```
pub fn get_align_of_empty_tuple() -> usize {
    core::mem::align_of::<()>()
}

fn main() {}
