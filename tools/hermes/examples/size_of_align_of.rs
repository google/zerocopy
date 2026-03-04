/// ```hermes
/// ensures result.val = 0
/// proof
///   unfold get_size_of_empty_tuple
///   simp
/// ```
pub fn get_size_of_empty_tuple() -> usize {
    core::mem::size_of::<()>()
}

/// ```hermes
/// ensures result.val = 1
/// proof
///   unfold get_align_of_empty_tuple
///   simp
/// ```
pub fn get_align_of_empty_tuple() -> usize {
    core::mem::align_of::<()>()
}

fn main() {}
