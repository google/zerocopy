/// ```hermes
/// ensures (h_size):
///   ret.val = 0
/// ensures (h_valid):
///   Hermes.IsValid.isValid ret
/// proof context:
///   unfold get_size_of_empty_tuple
///   simp
/// proof context:
/// proof (h_size):
///   simp_all
/// proof (h_valid):
///   simp_all [Hermes.IsValid.isValid]
/// ```
pub fn get_size_of_empty_tuple() -> usize {
    core::mem::size_of::<()>()
}

/// ```hermes
/// ensures (h_align):
///   ret.val = 1
/// ensures (h_valid):
///   Hermes.IsValid.isValid ret
/// proof context:
///   unfold get_align_of_empty_tuple
///   simp
/// proof context:
/// proof (h_align):
///   simp_all
/// proof (h_valid):
///   simp_all [Hermes.IsValid.isValid]
/// ```
pub fn get_align_of_empty_tuple() -> usize {
    core::mem::align_of::<()>()
}

fn main() {}
