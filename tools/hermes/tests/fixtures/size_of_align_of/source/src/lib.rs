/// ```hermes
/// ensures (h_size):
///   ret.val = 0
/// ensures (h_valid):
///   Hermes.IsValid.isValid ret
/// proof (h_progress):
///   unfold get_size_of_empty_tuple at *
///   simp_all
/// proof context:
///   unfold get_size_of_empty_tuple at h_ret_
///   simp_all
///   subst h_ret_
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
/// proof (h_progress):
///   unfold get_align_of_empty_tuple at *
///   simp_all
/// proof context:
///   unfold get_align_of_empty_tuple at h_ret_
///   simp_all
///   subst h_ret_
/// proof (h_align):
///   simp_all
/// proof (h_valid):
///   simp_all [Hermes.IsValid.isValid]
/// ```
pub fn get_align_of_empty_tuple() -> usize {
    core::mem::align_of::<()>()
}

fn main() {}
