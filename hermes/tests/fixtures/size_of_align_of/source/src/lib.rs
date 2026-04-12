/// ```anneal
/// ensures (h_size):
///   ret.val = 0
/// ensures (h_valid):
///   Anneal.IsValid.isValid ret
/// proof (h_progress):
///   unfold get_size_of_empty_tuple at *
///   simp_all
/// proof context:
///   have h_foo : True := True.intro
/// proof (h_size):
///   unfold get_size_of_empty_tuple at h_returns
///   simp_all
///   subst h_returns
///   simp_all
/// proof (h_valid):
///   unfold get_size_of_empty_tuple at h_returns
///   simp_all
///   subst h_returns
///   simp_all [Anneal.IsValid.isValid]
/// ```
pub fn get_size_of_empty_tuple() -> usize {
    core::mem::size_of::<()>()
}

/// ```anneal
/// ensures (h_align):
///   ret.val = 1
/// ensures (h_valid):
///   Anneal.IsValid.isValid ret
/// proof (h_progress):
///   unfold get_align_of_empty_tuple at *
///   simp_all
/// proof context:
///   have h_foo : True := True.intro
/// proof (h_align):
///   unfold get_align_of_empty_tuple at h_returns
///   simp_all
///   subst h_returns
///   simp_all
/// proof (h_valid):
///   unfold get_align_of_empty_tuple at h_returns
///   simp_all
///   subst h_returns
///   simp_all [Anneal.IsValid.isValid]
/// ```
pub fn get_align_of_empty_tuple() -> usize {
    core::mem::align_of::<()>()
}

fn main() {}
