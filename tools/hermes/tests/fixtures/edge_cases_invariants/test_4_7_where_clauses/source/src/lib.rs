
/// @spec
/// isValid self := True
pub struct Foo<T> where T: Copy + Clone + Default {
    pub inner: T,
}


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold dummy_hermes_padding at *
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
