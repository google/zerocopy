
/// @spec
/// isValid self := True
pub struct Foo<T> where T: Copy + Clone + Default {
    pub inner: T,
}


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding() {}
