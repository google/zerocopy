
/// @spec
/// isValid self := True
pub struct Foo<T> where T: Copy + Clone + Default {
    pub inner: T,
}


/// ```lean, hermes
/// proof
///   sorry
/// ```
pub fn dummy_hermes_padding() {}
