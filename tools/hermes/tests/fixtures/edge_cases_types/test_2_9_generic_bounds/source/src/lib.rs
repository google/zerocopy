pub struct Phantom<T> {
    _marker: std::marker::PhantomData<T>,
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn unused<T>(x: u32) -> u32 {
    x
}
