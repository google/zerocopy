pub struct Phantom<T> {
    _marker: std::marker::PhantomData<T>,
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold unused at *
///   simp_all
/// ```
pub fn unused<T>(x: u32) -> u32 {
    x
}
