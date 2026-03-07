pub struct Phantom<T> {
    _marker: std::marker::PhantomData<T>,
}

/// ```lean, hermes
/// proof context:
///   unfold unused
///   simp_all
/// ```
pub fn unused<T>(x: u32) -> u32 {
    x
}
