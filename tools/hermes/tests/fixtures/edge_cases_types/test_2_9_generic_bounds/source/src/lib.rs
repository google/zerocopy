pub struct Phantom<T> {
    _marker: std::marker::PhantomData<T>,
}

/// ```lean, hermes
/// proof
///   sorry
/// ```
pub fn unused<T>(x: u32) -> u32 {
    x
}
