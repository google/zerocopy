
pub enum Void {}

/// ```lean, hermes
/// proof:
///   unfold invert at *
///   contradiction
/// ```
pub fn invert(v: Void) -> ! {
    match v {}
}
