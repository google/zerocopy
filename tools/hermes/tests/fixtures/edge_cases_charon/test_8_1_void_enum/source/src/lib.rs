
pub enum Void {}

/// ```lean, hermes
/// proof:
///   unfold invert
///   contradiction
/// ```
pub fn invert(v: Void) -> ! {
    match v {}
}
