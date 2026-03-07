
pub enum Void {}

/// ```lean, hermes
/// proof context:
///   unfold invert
///   contradiction
/// ```
pub fn invert(v: Void) -> ! {
    match v {}
}
