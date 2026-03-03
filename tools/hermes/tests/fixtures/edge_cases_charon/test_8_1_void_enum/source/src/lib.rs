
pub enum Void {}

/// ```lean, hermes
/// proof
///   sorry
/// ```
pub fn invert(v: Void) -> ! {
    match v {}
}
