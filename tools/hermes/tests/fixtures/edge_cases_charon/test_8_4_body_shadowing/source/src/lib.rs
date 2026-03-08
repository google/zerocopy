/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   sorry
/// ```
pub fn shadow(x: u32) -> u32 {
    let x = x + 1;
    let x = x * 2;
    x
}
