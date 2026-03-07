/// ```lean, hermes
/// proof context:
///   sorry
/// ```
pub fn mut_passthrough(x: &mut u32) {
    *x += 1;
}
