/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   sorry
/// ```
pub fn mut_passthrough(x: &mut u32) {
    *x += 1;
}
