
/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   sorry
/// ```
pub fn mix(a: &mut u32, b: &u32, c: &mut u32) {
    *a += *b;
    *c += *b;
}
