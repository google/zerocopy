
/// @spec
/// requires: x > 10
/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   sorry
/// ```
pub fn bar(x: &mut u32) {
    *x += 1;
}
