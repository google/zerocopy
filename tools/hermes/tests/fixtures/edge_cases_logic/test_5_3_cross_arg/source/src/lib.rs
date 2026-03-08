
/// @spec
/// requires: a.len = b.len
/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold zip at *
///   simp_all
/// ```
pub fn zip(a: &[u8], b: &[u8]) {}
