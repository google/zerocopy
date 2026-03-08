
use std::collections::HashMap;

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold use_external_type at *
///   simp_all
/// ```
pub fn use_external_type(m: HashMap<u32, u32>) -> usize {
    m.len()
}
