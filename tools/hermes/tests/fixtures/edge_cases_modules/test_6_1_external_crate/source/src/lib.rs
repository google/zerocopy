
use std::collections::HashMap;

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn use_external_type(m: HashMap<u32, u32>) -> usize {
    m.len()
}
