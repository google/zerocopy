
use std::collections::HashMap;

/// ```lean, hermes
/// proof context:
///   unfold use_external_type
///   simp_all
/// ```
pub fn use_external_type(m: HashMap<u32, u32>) -> usize {
    m.len()
}
