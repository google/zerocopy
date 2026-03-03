
use std::collections::HashMap;

/// ```lean, hermes
/// proof
///   sorry
/// ```
pub fn use_external_type(m: HashMap<u32, u32>) -> usize {
    m.len()
}
