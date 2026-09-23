/// ```anneal
/// requires: True
/// ```
pub fn safe_with_requires() {}

/// ```anneal
/// requires: x > 0
/// requires: y > 0
/// ```
pub fn multiple_requires_safe(x: u32, y: u32) {}

/// ```anneal
/// requires:
/// ```
pub fn empty_requires_safe() {}

/// ```anneal
/// requires(h_true): True
/// ```
pub fn named_requires_safe() {}
