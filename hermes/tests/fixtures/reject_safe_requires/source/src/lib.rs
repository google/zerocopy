/// ```hermes
/// requires: True
/// ```
pub fn safe_with_requires() {}

/// ```hermes
/// requires: x > 0
/// requires: y > 0
/// ```
pub fn multiple_requires_safe(x: u32, y: u32) {}

/// ```hermes
/// requires:
/// ```
pub fn empty_requires_safe() {}

/// ```hermes
/// requires(h_true): True
/// ```
pub fn named_requires_safe() {}
