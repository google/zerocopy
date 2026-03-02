/// ```hermes
/// isSafe : true
/// ```
pub trait SafeWithIsSafe {}

/// ```hermes
/// isSafe : true
/// isSafe : false
/// ```
pub trait MultipleIsSafeSafe {}

/// ```hermes
/// isSafe
/// ```
pub trait EmptyIsSafeSafe {}
