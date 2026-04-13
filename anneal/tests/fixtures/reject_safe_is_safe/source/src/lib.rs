/// ```anneal
/// isSafe :
///   true
/// ```
pub trait SafeWithIsSafe {}

/// ```anneal
/// isSafe :
///   true
/// isSafe :
///   false
/// ```
pub trait MultipleIsSafeSafe {}

/// ```anneal
/// isSafe
/// ```
pub trait EmptyIsSafeSafe {}
