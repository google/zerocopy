
/// @spec
/// isSafe Self
pub trait A {}

/// @spec
/// isSafe Self
pub trait B: A {}

/// @spec
/// isSafe Self
pub trait C: A {}

/// @spec
/// isSafe Self
pub trait D: B + C {}
