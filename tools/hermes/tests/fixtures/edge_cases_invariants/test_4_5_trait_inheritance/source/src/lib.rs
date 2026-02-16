
/// @spec
/// isSafe : True
pub trait A {}

/// @spec
/// isSafe : True
pub trait B: A {}

/// @spec
/// isSafe : True
pub trait C: A {}

/// @spec
/// isSafe : True
pub trait D: B + C {}
