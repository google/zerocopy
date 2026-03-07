
/// @spec
/// isSafe :
///   True
pub trait A {}

/// @spec
/// isSafe :
///   True
pub trait B: A {}

/// @spec
/// isSafe :
///   True
pub trait C: A {}

/// @spec
/// isSafe :
///   True
pub trait D: B + C {}


/// ```lean, hermes
/// proof context:
///   unfold dummy_hermes_padding
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
