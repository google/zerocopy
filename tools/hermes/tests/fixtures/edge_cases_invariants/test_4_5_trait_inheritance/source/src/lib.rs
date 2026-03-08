
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
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold dummy_hermes_padding at *
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
