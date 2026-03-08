
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
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding() {}
