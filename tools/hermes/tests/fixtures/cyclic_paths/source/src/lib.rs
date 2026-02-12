// This simulates a symlink loop by pointing a module declaration back at itself.
// Without canonicalization, this causes a stack overflow.
#[path = "lib.rs"]
mod self_loop;

/// ```lean
/// theorem valid : True := trivial
/// ```
pub fn valid() {}
