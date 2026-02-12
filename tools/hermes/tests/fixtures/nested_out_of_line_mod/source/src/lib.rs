pub fn outer_logic() {
    // This module declaration is hidden inside a function.
    // Hermes must NOT load `hidden.rs`.
    #[path = "hidden.rs"]
    mod hidden;
}

/// ```lean
/// theorem valid_proof : True := trivial
/// ```
pub fn valid_proof() {} // Included so the crate has at least one valid proof to succeed.
