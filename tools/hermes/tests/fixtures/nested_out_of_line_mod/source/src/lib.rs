pub fn outer_logic() {
    mod inner {
        // Despite living in `mod inner`, `inner` itself is hidden inside a
        // function. Hermes must reject all annotated items inside `mod hidden`.
        #[path = "hidden.rs"]
        mod hidden;
    }
}

/// ```lean, hermes
/// theorem valid_proof : True := trivial
/// ```
pub fn valid_proof() {} // Included so the crate has at least one valid proof to succeed.
