//! Tests for basic Anneal specification syntax.

/// A test for zero ensures blocks and zero proofs.
/// Anneal should auto-inject proofs for implicit bounds (like isValid).
///
/// ```lean, anneal, spec
/// ```
pub fn zero_ensures_no_proof(x: u32) -> u32 {
    x
}

/// A function with absolutely no parameters, requires, or ensures.
/// Should generate cleanly and omit the `Pre` and `Post` structs entirely
/// (if there are no implicit bounds either).
pub fn zero_guarantees_zero_params() {}

/// A function with zero arguments and no specifications.
/// The Pre structure should be completely omitted.
///
/// ```lean, anneal, spec
/// ```
fn test_zero_args_no_bounds() {}
