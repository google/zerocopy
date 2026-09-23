#![allow(dead_code, unused_variables)]

/// Test Case 1: Error exactly inside a `proof context` block.
/// The `by decide` tactic here is invalid for `1 = 2`.
/// 
/// ```anneal
/// ensures: ret == ()
/// proof context:
///   have h : 1 = 2 := by decide
/// ```
pub fn test_proof_context_exact_error() {}

/// Test Case 2: Error overlapping the start of `proof context` line.
/// We'll use a tactic that has invalid syntax starting at the first character
/// or leading to an error that subsumes the indentation if Lean reports it that way.
/// 
/// ```anneal
/// ensures: ret == ()
/// proof context:
///  invalid_tactic_xyz
/// ```
pub fn test_proof_context_invalid_syntax() {}

/// Test Case 3: Error on an exact `have` variable name.
/// `h_bad` doesn't exist.
/// 
/// ```anneal
/// ensures: ret == ()
/// proof context:
///   exact h_bad
/// ```
pub fn test_proof_context_unknown_variable() {}

/// Test Case 4: Complete block failure ("uses sorry").
/// When a proof step is just left empty or lacks `sorry`, the compiler might report "uses sorry"
/// on the entire context or the declaration.
/// 
/// ```anneal
/// ensures: ret == ()
/// proof context:
///   sorry
/// ```
pub fn test_proof_context_sorry() {}

/// Test Case 5: Error mapping to the automatically injected synthetic theorem `post`.
/// We leave the proof blank. The `uses sorry` error should be redirected 
/// to the `ensures` keyword.
/// 
/// ```anneal
/// ensures: ret == ()
/// ```
pub fn test_synthetic_theorem_sorry() {}


