#![allow(dead_code, unused_variables)]

/// Test Case 1: Error exactly inside a `proof context` block.
/// The `by decide` tactic here is invalid for `1 = 2`.
/// 
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (test_proof_context_exact_error) (fun ret_ => True) := by
///   have h : 1 = 2 := by decide
///   simp_all
/// ```
pub fn test_proof_context_exact_error() {}

/// Test Case 2: Error overlapping the start of `proof context` line.
/// We'll use a tactic that has invalid syntax starting at the first character
/// or leading to an error that subsumes the indentation if Lean reports it that way.
/// 
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (test_proof_context_invalid_syntax) (fun ret_ => True) := by
///  invalid_tactic_xyz
/// ```
pub fn test_proof_context_invalid_syntax() {}

/// Test Case 3: Error on an exact `have` variable name.
/// `h_bad` doesn't exist.
/// 
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (test_proof_context_unknown_variable) (fun ret_ => True) := by
///   exact h_bad
/// ```
pub fn test_proof_context_unknown_variable() {}

/// Test Case 4: Complete block failure ("uses sorry").
/// When a proof step is just left empty or lacks `sorry`, the compiler might report "uses sorry"
/// on the entire context or the declaration.
/// 
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (test_proof_context_sorry) (fun ret_ => True) := by
///   sorry
/// ```
pub fn test_proof_context_sorry() {}

/// Test Case 5: Error mapping to the automatically injected synthetic theorem `post`.
/// We leave the proof blank. The `uses sorry` error should be redirected 
/// to the `ensures` keyword.
/// 
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (test_synthetic_theorem_sorry) (fun ret_ => True) := by
/// ```
pub fn test_synthetic_theorem_sorry() {}


