/// A simple test for the named bounds feature.
/// 
/// ```lean, hermes, spec
/// requires (req):
///   x > 0
/// ensures (ens):
///   ret > 0
/// proof context:
/// proof (ens):
///   have h : x > 0 := req
///   scalar_tac
/// ```
unsafe fn test_named_bounds(x: u32) -> u32 {
    x
}

/// A test for a single unnamed ensures with an unnamed proof block.
/// 
/// ```lean, hermes, spec
/// ensures:
///   ret = x
/// proof context:
/// proof:
///   simp_all
/// ```
fn test_single_unnamed_ensures(x: u32) -> u32 {
    x
}

/// A test for multiple named requires clauses.
/// 
/// ```lean, hermes, spec
/// requires (r1):
///   x > 0
/// requires (r2):
///   y > 0
/// ensures (ens):
///   ret > 0
/// proof context:
/// proof (ens):
///   have h1 : x > 0 := r1
///   have h2 : y > 0 := r2
///   scalar_tac
/// ```
unsafe fn test_multiple_named_requires(x: u32, y: u32) -> u32 {
    x
}

/// A caller function to verify that we can correctly construct the `Pre` struct for `test_multiple_named_requires`.
///
/// ```lean, hermes, spec
/// requires (req):
///   x > 0
/// ensures (ens):
///   ret > 0
/// proof context:
/// proof (ens):
///   have h0 : x > 0 := req
///   have h_call := test_multiple_named_requires.spec x x { h_x_is_valid := by trivial, h_y_is_valid := by trivial, r1 := h0, r2 := h0 }
///   scalar_tac
/// ```
unsafe fn test_caller_multiple_named_requires(x: u32) -> u32 {
    test_multiple_named_requires(x, x)
}

/// A test for multiple named ensures and named proofs.
///
/// ```lean, hermes, spec
/// ensures (e1):
///   ret = x
/// ensures (e2):
///   ret = x
/// proof context:
/// proof context:
/// proof (e1):
///   simp_all
/// proof (e2):
///   simp_all
/// ```
fn test_multiple_named_ensures(x: u32, y: u32) -> u32 {
    x
}

/// A test for utilizing `proof context` with multiple named proofs.
///
/// ```lean, hermes, spec
/// ensures (e1):
///   ret = x
/// ensures (e2):
///   ret = x
/// proof context:
///   have h_shared : x = x := by rfl
/// proof context:
/// proof (e1):
///   simp_all
/// proof (e2):
///   simp_all
/// ```
fn test_proof_context(x: u32, y: u32) -> u32 {
    x
}

/// A test for auto-injecting `isValid` when a user proof is omitted, but other named proofs are provided.
/// The return type `u32` has an implicit `isValid` bound.
/// 
/// A test for missing implicitly injected `isValid` proofs.
///
/// ```lean, hermes, spec
/// ensures (e1):
///   ret = x
/// proof context:
/// proof (e1):
///   simp_all
/// ```
fn test_missing_proof_injected_isvalid(x: u32) -> u32 {
    x
}

/// A test for a single unnamed requires clause.
/// 
/// ```lean, hermes, spec
/// requires:
///   x > 0
/// ensures (ens):
///   ret = x
/// proof context:
/// proof (ens):
///   simp_all
/// ```
unsafe fn test_single_unnamed_requires(x: u32) -> u32 {
    x
}

/// A caller function to verify that we can correctly construct the `Pre` struct for `test_single_unnamed_requires`.
///
/// ```lean, hermes, spec
/// requires:
///   x > 0
/// ensures (ens):
///   ret = x
/// proof context:
/// proof (ens):
///   have h0 : x > 0 := unnamed
///   have h_call := test_single_unnamed_requires.spec x { h_x_is_valid := by trivial, unnamed := h0 }
///   simp_all
/// ```
unsafe fn test_caller_single_unnamed_requires(x: u32) -> u32 {
    test_single_unnamed_requires(x)
}

/// A test for zero ensures blocks and zero proofs.
/// Hermes should auto-inject proofs for implicit bounds (like isValid).
/// 
/// ```lean, hermes, spec
/// ```
fn test_zero_ensures_no_proof(x: u32) -> u32 {
    x
}

/// A test for manually proving an auto-injected bound.
/// 
/// ```lean, hermes, spec
/// proof context:
/// proof:
///   trivial
/// ```
fn test_manual_proof_for_is_valid(x: u32) -> u32 {
    x
}

/// A function testing multiple disjoint `proof context` blocks.
/// 
/// The parser should loop and concatenate them transparently.
/// ```lean, hermes, spec
/// ensures (h_same):
///   ret = x
/// proof context:
///   have h1: x = x := by simp
/// proof context:
///   have h2: x = x := by simp
/// proof context:
/// proof (h_same):
///   simp_all
/// ```
fn test_multiple_proof_context_blocks(x: u32) -> u32 {
    x
}

/// A function testing `proof context` declared *after* proof cases.
///
/// The parser pushes the blocks into disjoint `cases` and `context` vectors, 
/// so they should render correctly with `context` first in Lean regardless of 
/// declaration order in Rust.
/// ```lean, hermes, spec
/// ensures (h_same):
///   ret = x
/// proof context:
/// proof (h_same):
///   simp_all
/// proof context:
///   have h1: x = x := by simp
/// ```
fn test_proof_context_at_end(x: u32) -> u32 {
    x
}

/// A function using leading underscores for explicit bounds, avoiding unused variable warnings in Lean.
/// ```lean, hermes, spec
/// requires (_h_same):
///   x > 0
/// ensures (_h_ens):
///   ret = x
/// proof context:
/// proof (_h_ens):
///   simp_all
/// ```
unsafe fn test_leading_underscore_name(x: u32) -> u32 {
    x
}

/// A function with an empty `proof context` block.
///
/// The parser should gracefully ingest the empty lines without disrupting Lean proofs.
/// ```lean, hermes, spec
/// ensures (h_same):
///   ret = x
/// proof context:
/// proof context:
/// proof (h_same):
///   simp_all
/// ```
fn test_empty_proof_context(x: u32) -> u32 {
    x
}

/// A test showing that explicitly naming a requirement `unnamed` passes validation
/// and does not natively collide with the implicitly reserved `unnamed` token.
/// ```lean, hermes, spec
/// requires (unnamed):
///   x > 0
/// ensures (ens):
///   ret = x
/// proof context:
/// proof (ens):
///   simp_all
/// ```
unsafe fn test_explicit_unnamed_requires(x: u32) -> u32 {
    x
}

/// A test showing that a `proof context` fulfills the requirement for an `inner: Proof`, 
/// even when `cases` is empty. The `simp_all` or `sorry` fallback generates the missing cases as designed.
/// ```lean, hermes, spec
/// ensures (ens):
///   ret = x
/// proof context:
///   have h: x = x := by simp
/// proof (ens):
///   sorry
/// ```
fn test_proof_context_without_cases(x: u32) -> u32 {
    x
}

/// A function verifying that `unsafe(axiom)` blocks correctly parse.
/// ```lean, hermes, unsafe(axiom)
/// axiom:
///   some_axiom_content
/// ```
unsafe fn test_axiom_pseudo_name() {}

/// A test confirming that `isValid` fields on `Pre` struct instantiations
/// can be completely omitted due to the `verify_is_valid` autoParam tactic.
/// 
/// ```lean, hermes, spec
/// requires (r1):
///   x > 0
/// ensures (ens):
///   ret > 0
/// proof context:
/// proof (ens):
///   have h1 : x > 0 := r1
///   scalar_tac
/// ```
unsafe fn test_explicit_requires(x: u32) -> u32 {
    x
}

/// A calling function that asserts Lean allows omitting `h_x_is_valid`.
/// 
/// ```lean, hermes, spec
/// requires (r1):
///   x > 0
/// ensures (ens):
///   ret > 0
/// proof context:
/// proof (ens):
///   have h1 : x > 0 := r1
///   -- We instantiate `Pre x` but omit the `h_x_is_valid` field!
///   have _h_call := test_explicit_requires.spec x { r1 := h1 }
///   scalar_tac
/// ```
unsafe fn test_implicit_is_valid_instantiation(x: u32) -> u32 {
    test_explicit_requires(x)
}

/// A function verifying that entirely empty `axiom` blocks compile correctly.
/// ```lean, hermes, unsafe(axiom)
/// ```
unsafe fn test_empty_axiom() {}

/// A function with zero arguments but explicit specifications.
/// The Pre structure should be generated uniquely.
///
/// ```lean, hermes, spec
/// requires (h_req):
///   true
/// ensures (h_ens):
///   true
/// proof (h_ens):
///   trivial
/// ```
unsafe fn test_zero_args_with_bounds() {}

/// A function with zero arguments and no specifications.
/// The Pre structure should be completely omitted.
/// 
/// ```lean, hermes, spec
/// ```
fn test_zero_args_no_bounds() {}

/// Explicitly naming a bound "unnamed", which is the fallback name.
/// 
/// ```lean, hermes, spec
/// requires (unnamed):
///   x > 0
/// ensures (ens):
///   ret = x
/// proof (ens):
///   simp_all
/// ```
unsafe fn test_explicit_unnamed_name(x: u32) -> u32 { x }

/// Missing proof body. It should just fall back to standard sorry/simp_all.
/// 
/// ```lean, hermes, spec
/// ensures (ens):
///   ret = x
/// proof (ens):
/// ```
fn test_empty_proof_block_named(x: u32) -> u32 { x }

/// Proof context after a proof block.
/// They should all be aggregated correctly.
/// 
/// ```lean, hermes, spec
/// ensures (ens):
///   ret = x
/// proof (ens):
///   simp_all
/// proof context:
///   have _h : 1 = 1 := by rfl
/// ```
fn test_proof_context_after_proof(x: u32) -> u32 { x }

/// Single unnamed requires with named ensures.
/// This is valid because the multiple-rule applies per-category.
/// 
/// ```lean, hermes, spec
/// requires:
///   x > 0
/// ensures (h_ens):
///   ret = x
/// proof (h_ens):
///   simp_all
/// ```
unsafe fn test_single_unnamed_requires_with_named_ensures(x: u32) -> u32 { x }

/// Multiple proof context blocks.
/// They should be aggregated sequentially in the Lean output.
/// 
/// ```lean, hermes, spec
/// ensures (ens):
///   ret = x
/// proof context:
///   have _h1 : 1 = 1 := by rfl
/// proof context:
///   have _h2 : 2 = 2 := by rfl
/// proof (ens):
///   simp_all
/// ```
fn test_multiple_proof_context_blocks_named(x: u32) -> u32 { x }

/// Target a mutable reference implicit bound.
/// 
/// ```lean, hermes, spec
/// proof (h_x_new_is_valid):
///   simp_all [Hermes.IsValid.isValid]
/// ```
fn test_proof_targets_mut_ref_is_valid(x: &mut u32) {}


/// A function with interleaved requires and ensures declarations.
/// The parser should aggregate them into their respective categories based on the name of the clause.
/// ```lean, hermes, spec
/// requires (r1):
///   x > 0
/// ensures (e1):
///   ret = x
/// requires (r2):
///   x > 0
/// ensures (e2):
///   ret > 0
/// proof (e1):
///   simp_all
/// proof (e2):
///   have h2 : x > 0 := r2
///   scalar_tac
/// ```
unsafe fn test_interleaved_clauses(x: u32) -> u32 { x }

/// A function with out-of-order bounds. Ensures before requires, proof before ensures, etc.
/// ```lean, hermes, spec
/// ensures (e1):
///   ret = x
/// requires (r1):
///   x > 0
/// proof (e1):
///   simp_all
/// ensures (e2):
///   ret > 0
/// proof (e2):
///   have h1 : x > 0 := r1
///   scalar_tac
/// ```
unsafe fn test_out_of_order_clauses(x: u32) -> u32 { x }

/// A function with completely empty lines inside a proof block.
/// ```lean, hermes, spec
/// ensures (e1):
///   ret = x
/// proof (e1):
/// 
///   simp_all
/// 
/// ```
fn test_blank_lines_in_proof(x: u32) -> u32 { x }

/// A function using an absurdly long bound name.
/// ```lean, hermes, spec
/// requires (this_is_a_very_long_name_this_is_a_very_long_name_this_is_a_very_long_name):
///   x > 0
/// ensures (ens):
///   ret = x
/// proof (ens):
///   simp_all
/// ```
unsafe fn test_very_long_bound_name(x: u32) -> u32 { x }

/// A function with absolutely no parameters, requires, or ensures.
/// Should generate cleanly and omit the `Pre` and `Post` structs entirely
/// (if there are no implicit bounds either).
fn test_zero_guarantees_zero_params() {}

/// A function with a single anonymous ensures clause and an anonymous proof.
/// The parser should map the ensures clause to the `unnamed` dummy field,
/// and the generator should inject the anonymous proof into the `case unnamed` branch.
/// ```lean, hermes, spec
/// ensures:
///   ret = 0#u32
/// proof:
///   scalar_tac
/// ```
fn test_single_anonymous_dummy_ensures() -> u32 { 0 }


fn main() {}
