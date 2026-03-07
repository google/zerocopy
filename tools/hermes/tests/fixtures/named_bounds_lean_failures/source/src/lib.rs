/// This file contains failure cases for the Hermes named bounds feature.
/// We test both validation errors (rust-level parsing and validation)
/// and verification errors (Lean-level theorem failures).


/// 6. Unnamed ensures verification failure mathematically
/// ```lean, hermes, spec
/// ensures:
///   ///   ///   ret = 0
/// proof context:
/// proof:
///   simp_all
/// ```
fn fail_unnamed_ensures_verification(x: u32) -> u32 {
    1
}


/// ```lean, hermes
/// isValid self := self.val > 0
/// ```
pub struct Positive {
    pub val: u32,
}


/// 7. isValid verification failure
/// ```lean, hermes, spec
/// ensures (e1):
///   ///   ///   ret.val = x.val
/// proof context:
/// proof:
///   simp_all
/// ```
fn fail_is_valid_verification(x: Positive) -> Positive {
    Positive { val: 0 }
}


/// 12. Bypassing validation with extra `proof (unnamed)`
///
/// If a function returns a value (generating an `isValid` boundary), 
/// `validate.rs` natively adds `"unnamed"` into `valid_names`. 
/// By providing all necessary named proofs AND an extra `proof (unnamed)`,
/// validation succeeds natively. However, `generate.rs` does not emit 
/// the `unnamed` field in the structure because no unnamed ensures exist.
/// This will correctly generate a Lean failure!
/// ```lean, hermes, spec
/// ensures (h_foo):
///   ///   ///   ret = x
/// proof context:
/// proof:
///   simp_all
/// proof (h_foo):
///   simp_all
/// ```
fn fail_extra_unnamed_proof_bypasses_validation(x: u32) -> u32 {
    x
}


/// 13. Proof context tactic failure
/// ```lean, hermes, spec
/// ensures (ens):
///   ///   ///   ret = x
/// proof context:
///   have h: false := by simp
/// proof context:
/// proof:
///   simp_all
/// ```
fn fail_proof_context_tactic_failure(x: u32) -> u32 {
    x
}


/// 20. Dropped unnamed proof bypass
///
/// Because returning a value generates a post-condition, `validate.rs` used to accept `proof (unnamed)`.
/// However `generate.rs` never maps it, natively dropping the `have h` proof completely!
/// This now correctly fails validation because `unnamed` is only reserved if explicitly specified in `ensures`.
/// ```lean, hermes, spec
/// proof context:
/// proof:
///   have h: 1 = 1 := by simp
///   simp_all
/// ```
fn fail_dropped_proof(x: u32) -> u32 {
    x
}


/// 23. Naming a proof a Lean keyword
/// ```lean, hermes, spec
/// ensures (ens):
///   ///   ///   ret = x
/// proof context:
/// proof:
///   simp_all
/// ```
fn fail_lean_keyword_proof(x: u32) -> u32 {
    x
}

/// 27. Using Lean `ret` inside requires instead of ensures
///
/// `ret` is a WP variable. It should not exist in the Pre structure.
/// ```lean, hermes, spec
/// requires (h_impossible):
///   ret = x
/// ```
unsafe fn fail_ret_in_requires(x: u32) -> u32 {
    x
}
/// 29. Naming a rust argument `ret` to shadow the WP variable
///
/// If we name an argument `ret`, it will be passed into the context as `ret`.
/// But Hermes WP generation will also introduce the return value as `ret`.
/// This should cause Lean to fail due to variable shadowing or duplicate binders!
/// ```lean, hermes, spec
/// ensures (ens):
///   ret = 0
/// proof (ens):
///   simp_all
/// ```
fn fail_argument_named_ret(ret: u32) -> u32 {
    0
}

/// 30. Unknown variable in requires clause
/// ```lean, hermes, spec
/// requires (h):
///   unknown_var > 0
/// ```
unsafe fn fail_unknown_variable_in_requires(x: u32) -> u32 {
    x
}

fn main() {}
