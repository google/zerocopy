/// This file contains failure cases for the Hermes named bounds feature.
/// We test both validation errors (rust-level parsing and validation)
/// and verification errors (Lean-level theorem failures).


/// 3. Mismatched proof name
/// ```lean, hermes, spec
/// ensures (h_ensures):
///   ///   ///   ret == x
/// proof context:
/// proof (h_missing):
///   simp_all
/// ```
fn fail_mismatched_proof_name(x: u32) -> u32 {
    x
}


/// 9. Reserved name collision (requires)
/// ```lean, hermes, spec
/// requires (h_x_is_valid):
///   ///   ///   x > 0
/// ensures (ens):
///   ///   ///   ret = x
/// proof context:
/// proof:
///   simp_all
/// ```
unsafe fn fail_reserved_name_collision_requires(x: u32) -> u32 {
    x
}


/// 10. Reserved name collision (ensures)
/// ```lean, hermes, spec
/// ensures (h_ret_is_valid):
///   ///   ///   ret = x
/// proof context:
/// proof:
///   simp_all
/// ```
fn fail_reserved_name_collision_ensures(x: u32) -> u32 {
    x
}


/// 26. Proof targets a requires clause instead of an ensures clause
/// ```lean, hermes, spec
/// requires (h_req):
///   x > 0
/// proof (h_req):
///   simp_all
/// ```
unsafe fn fail_proof_targets_requires(x: u32) -> u32 {
    x
}

/// 28. Missing named ensures but providing a named proof when an unnamed ensures is present
/// ```lean, hermes, spec
/// ensures:
///   x > 0
/// proof (h_foo):
///   simp_all
/// ```
unsafe fn fail_missing_ensures_for_named_proof_with_unnamed_ensures_present(x: u32) -> u32 {
    x
}

/// 30. Empty requires clause
/// ```lean, hermes, spec
/// requires (r1):
/// 
/// ensures (e1):
///   ret = x
/// proof (e1):
///   simp_all
/// ```
unsafe fn fail_empty_requires_clause(x: u32) -> u32 {
    x
}

/// 31. Empty ensures clause
/// ```lean, hermes, spec
/// ensures (e1):
/// 
/// ```
unsafe fn fail_empty_ensures_clause(x: u32) -> u32 {
    x
}

fn main() {}
