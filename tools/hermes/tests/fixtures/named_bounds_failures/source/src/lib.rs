/// This file contains failure cases for the Hermes named bounds feature.
/// We test both validation errors (rust-level parsing and validation)
/// and verification errors (Lean-level theorem failures).

/// 1. Multiple unnamed requires clauses
/// ```lean, hermes, spec
/// requires:
///   ///   ///   x > 0
/// requires:
///   ///   ///   y > 0
/// ```
unsafe fn fail_multiple_unnamed_requires(x: u32, y: u32) {
}


/// 2. Multiple unnamed ensures clauses
/// ```lean, hermes, spec
/// ensures:
///   ///   ///   ret == x
/// ensures:
///   ///   ///   ret == y
/// ```
fn fail_multiple_unnamed_ensures(x: u32, y: u32) -> u32 {
    x
}


/// 4. Duplicate clause name
/// ```lean, hermes, spec
/// requires (h_same):
///   ///   ///   x > 0
/// ensures (h_same):
///   ///   ///   ret == x
/// proof context:
/// proof:
///   simp_all
/// ```
unsafe fn fail_duplicate_clause_name(x: u32) -> u32 {
    x
}


/// 5. Mixing named and unnamed proofs
/// ```lean, hermes, spec
/// ensures (h_ensures):
///   ///   ///   ret = x
/// proof context:
/// proof:
///   simp_all
/// ```
fn fail_mixing_named_and_unnamed_proofs(x: u32) -> u32 {
    x
}


/// 8. Mixing named and unnamed ensures
/// ```lean, hermes, spec
/// ensures (h_err):
///   ///   ///   ret = x
/// ensures:
///   ///   ///   ret = x
/// ```
fn fail_mix_named_unnamed_ensures(x: u32) -> u32 {
    x
}




/// 16. Naming an unnamable section
///
/// Trying to name a `proof context` with a trailing colon natively aborts the parser!
/// `Error: "proof context" sections cannot be named.`
/// ```lean, hermes, spec
/// proof context (foo):
///   have h: 1 = 1 := by simp
/// ```
fn fail_name_unnamable_section(x: u32) -> u32 {
    x
}


/// 17. Invalid bound name identifier
///
/// Ensures identifiers strictly follow `[a-zA-Z_][a-zA-Z0-9_]*`.
/// `Error: Invalid bound name 123invalid.`
/// ```lean, hermes, spec
/// requires (123invalid):
///   ///   ///   x > 0
/// ```
unsafe fn fail_invalid_bound_name(x: u32) -> u32 {
    x
}


/// 18. Empty bound name
///
/// Submitting an empty name cleanly aborts the parser.
/// ```lean, hermes, spec
/// requires ():
///   x > 0
/// ```
unsafe fn fail_empty_bound_name(x: u32) -> u32 {
    x
}


/// 19. Missing colon after name
///
/// Omitting the colon after a named bound creates a parser error.
/// ```lean, hermes, spec
/// requires (True):
/// ensures (h_same):
///   ///   ///   ret = x
/// proof context:
/// proof:
///   simp_all
/// ```
unsafe fn fail_missing_colon_creates_error(x: u32) -> u32 {
    x
}


/// 21. Naming a bound a Lean keyword (requires)
/// ```lean, hermes, spec
/// requires (if):
///   ///   ///   x > 0
/// ```
unsafe fn fail_lean_keyword_requires(x: u32) -> u32 {
    x
}


/// 22. Naming a bound a Lean keyword (ensures)
/// ```lean, hermes, spec
/// ensures (then):
///   ///   ///   ret = x
/// ```
fn fail_lean_keyword_ensures(x: u32) -> u32 {
    x
}


/// 24. Duplicate proof names
/// ```lean, hermes, spec
/// ensures (e1):
///   ret = x
/// proof (e1):
///   simp_all
/// proof (e1):
///   simp_all
/// ```
fn fail_duplicate_proof_names(x: u32) -> u32 {
    x
}


/// 25. Mixing named and unnamed requires
/// ```lean, hermes, spec
/// requires (h_err):
///   x > 0
/// requires:
///   x > 0
/// ```
unsafe fn fail_mix_named_unnamed_requires(x: u32) -> u32 {
    x
}

fn main() {}
