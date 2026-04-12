/// This file contains failure cases for the Anneal named bounds feature.
/// We test both validation errors (rust-level parsing and validation)
/// and verification errors (Lean-level theorem failures).

/// 1. Multiple anon requires clauses
/// ```lean, anneal, spec
/// requires:
///   ///   ///   x > 0
/// requires:
///   ///   ///   y > 0
/// ```
unsafe fn fail_multiple_anon_requires(x: u32, y: u32) {
}


/// 2. Multiple anon ensures clauses
/// ```lean, anneal, spec
/// ensures:
///   ///   ///   ret == x
/// ensures:
///   ///   ///   ret == y
/// ```
fn fail_multiple_anon_ensures(x: u32, y: u32) -> u32 {
    x
}


/// 4. Duplicate clause name
/// ```lean, anneal, spec
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


/// 5. Mixing named and anon proofs
/// ```lean, anneal, spec
/// ensures (h_ensures):
///   ///   ///   ret = x
/// proof context:
/// proof:
///   simp_all
/// ```
fn fail_mixing_named_and_anon_proofs(x: u32) -> u32 {
    x
}


/// 8. Mixing named and anon ensures
/// ```lean, anneal, spec
/// ensures (h_err):
///   ///   ///   ret = x
/// ensures:
///   ///   ///   ret = x
/// ```
fn fail_mix_named_anon_ensures(x: u32) -> u32 {
    x
}




/// 16. Naming an unnamable section
///
/// Trying to name a `proof context` with a trailing colon natively aborts the parser!
/// `Error: "proof context" sections cannot be named.`
/// ```lean, anneal, spec
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
/// ```lean, anneal, spec
/// requires (123invalid):
///   ///   ///   x > 0
/// ```
unsafe fn fail_invalid_bound_name(x: u32) -> u32 {
    x
}


/// 18. Empty bound name
///
/// Submitting an empty name cleanly aborts the parser.
/// ```lean, anneal, spec
/// requires ():
///   x > 0
/// ```
unsafe fn fail_empty_bound_name(x: u32) -> u32 {
    x
}


/// 19. Missing colon after name
///
/// Omitting the colon after a named bound creates a parser error.
/// ```lean, anneal, spec
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
/// ```lean, anneal, spec
/// requires (if):
///   ///   ///   x > 0
/// ```
unsafe fn fail_lean_keyword_requires(x: u32) -> u32 {
    x
}


/// 22. Naming a bound a Lean keyword (ensures)
/// ```lean, anneal, spec
/// ensures (then):
///   ///   ///   ret = x
/// ```
fn fail_lean_keyword_ensures(x: u32) -> u32 {
    x
}


/// 24. Duplicate proof names
/// ```lean, anneal, spec
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


/// 25. Mixing named and anon requires
/// ```lean, anneal, spec
/// requires (h_err):
///   x > 0
/// requires:
///   x > 0
/// ```
unsafe fn fail_mix_named_anon_requires(x: u32) -> u32 {
    x
}

fn main() {}
