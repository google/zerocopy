// A. 0 postconditions (returns `()`, no `ensures`, no `&mut`)

// A1. Transparent
/// ```anneal
/// ```
pub fn post0_trans_noproof() {}

/// ```anneal
/// proof context:
///   sorry
/// ```
pub fn post0_trans_ctx_sorry() {}



// A2. Opaque
/// ```anneal
/// proof (h_progress):
///   sorry
/// ```
pub fn post0_opaque_noproof() { dep::opaque(); }

/// ```anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   sorry
/// ```
pub fn post0_opaque_ctx_sorry() { dep::opaque(); }



// B. 1 implicit postcondition (returns `u32`, 0 user ensures)

// B1. Transparent
/// ```anneal
/// ```
pub fn post1_impl_trans_noproof() -> u32 { 0 }

/// ```anneal
/// proof context:
///   sorry
/// ```
pub fn post1_impl_trans_ctx_sorry() -> u32 { 0 }

/// ```anneal
/// proof (h_ret_is_valid):
///   sorry
/// ```
pub fn post1_impl_trans_named() -> u32 { 0 }

// B2. Opaque
/// ```anneal
/// proof (h_progress):
///   sorry
/// ```
pub fn post1_impl_opaque_noproof() -> u32 { dep::opaque_u32() }

/// ```anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   sorry
/// ```
pub fn post1_impl_opaque_ctx_sorry() -> u32 { dep::opaque_u32() }

/// ```anneal
/// proof (h_progress):
///   sorry
/// proof (h_ret_is_valid):
///   sorry
/// ```
pub fn post1_impl_opaque_named() -> u32 { dep::opaque_u32() }

// C. 1 explicit postcondition (returns `()`, 1 user `ensures`)

// C1. Transparent
/// ```anneal
/// ensures: ret == () ∧ False
/// ```
pub fn post1_expl_trans_noproof() {}

/// ```anneal
/// ensures: ret == () ∧ False
/// proof context:
///   sorry
/// ```
pub fn post1_expl_trans_ctx_sorry() {}

/// ```anneal
/// ensures: ret == () ∧ False
/// proof:
///   sorry
/// ```
pub fn post1_expl_trans_unnamed() {}

// C2. Opaque
/// ```anneal
/// ensures: ret == () ∧ False
/// proof (h_progress):
///   sorry
/// ```
pub fn post1_expl_opaque_noproof() { dep::opaque(); }

/// ```anneal
/// ensures: ret == () ∧ False
/// proof (h_progress):
///   sorry
/// proof context:
///   sorry
/// ```
pub fn post1_expl_opaque_ctx_sorry() { dep::opaque(); }

/// ```anneal
/// ensures: ret == () ∧ False
/// proof (h_progress):
///   sorry
/// proof:
///   sorry
/// ```
pub fn post1_expl_opaque_unnamed() { dep::opaque(); }

// D. 2 explicit postconditions (returns `()`, 2 user `ensures`)

// D1. Transparent
/// ```anneal
/// ensures (h1): ret == () ∧ False
/// ensures (h2): ret == () ∧ False
/// ```
pub fn post2_expl_trans_noproof() {}

/// ```anneal
/// ensures (h1): ret == () ∧ False
/// ensures (h2): ret == () ∧ False
/// proof context:
///   sorry
/// ```
pub fn post2_expl_trans_ctx_sorry() {}

/// ```anneal
/// ensures (h1): ret == () ∧ False
/// ensures (h2): ret == () ∧ False
/// proof (h1):
///   sorry
/// proof (h2):
///   sorry
/// ```
pub fn post2_expl_trans_named() {}

// D2. Opaque
/// ```anneal
/// ensures (h1): ret == () ∧ False
/// ensures (h2): ret == () ∧ False
/// proof (h_progress):
///   sorry
/// ```
pub fn post2_expl_opaque_noproof() { dep::opaque(); }

/// ```anneal
/// ensures (h1): ret == () ∧ False
/// ensures (h2): ret == () ∧ False
/// proof (h_progress):
///   sorry
/// proof context:
///   sorry
/// ```
pub fn post2_expl_opaque_ctx_sorry() { dep::opaque(); }

/// ```anneal
/// ensures (h1): ret == () ∧ False
/// ensures (h2): ret == () ∧ False
/// proof (h_progress):
///   sorry
/// proof (h1):
///   sorry
/// proof (h2):
///   sorry
/// ```
pub fn post2_expl_opaque_named() { dep::opaque(); }
