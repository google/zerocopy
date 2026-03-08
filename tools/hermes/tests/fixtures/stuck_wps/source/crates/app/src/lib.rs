// A. 0 postconditions (returns `()`, no `ensures`, no `&mut`)

// A1. Transparent
/// ```hermes
/// ```
pub fn post0_trans_noproof() {}

/// ```hermes
/// proof context:
///   sorry
/// ```
pub fn post0_trans_ctx_sorry() {}



// A2. Opaque
/// ```hermes
/// ```
pub fn post0_opaque_noproof() { dep::opaque(); }

/// ```hermes
/// proof context:
///   sorry
/// ```
pub fn post0_opaque_ctx_sorry() { dep::opaque(); }



// B. 1 implicit postcondition (returns `u32`, 0 user ensures)

// B1. Transparent
/// ```hermes
/// ```
pub fn post1_impl_trans_noproof() -> u32 { 0 }

/// ```hermes
/// proof context:
///   sorry
/// ```
pub fn post1_impl_trans_ctx_sorry() -> u32 { 0 }

/// ```hermes
/// proof (h_ret_is_valid):
///   sorry
/// ```
pub fn post1_impl_trans_named() -> u32 { 0 }

// B2. Opaque
/// ```hermes
/// ```
pub fn post1_impl_opaque_noproof() -> u32 { dep::opaque_u32() }

/// ```hermes
/// proof context:
///   sorry
/// ```
pub fn post1_impl_opaque_ctx_sorry() -> u32 { dep::opaque_u32() }

/// ```hermes
/// proof (h_ret_is_valid):
///   sorry
/// ```
pub fn post1_impl_opaque_named() -> u32 { dep::opaque_u32() }

// C. 1 explicit postcondition (returns `()`, 1 user `ensures`)

// C1. Transparent
/// ```hermes
/// ensures: ret == ()
/// ```
pub fn post1_expl_trans_noproof() {}

/// ```hermes
/// ensures: ret == ()
/// proof context:
///   sorry
/// ```
pub fn post1_expl_trans_ctx_sorry() {}

/// ```hermes
/// ensures: ret == ()
/// proof:
///   sorry
/// ```
pub fn post1_expl_trans_unnamed() {}

// C2. Opaque
/// ```hermes
/// ensures: ret == ()
/// ```
pub fn post1_expl_opaque_noproof() { dep::opaque(); }

/// ```hermes
/// ensures: ret == ()
/// proof context:
///   sorry
/// ```
pub fn post1_expl_opaque_ctx_sorry() { dep::opaque(); }

/// ```hermes
/// ensures: ret == ()
/// proof:
///   sorry
/// ```
pub fn post1_expl_opaque_unnamed() { dep::opaque(); }

// D. 2 explicit postconditions (returns `()`, 2 user `ensures`)

// D1. Transparent
/// ```hermes
/// ensures (h1): ret == ()
/// ensures (h2): ret == ()
/// ```
pub fn post2_expl_trans_noproof() {}

/// ```hermes
/// ensures (h1): ret == ()
/// ensures (h2): ret == ()
/// proof context:
///   sorry
/// ```
pub fn post2_expl_trans_ctx_sorry() {}

/// ```hermes
/// ensures (h1): ret == ()
/// ensures (h2): ret == ()
/// proof (h1):
///   sorry
/// proof (h2):
///   sorry
/// ```
pub fn post2_expl_trans_named() {}

// D2. Opaque
/// ```hermes
/// ensures (h1): ret == ()
/// ensures (h2): ret == ()
/// ```
pub fn post2_expl_opaque_noproof() { dep::opaque(); }

/// ```hermes
/// ensures (h1): ret == ()
/// ensures (h2): ret == ()
/// proof context:
///   sorry
/// ```
pub fn post2_expl_opaque_ctx_sorry() { dep::opaque(); }

/// ```hermes
/// ensures (h1): ret == ()
/// ensures (h2): ret == ()
/// proof (h1):
///   sorry
/// proof (h2):
///   sorry
/// ```
pub fn post2_expl_opaque_named() { dep::opaque(); }
