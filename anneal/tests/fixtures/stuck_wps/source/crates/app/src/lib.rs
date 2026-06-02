// A. 0 postconditions (returns `()`, no `ensures`, no `&mut`)

// A1. Transparent
/// ```lean, anneal, spec
/// -- FIXME: Remove manual sorry once we support omitting proofs
/// theorem spec :
///   Aeneas.Std.WP.spec (post0_trans_noproof) (fun ret_ => True) := by
///   sorry
/// ```
pub fn post0_trans_noproof() {}

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post0_trans_ctx_sorry) (fun ret_ => True) := by
///   sorry
/// ```
pub fn post0_trans_ctx_sorry() {}



// A2. Opaque
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post0_opaque_noproof) (fun ret_ => True) := by
///   sorry
/// ```
pub fn post0_opaque_noproof() { dep::opaque(); }

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post0_opaque_ctx_sorry) (fun ret_ => True) := by
///   sorry
/// ```
pub fn post0_opaque_ctx_sorry() { dep::opaque(); }



// B. 1 implicit postcondition (returns `u32`, 0 user ensures)

// B1. Transparent
/// ```lean, anneal, spec
/// -- FIXME: Remove manual sorry once we support omitting proofs
/// theorem spec :
///   Aeneas.Std.WP.spec (post1_impl_trans_noproof) (fun ret_ => True) := by
///   sorry
/// ```
pub fn post1_impl_trans_noproof() -> u32 { 0 }

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post1_impl_trans_ctx_sorry) (fun ret_ => True) := by
///   sorry
/// ```
pub fn post1_impl_trans_ctx_sorry() -> u32 { 0 }

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post1_impl_trans_named) (fun ret_ => True) := by
///   sorry
/// ```
pub fn post1_impl_trans_named() -> u32 { 0 }

// B2. Opaque
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post1_impl_opaque_noproof) (fun ret_ => True) := by
///   sorry
/// ```
pub fn post1_impl_opaque_noproof() -> u32 { dep::opaque_u32() }

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post1_impl_opaque_ctx_sorry) (fun ret_ => True) := by
///   sorry
/// ```
pub fn post1_impl_opaque_ctx_sorry() -> u32 { dep::opaque_u32() }

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post1_impl_opaque_named) (fun ret_ => True) := by
///   sorry
/// ```
pub fn post1_impl_opaque_named() -> u32 { dep::opaque_u32() }

// C. 1 explicit postcondition (returns `()`, 1 user `ensures`)

// C1. Transparent
/// ```lean, anneal, spec
/// -- FIXME: Remove manual sorry once we support omitting proofs
/// theorem spec :
///   Aeneas.Std.WP.spec (post1_expl_trans_noproof) (fun ret_ => ret_ = () ∧ False) := by
///   sorry
/// ```
pub fn post1_expl_trans_noproof() {}

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post1_expl_trans_ctx_sorry) (fun ret_ => ret_ = () ∧ False) := by
///   sorry
/// ```
pub fn post1_expl_trans_ctx_sorry() {}

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post1_expl_trans_unnamed) (fun ret_ => ret_ = () ∧ False) := by
///   sorry
/// ```
pub fn post1_expl_trans_unnamed() {}

// C2. Opaque
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post1_expl_opaque_noproof) (fun ret_ => ret_ = () ∧ False) := by
///   sorry
/// ```
pub fn post1_expl_opaque_noproof() { dep::opaque(); }

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post1_expl_opaque_ctx_sorry) (fun ret_ => ret_ = () ∧ False) := by
///   sorry
/// ```
pub fn post1_expl_opaque_ctx_sorry() { dep::opaque(); }

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post1_expl_opaque_unnamed) (fun ret_ => ret_ = () ∧ False) := by
///   sorry
/// ```
pub fn post1_expl_opaque_unnamed() { dep::opaque(); }

// D. 2 explicit postconditions (returns `()`, 2 user `ensures`)

// D1. Transparent
/// ```lean, anneal, spec
/// -- FIXME: Remove manual sorry once we support omitting proofs
/// theorem spec :
///   Aeneas.Std.WP.spec (post2_expl_trans_noproof) (fun ret_ => ret_ = () ∧ False) := by
///   sorry
/// ```
pub fn post2_expl_trans_noproof() {}

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post2_expl_trans_ctx_sorry) (fun ret_ => ret_ = () ∧ False) := by
///   sorry
/// ```
pub fn post2_expl_trans_ctx_sorry() {}

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post2_expl_trans_named) (fun ret_ => ret_ = () ∧ False) := by
///   sorry
/// ```
pub fn post2_expl_trans_named() {}

// D2. Opaque
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post2_expl_opaque_noproof) (fun ret_ => ret_ = () ∧ False) := by
///   sorry
/// ```
pub fn post2_expl_opaque_noproof() { dep::opaque(); }

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post2_expl_opaque_ctx_sorry) (fun ret_ => ret_ = () ∧ False) := by
///   sorry
/// ```
pub fn post2_expl_opaque_ctx_sorry() { dep::opaque(); }

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (post2_expl_opaque_named) (fun ret_ => ret_ = () ∧ False) := by
///   sorry
/// ```
pub fn post2_expl_opaque_named() { dep::opaque(); }
