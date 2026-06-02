// Struct for testing IsValid with explicit definition
/// ```lean, anneal
/// def isValid (self : InvalidStruct) : Prop := self.x.val > self.y.val
/// ```
pub struct InvalidStruct {
    // Has a non-trivial IsValid
    pub x: u32,
    pub y: u32,
}

pub struct ValidStruct {
    // Trivial IsValid
    pub z: u32,
}

/// No proof provided, triggers allow_sorry on user bound
///
/// ```lean, anneal, spec
/// -- FIXME: Remove manual sorry once we support omitting proofs
/// theorem spec :
///   Aeneas.Std.WP.spec (missing_user_bound) (fun ret_ => ret_ = ¬ ret_) := by
///   sorry
/// ```
pub fn missing_user_bound() -> bool {
    true
}

/// Triggers allow_sorry on the complex isValid autoParam
/// ```lean, anneal, spec
/// -- FIXME: Remove manual sorry once we support omitting proofs
/// theorem spec :
///   Aeneas.Std.WP.spec (unprovable_is_valid) (fun ret_ => InvalidStruct.isValid ret_) := by
///   sorry
/// ```
pub fn unprovable_is_valid() -> InvalidStruct {
    InvalidStruct { x: 1, y: 2 }
}

/// Should NOT trigger any "declaration uses sorry" because simp_all cleanly solves `True`
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (trivial_is_valid) (fun ret_ => True) := by
///   simp_all
/// ```
pub fn trivial_is_valid() -> ValidStruct {
    ValidStruct { z: 5 }
}

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (explicit_broken_proof) (fun ret_ => True) := by
///   exact {
///       invalid_tactic
///   }
/// ```
pub fn explicit_broken_proof() -> InvalidStruct {
    InvalidStruct { x: 1, y: 2 }
}

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (explicit_semantic_failure) (fun ret_ => True = False) := by
///   rfl
/// ```
pub fn explicit_semantic_failure() {
}

/// ```lean, anneal, unsafe(axiom)
/// axiom spec (cond : Bool) (h_req : cond = true) :
///   Aeneas.Std.WP.spec (expects_precondition cond) (fun ret_ => True)
/// ```
pub unsafe fn expects_precondition(cond: bool) {}

/// Should fail with "unsolved goals" or tactic failure, not "uses sorry"
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (fail_to_prove_precondition) (fun ret_ => True) := by
///   have h_call := expects_precondition.spec false (by rfl)
///   simp_all
/// ```
pub fn fail_to_prove_precondition() {
    unsafe {
        expects_precondition(false);
    }
}
