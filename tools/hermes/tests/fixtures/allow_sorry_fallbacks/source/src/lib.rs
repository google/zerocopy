// Struct for testing IsValid with explicit definition
/// ```lean, hermes
/// isValid self := self.x > self.y
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
/// ```lean, hermes, spec
/// ensures:
///   ret == true
/// ```
pub fn missing_user_bound() -> bool {
    true
}

/// Triggers allow_sorry on the complex isValid autoParam
/// ```lean, hermes, spec
/// ```
pub fn unprovable_is_valid() -> InvalidStruct {
    InvalidStruct { x: 1, y: 2 }
}

/// Should NOT trigger any "declaration uses sorry" because simp_all cleanly solves `True`
/// ```lean, hermes, spec
/// ```
pub fn trivial_is_valid() -> ValidStruct {
    ValidStruct { z: 5 }
}

/// ```lean, hermes, spec
/// ensures:
///   ret == true
/// proof:
///   -- A deliberately broken explicit proof should NOT emit "declaration uses sorry"
///   -- but instead natively fail on the syntax error "unknown tactic".
///   exact {
///       invalid_tactic
///   }
/// ```
pub fn explicit_broken_proof() -> InvalidStruct {
    InvalidStruct { x: 1, y: 2 }
}

/// ```lean, hermes, spec
/// ensures (h):
///   true == false
/// proof (h):
///   rfl
/// ```
pub fn explicit_semantic_failure() {
}

/// ```lean, hermes, spec
/// requires:
///   cond
/// ```
pub unsafe fn expects_precondition(cond: bool) {}

/// Should fail with "unsolved goals" or tactic failure, not "uses sorry"
/// ```lean, hermes, spec
/// proof:
///   rfl
/// ```
pub fn fail_to_prove_precondition() {
    unsafe {
        expects_precondition(false);
    }
}
