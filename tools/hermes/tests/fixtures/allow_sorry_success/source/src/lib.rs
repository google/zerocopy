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

/// Triggers allow_sorry on the complex isValid autoParam.
/// Should emit a single "declaration uses sorry" warning.
/// ```lean, hermes, spec
/// ```
pub fn unprovable_is_valid() -> InvalidStruct {
    InvalidStruct { x: 1, y: 2 }
}

/// Should NOT trigger any "declaration uses sorry" because simp_all cleanly solves `True` for `ValidStruct`.
/// ```lean, hermes, spec
/// ```
pub fn trivial_is_valid() -> ValidStruct {
    ValidStruct { z: 5 }
}

/// ```lean, hermes, spec
/// requires (h_eq):
///   x = _y
/// ensures:
///   ret = _y
/// proof:
///   have h := h_eq
///   simp_all
/// ```
pub unsafe fn named_precondition_visibility(x: u32, _y: u32) -> u32 {
    x
}
