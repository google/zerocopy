#![crate_type = "lib"]

// Struct for testing IsValid with explicit definition
/// ```lean, hermes
/// isValid self := self.val > 0
/// ```
pub struct Positive {
    pub val: u32,
}

// 1. No arguments, no return
/// ```hermes
/// proof
///   unfold no_args_no_return
///   simp
/// ```
pub fn no_args_no_return() {}

// 2. Immutable arguments, no return
/// ```hermes
/// ensures True
/// proof
///   unfold immutable_args_no_return
///   simp_all [Hermes.IsValid.isValid]
/// ```
pub fn immutable_args_no_return(_x: u32, _p: Positive) {}

// 3. Mutable arguments, no return
/// ```hermes
/// proof
///   unfold mutable_args_no_return
///   simp_all [Hermes.IsValid.isValid]
/// ```
pub fn mutable_args_no_return(x: &mut Positive) {}

// 4. Immutable args, return value
/// ```hermes
/// proof
///   unfold immutable_args_return_value
///   simp_all [Hermes.IsValid.isValid]
/// ```
pub fn immutable_args_return_value(x: Positive) -> Positive {
    x
}

// 5. No arguments, return value
/// ```hermes
/// proof
///   unfold no_args_return_value
///   simp_all [Hermes.IsValid.isValid]
///   decide
/// ```
pub fn no_args_return_value() -> Positive {
    Positive { val: 1 }
}

// 6. Mutable arguments, and return value
/// ```hermes
/// proof
///   unfold mutable_args_return_value
///   simp_all [Hermes.IsValid.isValid]
///   decide
/// ```
pub fn mutable_args_return_value(x: &mut Positive) -> Positive {
    let val = x.val;
    x.val = 2;
    Positive { val }
}
