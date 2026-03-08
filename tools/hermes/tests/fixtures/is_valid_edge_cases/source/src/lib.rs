#![crate_type = "lib"]

// Struct for testing IsValid with explicit definition
/// ```lean, hermes
/// isValid self := self.val > (0 : Int)
/// ```
pub struct Positive {
    pub val: u32,
}

// 1. No arguments, no return
pub fn no_args_no_return() {}

// 2. Immutable arguments, no return
/// ```hermes
/// ensures:
///   True
/// proof:
///   trivial
/// ```
pub fn immutable_args_no_return(_x: u32, _p: Positive) {}

// 3. Mutable arguments, no return
pub fn mutable_args_no_return(_x: &mut Positive) {}

// 4. Immutable args, return value
pub fn immutable_args_return_value(x: Positive) -> Positive {
    x
}

// 5. No arguments, return value
pub fn no_args_return_value() -> Positive {
    Positive { val: 1 }
}

// 6. Mutable arguments, and return value
pub fn mutable_args_return_value(x: &mut Positive) -> Positive {
    let val = x.val;
    x.val = 2;
    Positive { val }
}


