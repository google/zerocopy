#![crate_type = "lib"]

// Struct for testing IsValid with explicit definition
/// ```lean, hermes
/// isValid self := self.val > (0 : Int)
/// ```
pub struct Positive {
    pub val: u32,
}

// 1. No arguments, no return
/// ```hermes
/// proof context:
///   unfold is_valid_edge_cases.no_args_no_return
///   simp_all
///   all_goals try scalar_tac
///   all_goals try rfl
/// ```
pub fn no_args_no_return() {}

// 2. Immutable arguments, no return
/// ```hermes
/// ensures:
///   True
/// proof context:
///   unfold is_valid_edge_cases.immutable_args_no_return
///   simp_all
///   all_goals try scalar_tac
///   all_goals try rfl
/// proof:
///   trivial
/// ```
pub fn immutable_args_no_return(_x: u32, _p: Positive) {}

// 3. Mutable arguments, no return
/// ```hermes
/// proof context:
///   unfold is_valid_edge_cases.mutable_args_no_return
///   have h := h_x_is_valid
///   simp_all
///   all_goals try scalar_tac
///   all_goals try rfl
/// ```
pub fn mutable_args_no_return(x: &mut Positive) {}

// 4. Immutable args, return value
/// ```hermes
/// proof context:
///   unfold is_valid_edge_cases.immutable_args_return_value
///   have h := h_x_is_valid
///   simp_all
///   all_goals try scalar_tac
///   all_goals try rfl
/// ```
pub fn immutable_args_return_value(x: Positive) -> Positive {
    x
}

// 5. No arguments, return value
/// ```hermes
/// proof context:
///   unfold is_valid_edge_cases.no_args_return_value
///   simp_all
///   all_goals try scalar_tac
///   all_goals try rfl
/// ```
pub fn no_args_return_value() -> Positive {
    Positive { val: 1 }
}

// 6. Mutable arguments, and return value
/// ```hermes
/// proof context:
///   unfold is_valid_edge_cases.mutable_args_return_value
///   have h := h_x_is_valid
///   simp_all
///   all_goals try scalar_tac
///   all_goals try rfl
/// ```
pub fn mutable_args_return_value(x: &mut Positive) -> Positive {
    let val = x.val;
    x.val = 2;
    Positive { val }
}
