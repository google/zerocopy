/// ```lean, hermes, unsafe(axiom)
/// requires b.val > 0
/// ensures ret.val = a.val / b.val
/// ```
#[allow(unused_unsafe)]
pub unsafe fn safe_div(a: u32, b: u32) -> u32 {
    unsafe { a / b }
}

/// ```lean, hermes, spec
/// ensures ret.val = a.val
/// proof
///   rw [wrapper]
///   obtain ⟨ret_val, h_eq⟩ := safe_div_spec a 1#u32 (by decide)
///   simp_all [Nat.div_one]
///   omega
/// ```
pub fn wrapper(a: u32) -> u32 {
    unsafe { safe_div(a, 1) }
}

/// ```lean, hermes
/// isValid self := 2 | self.x.val
/// ```
pub struct Even {
    #[allow(dead_code)]
    x: usize,
}

/// ```lean, hermes
/// isSafe : ...
/// ```
pub unsafe trait FromBytes {}

/// ```lean, hermes, spec
/// ensures ret.val = x.val
/// proof
///   -- We will use sorry here for unproven things to allow verification to proceed
///   sorry
/// ```
pub fn read_val(x: &u32) -> u32 {
    *x
}

/// ```lean, hermes, spec
/// ensures x'.val = x.val + add.val
/// proof
///   sorry
/// ```
pub fn add_in_place(x: &mut u32, add: u32) {
    *x += add;
}

/// ```lean, hermes
/// requires stack.len > 0
/// ensures stack'.len = stack.len - 1
/// ensures ret = stack[stack.len - 1]
/// proof
///   sorry
/// ```
pub fn pop(stack: &mut Vec<u32>) -> u32 {
    stack.pop().unwrap()
}

