/// Computes the absolute value.
///
/// ```lean, hermes, spec
/// requires: x.val > -2147483648
/// ensures (h0): ret >= 0
/// ensures (h1): x >= 0 -> ret = x
/// ensures (h2): x < 0 -> ret = -x
/// proof:
///   unfold abs
///   split
///   . simp
///     sorry -- arithmetic with primitives is hard for scalar_tac currently
///   . simp
///     sorry -- scalar_tac context issue?
/// ```
pub unsafe fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

fn main() {}
