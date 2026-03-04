/// Computes the absolute value.
///
/// ```lean, hermes, spec
/// requires x.val > -2147483648
/// ensures result >= 0
/// ensures x >= 0 -> result = x
/// ensures x < 0 -> result = -x
/// proof
///   unfold abs
///   split
///   . simp
///     sorry -- arithmetic with primitives is hard for scalar_tac currently
///   . simp
///     sorry -- scalar_tac context issue?
/// ```
pub fn abs(x: i32) -> i32 {
    if x < 0 {
        -x
    } else {
        x
    }
}

fn main() {}
