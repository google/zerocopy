/// Computes the absolute value.
///
/// ```lean, hermes, spec
/// ensures result >= 0
/// ensures x >= 0 -> result = x
/// ensures x < 0 -> result = -x
/// proof
///   unfold abs
///   split <;> simp_all
/// ```
pub fn abs(x: i32) -> i32 {
    if x < 0 {
        -x
    } else {
        x
    }
}

fn main() {}
