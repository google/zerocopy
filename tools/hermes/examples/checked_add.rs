/// Safe addition.
///
/// ```lean, hermes, spec
/// ensures match result with
///   | .none => x + y > I32.max ∨ x + y < I32.min
///   | .some v => v = x + y
/// proof
///   unfold checked_add
///   simp_all
/// ```
pub fn checked_add(x: i32, y: i32) -> Option<i32> {
    x.checked_add(y)
}

fn main() {}
