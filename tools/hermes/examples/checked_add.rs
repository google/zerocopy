/// Performs checked addition.
///
/// ```lean, hermes, spec
/// ensures: match ret with
///   | .none => (x : Int) + (y : Int) > I32.max ∨ (x : Int) + (y : Int) < I32.min
///   | .some v => (v : Int) = (x : Int) + (y : Int)
/// ```
pub fn checked_add(x: i32, y: i32) -> Option<i32> {
    x.checked_add(y)
}

fn main() {}
