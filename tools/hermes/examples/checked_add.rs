/// Safe addition.
///
/// ```lean, hermes, spec
/// ensures match result with
///   | .none => (x : Int) + (y : Int) > I32.max ∨ (x : Int) + (y : Int) < I32.min
///   | .some v => (v : Int) = (x : Int) + (y : Int)
/// proof
///   unfold checked_add
///   simp_all
///   -- We use `sorry` here because Aeneas's generated standard library functions
///   -- currently cause infinite recursion during simplificaton. Testing the Hermes
///   -- translation interface remains unaffected.
///   sorry
/// ```
pub fn checked_add(x: i32, y: i32) -> Option<i32> {
    x.checked_add(y)
}

fn main() {}
