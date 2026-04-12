/// Performs checked addition.
///
/// ```lean, anneal, spec
/// ensures: match ret with
///   | .none => (x : Int) + (y : Int) > I32.max ∨ (x : Int) + (y : Int) < I32.min
///   | .some v => (v : Int) = (x : Int) + (y : Int)
/// proof (h_anon):
///   unfold checked_add at h_returns
///   have h := Aeneas.Std.I32.checked_add_bv_spec x y
///   simp_all [Aeneas.Std.I32.checked_add]
///   cases ret <;> simp_all <;> scalar_tac
/// proof (h_progress):
///   unfold checked_add
///   simp_all
/// ```
pub fn checked_add(x: i32, y: i32) -> Option<i32> {
    x.checked_add(y)
}

fn main() {}
