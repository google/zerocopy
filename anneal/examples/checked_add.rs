/// Performs checked addition.
///
/// ```lean, anneal, spec
/// theorem spec (x y : Std.I32) :
///   Aeneas.Std.WP.spec (checked_add x y) (fun ret_ =>
///     match ret_ with
///     | .none => (x : Int) + (y : Int) > I32.max ∨ (x : Int) + (y : Int) < I32.min
///     | .some v => (v : Int) = (x : Int) + (y : Int)) := by
///   unfold checked_add
///   simp_all [Aeneas.Std.I32.checked_add]
///   have h := Aeneas.Std.I32.checked_add_bv_spec x y
///   split <;> split at h <;> simp_all <;> scalar_tac
/// ```
pub fn checked_add(x: i32, y: i32) -> Option<i32> {
    x.checked_add(y)
}

fn main() {}
