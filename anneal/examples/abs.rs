/// Computes the absolute value.
///
/// ```lean, anneal, spec
/// theorem spec (x : Std.I32) (h_req : x.val > -2147483648) :
///   Aeneas.Std.WP.spec (abs x) (fun ret_ =>
///     (ret_ : Int) ≥ 0 ∧
///     ((x : Int) ≥ 0 → (ret_ : Int) = x) ∧
///     ((x : Int) < 0 → (ret_ : Int) = -x)) := by
///   unfold abs
///   split <;> intros <;> (try cases h_req) <;> (try have := Aeneas.Std.IScalar.hmin x) <;> (try have := Aeneas.Std.IScalar.hmax x) <;> (try have : (↑(0 : I32) : Int) = 0 := by rfl) <;> (try have h_bound := Aeneas.Std.IScalar.tryMk_eq IScalarTy.I32 (-↑x)) <;> (try split at h_bound) <;> (try simp_all [HNeg.hNeg, Aeneas.Std.IScalar.neg, Aeneas.Std.IScalar.inBounds]) <;> scalar_tac
/// ```
pub unsafe fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

fn main() {}
