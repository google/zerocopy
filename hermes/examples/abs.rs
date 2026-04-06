/// Computes the absolute value.
///
/// ```lean, hermes, spec
/// requires: x.val > -2147483648
/// ensures (h0): ret >= 0
/// ensures (h1): (x : Int) >= 0 -> (ret : Int) = x
/// ensures (h2): (x : Int) < 0 -> (ret : Int) = -x
/// proof (h_progress):
///   unfold abs
///   split <;> intros <;> (try cases h_req) <;> (try have := Aeneas.Std.IScalar.hmin x) <;> (try have := Aeneas.Std.IScalar.hmax x) <;> (try have : (↑(0 : I32) : Int) = 0 := by rfl) <;> (try have h_bound := Aeneas.Std.IScalar.tryMk_eq IScalarTy.I32 (-↑x)) <;> (try split at h_bound) <;> (try simp_all [HNeg.hNeg, Aeneas.Std.IScalar.neg, Aeneas.Std.IScalar.inBounds]) <;> scalar_tac
/// proof (h0):
///   unfold abs at h_returns
///   split at h_returns <;> intros <;> (try cases h_req) <;> (try have := Aeneas.Std.IScalar.hmin x) <;> (try have := Aeneas.Std.IScalar.hmax x) <;> (try have : (↑(0 : I32) : Int) = 0 := by rfl) <;> (try have h_bound := Aeneas.Std.IScalar.tryMk_eq IScalarTy.I32 (-↑x)) <;> (try split at h_bound) <;> (try simp_all [HNeg.hNeg, Aeneas.Std.IScalar.neg, Aeneas.Std.IScalar.inBounds]) <;> scalar_tac
/// proof (h1):
///   unfold abs at h_returns
///   split at h_returns <;> intros <;> (try cases h_req) <;> (try have := Aeneas.Std.IScalar.hmin x) <;> (try have := Aeneas.Std.IScalar.hmax x) <;> (try have : (↑(0 : I32) : Int) = 0 := by rfl) <;> (try have h_bound := Aeneas.Std.IScalar.tryMk_eq IScalarTy.I32 (-↑x)) <;> (try split at h_bound) <;> (try simp_all [HNeg.hNeg, Aeneas.Std.IScalar.neg, Aeneas.Std.IScalar.inBounds]) <;> scalar_tac
/// proof (h2):
///   unfold abs at h_returns
///   split at h_returns <;> intros <;> (try cases h_req) <;> (try have := Aeneas.Std.IScalar.hmin x) <;> (try have := Aeneas.Std.IScalar.hmax x) <;> (try have : (↑(0 : I32) : Int) = 0 := by rfl) <;> (try have h_bound := Aeneas.Std.IScalar.tryMk_eq IScalarTy.I32 (-↑x)) <;> (try split at h_bound) <;> (try simp_all [HNeg.hNeg, Aeneas.Std.IScalar.neg, Aeneas.Std.IScalar.inBounds]) <;> scalar_tac
/// ```
pub unsafe fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

fn main() {}
