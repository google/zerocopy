/// Computes the absolute value.
///
/// ```lean, hermes, spec
/// requires: x.val > -2147483648
/// ensures (h0): ret >= 0
/// ensures (h1): (x : Int) >= 0 -> (ret : Int) = x
/// ensures (h2): (x : Int) < 0 -> (ret : Int) = -x
/// proof (h_progress):
///   unfold abs
///   cases h_req
///   have : (↑(0 : I32) : Int) = 0 := by rfl
///   have := Aeneas.Std.IScalar.hmin x
///   have := Aeneas.Std.IScalar.hmax x
///   split
///   · have h_bound := Aeneas.Std.IScalar.tryMk_eq IScalarTy.I32 (-↑x)
///     split at h_bound <;> (try simp_all [HNeg.hNeg, Aeneas.Std.IScalar.neg]); (try scalar_tac)
///   · simp_all
/// proof (h0):
///   unfold abs at h_returns
///   have : (↑(0 : I32) : Int) = 0 := by rfl
///   have := Aeneas.Std.IScalar.hmin x
///   have := Aeneas.Std.IScalar.hmax x
///   split at h_returns
///   · have h_bound := Aeneas.Std.IScalar.tryMk_eq IScalarTy.I32 (-↑x)
///     split at h_bound <;> (try simp_all [HNeg.hNeg, Aeneas.Std.IScalar.neg]); (try scalar_tac)
///   · simp_all
/// proof (h1):
///   unfold abs at h_returns
///   have : (↑(0 : I32) : Int) = 0 := by rfl
///   split at h_returns <;> simp_all
/// proof (h2):
///   unfold abs at h_returns
///   have : (↑(0 : I32) : Int) = 0 := by rfl
///   have := Aeneas.Std.IScalar.hmin x
///   have := Aeneas.Std.IScalar.hmax x
///   split at h_returns
///   · have h_bound := Aeneas.Std.IScalar.tryMk_eq IScalarTy.I32 (-↑x)
///     split at h_bound <;> (try simp_all [HNeg.hNeg, Aeneas.Std.IScalar.neg])
///   · simp_all
/// ```
pub unsafe fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

fn main() {}
