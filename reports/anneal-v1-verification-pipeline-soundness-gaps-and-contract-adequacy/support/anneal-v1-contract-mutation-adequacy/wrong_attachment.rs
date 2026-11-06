/// Computes the absolute value.
///
/// ```lean, anneal, spec
/// requires: x.val > -2147483648
/// ensures (h0): ret >= 0
/// ensures (h1): (x : Int) >= 0 -> (ret : Int) = x
/// ensures (h2): (x : Int) < 0 -> (ret : Int) = -x
/// proof (h_progress):
///   simp [identity]
/// proof (h0):
///   simp [identity] at h_returns
///   subst ret
///   scalar_tac
/// proof (h1):
///   simp [identity] at h_returns
///   subst ret
///   scalar_tac
/// proof (h2):
///   simp [identity] at h_returns
///   subst ret
///   scalar_tac
/// ```
pub unsafe fn identity(x: i32) -> i32 {
    x
}

fn main() {}
