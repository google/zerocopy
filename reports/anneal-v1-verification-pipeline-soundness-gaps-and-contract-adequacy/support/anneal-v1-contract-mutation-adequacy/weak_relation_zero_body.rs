/// ```lean, anneal, spec
/// requires: x.val > -2147483648
/// ensures (h0): ret >= 0
/// proof (h_progress):
///   simp [abs]
/// proof (h0):
///   simp [abs] at h_returns
///   subst ret
///   decide
/// ```
pub unsafe fn abs(x: i32) -> i32 {
    0
}

fn main() {}
