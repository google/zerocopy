/// Swaps two values.
///
/// ```lean, hermes, spec
/// ensures(h_x'_eq_y): x' = y
/// ensures(h_y'_eq_x): y' = x
/// proof(h_x'_eq_y):
///   unfold swap at h_returns
///   simp_all
/// proof(h_y'_eq_x):
///   unfold swap at h_returns
///   simp_all
/// proof (h_progress):
///   unfold swap
///   simp_all
/// ```
#[allow(clippy::manual_swap)]
pub fn swap(x: &mut u32, y: &mut u32) {
    let tmp = *x;
    *x = *y;
    *y = tmp;
}

fn main() {}
