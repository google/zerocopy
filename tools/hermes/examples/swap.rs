/// Swaps two values.
///
/// ```lean, hermes, spec
/// ensures x' = y
/// ensures y' = x
/// proof
///   unfold swap
///   simp_all
/// ```
pub fn swap(x: &mut u32, y: &mut u32) {
    let tmp = *x;
    *x = *y;
    *y = tmp;
}

fn main() {}
