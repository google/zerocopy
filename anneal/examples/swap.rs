/// Swaps two values.
///
/// ```lean, anneal, spec
/// theorem spec (x y : Std.U32) :
///   Aeneas.Std.WP.spec (swap x y) (fun ret_ =>
///     let (x', y') := ret_
///     x' = y ∧ y' = x) := by
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
