/// Sets `acc` to `val` if `val` is larger.
///
/// ```lean, anneal, spec
/// theorem spec (acc : Std.U32) (val : Std.U32) :
///   Aeneas.Std.WP.spec (update_max acc val) (fun ret_ =>
///     ret_ = if val > acc then val else acc) := by
///   unfold update_max
///   split <;> simp_all
/// ```
pub fn update_max(acc: &mut u32, val: u32) {
    if val > *acc {
        *acc = val;
    }
}

fn main() {}
