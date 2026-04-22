/// ```lean, anneal, spec
/// theorem spec (x : _) (y : _) (z : _) :
///   Aeneas.Std.WP.spec (nested x y z) (fun ret_ => True) := by
///   sorry
/// ```
pub fn nested(x: &&u32, y: &mut &u32, z: &&mut u32) {
    let _ = **x;
    let _ = **y;
    let _ = **z;
}
