
/// ```lean, anneal, spec
/// theorem spec (v : Vec Std.U32) :
///   Aeneas.Std.WP.spec (pop v) (fun ret_ => True) := by
///   sorry
/// ```
pub fn pop(v: &mut Vec<u32>) -> Option<u32> {
    v.pop()
}

pub fn inc(x: &mut u32) {
    *x += 1;
}
