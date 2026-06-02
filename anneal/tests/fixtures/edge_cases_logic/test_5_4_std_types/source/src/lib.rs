
/// ```lean, anneal, spec
/// theorem spec (v : Vec Std.U32) (s : String) :
///   Aeneas.Std.WP.spec (std_types v s) (fun ret_ => True) := by
///   sorry
/// ```
pub fn std_types(v: Vec<u32>, s: String) {
    let _ = v.len();
    let _ = s.len();
}
