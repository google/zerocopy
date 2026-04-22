/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (get_size_of_empty_tuple) (fun ret_ => ret_.val = 0) := by
///   unfold get_size_of_empty_tuple
///   simp_all
/// ```
pub fn get_size_of_empty_tuple() -> usize {
    core::mem::size_of::<()>()
}

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (get_align_of_empty_tuple) (fun ret_ => ret_.val = 1) := by
///   unfold get_align_of_empty_tuple
///   simp_all
/// ```
pub fn get_align_of_empty_tuple() -> usize {
    core::mem::align_of::<()>()
}

fn main() {}
