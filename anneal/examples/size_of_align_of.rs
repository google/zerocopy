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

/// ```lean, anneal, spec
/// theorem spec {T : Type} (_val : ConstRawPtr T)
///   (h_req : ∃ (_sz : Anneal.core.marker.Sized T) (tl : Anneal.HasStaticLayout T), True) :
///   Aeneas.Std.WP.spec (silly_size_of _val) (fun ret_ =>
///     match core.mem.size_of T with
///     | Result.ok size => ret_.val = size.val
///     | _ => False) := by
///   sorry
/// ```
pub unsafe fn silly_size_of<T>(_val: *const T) -> usize {
    let size = core::mem::size_of::<T>();
    let align = core::mem::align_of::<T>();
    (size / align) * align
}

fn main() {}
