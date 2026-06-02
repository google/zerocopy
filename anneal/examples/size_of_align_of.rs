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
///   rcases h_req with ⟨_sz, tl, _⟩
///   unfold silly_size_of
///   have h_align_pos : 0 < (Anneal.HasStaticLayout.layout T).align.val.val := (Anneal.HasStaticLayout.layout T).align.isValid.left
///   have h_align_nz : (Anneal.HasStaticLayout.layout T).align.val.val ≠ 0 := by omega
///   simp_all
///   step
///   step
///   · rw [i_post]
///     simp
///   · rw [i_post] at r_post
///     simp at r_post
///     exact r_post
/// ```
pub unsafe fn silly_size_of<T>(_val: *const T) -> usize {
    let size = core::mem::size_of::<T>();
    let align = core::mem::align_of::<T>();
    (size / align) * align
}

fn main() {}
