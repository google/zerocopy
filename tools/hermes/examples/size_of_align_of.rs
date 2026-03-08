/// ```hermes
/// ensures: ret.val = 0
/// proof:
///   unfold get_size_of_empty_tuple
///   simp
/// ```
pub fn get_size_of_empty_tuple() -> usize {
    core::mem::size_of::<()>()
}

/// ```hermes
/// ensures: ret.val = 1
/// proof:
///   unfold get_align_of_empty_tuple
///   simp
/// ```
pub fn get_align_of_empty_tuple() -> usize {
    core::mem::align_of::<()>()
}

/// ```hermes
/// requires: ∃ (_sz : Hermes.core.marker.Sized T) (tl : Hermes.HasStaticLayout T), True
/// ensures: match core.mem.size_of T with
///   | Result.ok size => ret.val = size.val
///   | _ => False
/// proof:
///   rcases h_req with ⟨_sz, tl, _⟩
///   unfold silly_size_of
///   simp_all
///   have h_align_pos : 0 < tl.layout.align.val.val := tl.layout.align.isValid.left
///   have h_align_nz : tl.layout.align.val.val ≠ 0 := by omega
///   repeat (progress <;> try omega)
///   simp_all
/// ```
pub unsafe fn silly_size_of<T>(_val: *const T) -> usize {
    let size = core::mem::size_of::<T>();
    let align = core::mem::align_of::<T>();
    (size / align) * align
}

fn main() {}
