/// ```hermes, unsafe(axiom)
/// requires [Hermes.ReprC T]
/// requires [Hermes.SpecSliceDstTypeLayout T]
/// requires [Hermes.TrailingSlice T]
/// ensures ret.val = (Hermes.HasSpecLayout.layout val.v).size
/// ensures Hermes.IsValid.isValid ret
/// ```
#[allow(unused_variables)]
pub const unsafe fn size_of_val_raw<T: ?Sized>(val: *const T) -> usize {
    0
}

/// ```hermes, unsafe(axiom)
/// requires [Hermes.SpecSliceDstTypeLayout T]
/// requires [Hermes.TrailingSlice T]
/// ensures ret.val = (Hermes.SpecSliceDstTypeLayout.layout T).align.val
/// ensures Hermes.IsValid.isValid ret
/// ```
#[allow(unused_variables)]
pub const unsafe fn align_of_val_raw<T: ?Sized>(val: *const T) -> usize {
    0
}

/// ```hermes
/// ensures Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_slice
///   progress with raw_ptr_dst_layout.size_of_val_raw.spec as ⟨ i, h_size ⟩
///   progress with raw_ptr_dst_layout.align_of_val_raw.spec as ⟨ i1, h_align ⟩
///   simp_all
///   exact ⟨trivial, (Hermes.HasSpecLayout.layout slice.v).sizeAligned⟩
/// ```
pub fn test_slice(slice: *const [u8]) -> (usize, usize) {
    unsafe { (size_of_val_raw(slice), align_of_val_raw(slice)) }
}
