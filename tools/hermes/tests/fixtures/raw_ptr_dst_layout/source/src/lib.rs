/// ```hermes, unsafe(axiom)
/// requires [Hermes.ReprC T]
/// requires [Hermes.SliceDstTypeLayout T]
/// requires [Hermes.TrailingSlice T]
/// ensures result.val = (Hermes.ValueLayout.layout val.v).size
/// ```
#[allow(unused_variables)]
pub const unsafe fn size_of_val_raw<T: ?Sized>(val: *const T) -> usize {
    0
}

/// ```hermes, unsafe(axiom)
/// requires [Hermes.SliceDstTypeLayout T]
/// requires [Hermes.TrailingSlice T]
/// ensures result.val = (Hermes.SliceDstTypeLayout.layout (α := T)).align
/// ```
#[allow(unused_variables)]
pub const unsafe fn align_of_val_raw<T: ?Sized>(val: *const T) -> usize {
    0
}

/// ```hermes
/// ensures Hermes.Alignment result.2.val /\ result.2.val ∣ result.1.val
/// proof
///   unfold test_slice
///   progress with raw_ptr_dst_layout.size_of_val_raw.spec as ⟨ i, h_size ⟩
///   progress with raw_ptr_dst_layout.align_of_val_raw.spec as ⟨ i1, h_align ⟩
///   simp_all
///   exact ⟨(Hermes.SliceDstTypeLayout.layout (α := Slice Std.U8)).validAlignment, (Hermes.ValueLayout.layout slice.v).sizeAligned⟩
/// ```
pub fn test_slice(slice: *const [u8]) -> (usize, usize) {
    unsafe { (size_of_val_raw(slice), align_of_val_raw(slice)) }
}
