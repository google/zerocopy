/// ```hermes, unsafe(axiom)
/// requires (h_reprc): [Hermes.ReprC T]
/// requires (h_layout): [Hermes.SpecSliceDstTypeLayout T]
/// requires (h_trail): [Hermes.TrailingSlice T]
/// ensures (h_size): ret.val = (Hermes.HasSpecLayout.layout val.v).size
/// ensures (h_valid): Hermes.IsValid.isValid ret
/// ```
#[allow(unused_variables)]
pub const unsafe fn size_of_val_raw<T: ?Sized>(val: *const T) -> usize {
    0
}

/// ```hermes, unsafe(axiom)
/// requires (h_layout): [Hermes.SpecSliceDstTypeLayout T]
/// requires (h_trail): [Hermes.TrailingSlice T]
/// ensures (h_align): ret.val = (Hermes.SpecSliceDstTypeLayout.layout T).align.val
/// ensures (h_valid): Hermes.IsValid.isValid ret
/// ```
#[allow(unused_variables)]
pub const unsafe fn align_of_val_raw<T: ?Sized>(val: *const T) -> usize {
    0
}

/// ```hermes
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   unfold test_slice at *
///   progress with raw_ptr_dst_layout.size_of_val_raw.spec as ⟨ i, i_post ⟩
///   · exact {}
///   progress with raw_ptr_dst_layout.align_of_val_raw.spec as ⟨ i1, i1_post ⟩
///   · exact {}
///   simp_all
/// proof context:
///   have h_foo : True := True.intro
/// proof (h_align_div):
///   unfold test_slice at h_ret_
///   progress with raw_ptr_dst_layout.size_of_val_raw.spec as ⟨ i, i_post ⟩
///   · exact {}
///   progress with raw_ptr_dst_layout.align_of_val_raw.spec as ⟨ i1, i1_post ⟩
///   · exact {}
///   have h_size := i_post.h_size
///   have h_align := i1_post.h_align
///   simp_all
///   exact (Hermes.HasSpecLayout.layout slice.v).sizeAligned
/// ```
pub fn test_slice(slice: *const [u8]) -> (usize, usize) {
    unsafe { (size_of_val_raw(slice), align_of_val_raw(slice)) }
}
