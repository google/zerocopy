/// ```lean, hermes
/// isValid self := Hermes.Alignment self.align.val
/// ```
pub struct DstLayout {
    pub align: usize,
    pub size_info: SizeInfo,
}

pub enum SizeInfo {
    Sized { size: usize },
    ReprCSliceDst(TrailingSliceLayout),
}

#[derive(Copy, Clone)]
pub struct TrailingSliceLayout {
    pub offset: usize,
    pub elem_size: usize,
}

// TODO: Add `isSafe` that constrains this to be equal to `Self`'s layout.
// Self is either Sized or a repr(C) slice DST.
/// ```lean, hermes
/// isSafe : 
///   ∀ (val : Aeneas.Std.ConstRawPtr Self) [Hermes.SliceDstTypeLayout Self] (inst : KnownLayout Self), 
///     inst.pointer_to_metadata val = Result.ok (Hermes.raw_slice_dst_ptr_metadata val)
/// ```
pub unsafe trait KnownLayout {
    const LAYOUT: DstLayout;

    // TODO: Add `isSafe` that constrains this so that, if `Self` is a repr(C)
    // slice DST, this returns `val`'s actual pointer metadata.
    fn pointer_to_metadata(val: *const Self) -> usize;
}

// TODO: `ensures` that the result is correct and change this from `unsafe(axiom)` to
// `spec`.
/// ```lean, hermes, unsafe(axiom)
/// requires ∃ a : Hermes.Allocation, Hermes.FitsInAllocation (Hermes.raw_ptr_referent val) a
/// ```
pub unsafe fn size_of_val<T: ?Sized + KnownLayout>(val: *const T) -> usize {
    let metadata_val = T::pointer_to_metadata(val);

    let align = T::LAYOUT.align;
    match T::LAYOUT.size_info {
        SizeInfo::Sized { size } => size,
        SizeInfo::ReprCSliceDst(TrailingSliceLayout { offset, elem_size }) => {
            let unpadded_size = offset + elem_size * metadata_val;
            ((unpadded_size + align - 1) / align) * align
        }
    }
}
