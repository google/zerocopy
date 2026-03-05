/// ```lean, hermes
/// isValid self := Hermes.IsAlignment self.align.val
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

// Self is either Sized or a repr(C) slice DST.
/// ```lean, hermes
/// isSafe : 
///   (∀ [Hermes.core.marker.Sized Self] [Hermes.HasStaticLayout Self],
///     inst.LAYOUT.align = (Hermes.HasStaticLayout.layout (α := Self)).align.val ∧
///     inst.LAYOUT.size_info = dst_layout.SizeInfo.Sized (Hermes.HasStaticLayout.layout (α := Self)).size) ∧
///   (∀ [Hermes.SpecSliceDstTypeLayout Self],
///     inst.LAYOUT.align.val = (Hermes.SpecSliceDstTypeLayout.layout (α := Self)).align.val.val ∧
///     ∃ offset elemSize,
///       inst.LAYOUT.size_info = dst_layout.SizeInfo.ReprCSliceDst { offset := offset, elem_size := elemSize } ∧
///       offset.val = (Hermes.SpecSliceDstTypeLayout.layout (α := Self)).trailingOffset ∧
///       elemSize.val = (Hermes.SpecSliceDstTypeLayout.layout (α := Self)).elementSize ∧
///       ∀ val, inst.pointer_to_metadata val = Result.ok (Hermes.raw_slice_dst_ptr_metadata val))
/// ```
pub unsafe trait KnownLayout {
    const LAYOUT: DstLayout;

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
