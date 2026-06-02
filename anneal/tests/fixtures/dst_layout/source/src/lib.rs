/// ```lean, anneal
/// def isValid (self : DstLayout) : Prop := Anneal.IsAlignment self.align.val
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
/// ```lean, anneal
/// def isSafe {Self : Type} (inst : KnownLayout Self) : Prop :=
///   (∃ (_sz : Anneal.core.marker.Sized Self) (tl : Anneal.HasStaticLayout Self),
///     inst.LAYOUT.align = tl.layout.align.val ∧
///     inst.LAYOUT.size_info = dst_layout.SizeInfo.Sized tl.layout.size) ∨
///   (∃ (_rc : Anneal.ReprC Self) (sl : Anneal.SpecSliceDstTypeLayout Self) 
///       (_md : Anneal.HasMetadata (Aeneas.Std.RawPtr Self Aeneas.Std.Mutability.Const) Aeneas.Std.Usize)
///       (offset : Aeneas.Std.Usize) (elemSize : Aeneas.Std.Usize),
///     inst.LAYOUT.align.val = sl.layout.align.val.val ∧
///     inst.LAYOUT.size_info = dst_layout.SizeInfo.ReprCSliceDst { offset := offset, elem_size := elemSize } ∧
///     offset.val = sl.layout.trailingOffset ∧
///     elemSize.val = sl.layout.elementSize ∧
///     (∀ val, _md.metadata val = Anneal.raw_slice_dst_ptr_metadata val) ∧
///     ∀ val, inst.pointer_to_metadata val = Result.ok (Anneal.raw_slice_dst_ptr_metadata val))
/// ```
pub unsafe trait KnownLayout {
    const LAYOUT: DstLayout;

    fn pointer_to_metadata(val: *const Self) -> usize;
}

/// ```lean, anneal, spec
/// theorem spec {T : Type} [KnownLayoutInst : KnownLayout T] (val : *const T)
///   (valid_alloc : ∃ a : Anneal.Allocation, Anneal.FitsInAllocation (Anneal.raw_ptr_referent val) a)
///   (is_safe : KnownLayout.isSafe T) :
///   Aeneas.Std.WP.spec (size_of_val val) (fun ret_ => ret_.val = (Anneal.raw_ptr_referent val).size.val) := by
///   sorry
/// ```
pub unsafe fn size_of_val<T: ?Sized + KnownLayout>(val: *const T) -> usize {
    let align = T::LAYOUT.align;
    match T::LAYOUT.size_info {
        SizeInfo::Sized { size } => size,
        SizeInfo::ReprCSliceDst(TrailingSliceLayout { offset, elem_size }) => {
            let metadata_val = T::pointer_to_metadata(val);
            let unpadded_size = offset + elem_size * metadata_val;
            ((unpadded_size + align - 1) / align) * align
        }
    }
}
