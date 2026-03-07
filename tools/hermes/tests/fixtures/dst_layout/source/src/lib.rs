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
///   (∃ (_sz : Hermes.core.marker.Sized Self) (tl : Hermes.HasStaticLayout Self),
///     inst.LAYOUT.align = tl.layout.align.val ∧
///     inst.LAYOUT.size_info = dst_layout.SizeInfo.Sized tl.layout.size) ∨
///   (∃ (_rc : Hermes.ReprC Self) (sl : Hermes.SpecSliceDstTypeLayout Self) 
///       (_md : Hermes.HasMetadata (Aeneas.Std.RawPtr Self Aeneas.Std.Mutability.Const) Aeneas.Std.Usize)
///       (offset : Aeneas.Std.Usize) (elemSize : Aeneas.Std.Usize),
///     inst.LAYOUT.align.val = sl.layout.align.val.val ∧
///     inst.LAYOUT.size_info = dst_layout.SizeInfo.ReprCSliceDst { offset := offset, elem_size := elemSize } ∧
///     offset.val = sl.layout.trailingOffset ∧
///     elemSize.val = sl.layout.elementSize ∧
///     (∀ val, _md.metadata val = Hermes.raw_slice_dst_ptr_metadata val) ∧
///     ∀ val, inst.pointer_to_metadata val = Result.ok (Hermes.raw_slice_dst_ptr_metadata val))
/// ```
pub unsafe trait KnownLayout {
    const LAYOUT: DstLayout;

    fn pointer_to_metadata(val: *const Self) -> usize;
}

/// ```lean, hermes, spec
/// requires (valid_alloc): ∃ a : Hermes.Allocation, Hermes.FitsInAllocation (Hermes.raw_ptr_referent val) a
/// requires (is_safe): KnownLayout.Safe T KnownLayoutInst
/// ensures (h_size): ret.val = (Hermes.raw_ptr_referent val).size.val
/// proof context:
///   unfold size_of_val
///   have h_safe := is_safe.isSafe
///   rcases h_safe with ⟨_sz, _tl, h_align, h_size⟩ | ⟨_rc, _sl, inst_md, offset, elemSize, h_props⟩
///   · have h_ref_eq := @Hermes.referent_size_sized T _sz _tl Aeneas.Std.Mutability.Const val
///     simp_all
///     constructor
///     next => verify_is_valid h_ret_is_valid
///     next => simp_all
///   rcases h_props with ⟨h_align, h_size, h_offset, h_elem, h_md_eq, h_meta⟩
///   rw [h_size]
///   rw [h_meta val]
///   rcases valid_alloc with ⟨alloc, h_fits⟩
///   dsimp [Hermes.FitsInAllocation] at h_fits
///   rcases h_fits with ⟨h_referent_size, h_a_size⟩
///   have h_align_pos : 0 < KnownLayoutInst.LAYOUT.align.val := by rw [h_align]; exact _sl.layout.align.isValid.left
///   have h_ge := Hermes.roundUpToAlign_ge (offset.val + elemSize.val * (Hermes.raw_slice_dst_ptr_metadata val).val) KnownLayoutInst.LAYOUT.align.val h_align_pos
///   have h_alloc_max := alloc.base_add_size_le_usize_max
///   have h_overflow := @Hermes.slice_dst_padding_no_overflow T _rc _sl Aeneas.Std.Mutability.Const val
///   have h_bound : offset.val + elemSize.val * (Hermes.raw_slice_dst_ptr_metadata val).val + KnownLayoutInst.LAYOUT.align.val - 1 ≤ Aeneas.Std.Usize.max := by rw [h_offset, h_elem, h_align]; omega
///   have h_bound2 : 1 ≤ offset.val + elemSize.val * (Hermes.raw_slice_dst_ptr_metadata val).val + KnownLayoutInst.LAYOUT.align.val := by rw [h_offset, h_elem, h_align]; omega
///   have h_div := Nat.div_add_mod (offset.val + elemSize.val * (Hermes.raw_slice_dst_ptr_metadata val).val + KnownLayoutInst.LAYOUT.align.val - 1) KnownLayoutInst.LAYOUT.align.val
///   have h_mul_comm := Nat.mul_comm KnownLayoutInst.LAYOUT.align.val ((offset.val + elemSize.val * (Hermes.raw_slice_dst_ptr_metadata val).val + KnownLayoutInst.LAYOUT.align.val - 1) / KnownLayoutInst.LAYOUT.align.val)
///   repeat (progress <;> try omega)
///   have h_ref_eq := @Hermes.referent_size_slice_dst T _rc _sl Aeneas.Std.Mutability.Const alloc inst_md val ⟨h_referent_size, h_a_size⟩
/// proof (h_size):
///   simp_all [Hermes.roundUpToAlign, Hermes.reprCSliceDstSize, Nat.mul_comm]
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
