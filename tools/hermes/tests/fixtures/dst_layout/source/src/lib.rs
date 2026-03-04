#[derive(Copy, Clone)]
pub struct DstLayout {
    pub align: usize,
    pub size_info: SizeInfo,
    pub statically_shallow_unpadded: bool,
}

#[derive(Copy, Clone)]
pub enum SizeInfo<E = usize> {
    Sized { size: usize },
    SliceDst(TrailingSliceLayout<E>),
}

#[derive(Copy, Clone)]
pub struct TrailingSliceLayout<E = usize> {
    pub offset: usize,
    pub elem_size: E,
}

// Hermes representation of DstLayout size computation.
/// ```hermes
/// ensures ret.val = match layout.size_info with
///   | .Sized size => size.val
///   | .SliceDst l => (l.offset.val + l.elem_size.val * elems.val)
/// proof
///   sorry
/// ```
#[allow(unused)]
pub const fn compute_size(layout: DstLayout, elems: usize) -> usize {
    match layout.size_info {
        SizeInfo::Sized { size } => size,
        SizeInfo::SliceDst(TrailingSliceLayout { offset, elem_size }) => offset + elem_size * elems,
    }
}

/// ```hermes
/// isSafe : 
///   Nonempty (Hermes.ValueLayout Self) ∧
///   (∀ (vl : Hermes.ValueLayout Self) (val : Self),
///     (vl.layout val).align = inst.LAYOUT.align.val)
/// ```
pub unsafe trait KnownLayout {
    const LAYOUT: DstLayout;
    
    // Using a simplified `*const` passing style for pointer metadata retrieval
    // like `[T]`'s implementation of pointer_to_metadata.
    fn pointer_to_metadata(val: *const Self) -> usize;
}

/// ```hermes
/// context
///   noncomputable def value_layout_of_KnownLayout {T} (inst: KnownLayout T) (safe: KnownLayout.Safe T inst) : Hermes.ValueLayout T :=
///     Classical.choice safe.isSafe.left
///
/// ensures
///   -- Note: we use `sorry` here because proving actual layout resolution
///   -- logic is beyond the current scope of `dst_layout` minimal example.
///   ret = Aeneas.Std.Usize.ofNatCore (Hermes.SizedTypeLayout.layout (α := Aeneas.Std.U8)).size (by sorry)
/// ```
#[allow(unused_variables)]
pub unsafe fn size_of_val<T: ?Sized + KnownLayout>(val: *const T) -> usize {
    compute_size(T::LAYOUT, T::pointer_to_metadata(val))
}
