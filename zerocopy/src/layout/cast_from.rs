// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Compile-time cast planning and runtime pointer projection.
//!
//! `CastPlan` selects and applies numerical metadata transformations from two
//! layouts. `CastParams` associates a selected plan with a `KnownLayout` type
//! pair and converts their typed metadata to and from element counts. Its
//! associated constant performs selection at compile time; `CastFrom::project`
//! uses that constant to transform metadata and construct the destination
//! pointer at runtime.

use crate::*;

/// A numerical metadata transformation selected for a pair of layouts.
///
/// A raw plan contains no type or layout identity. Its parameters preserve size
/// only in relation to the layouts used by `try_compute`. `CastParams` retains
/// that connection to the `KnownLayout` pair used for pointer projection.
#[derive(Copy, Clone)]
enum CastPlan {
    // At compile time (specifically, post-monomorphization time),
    // we need to compute two things:
    // - Whether, given *any* `*Src`, it is possible to construct a
    //   `*Dst` which addresses the same number of bytes (ie,
    //   whether, for any `Src` pointer metadata, there exists `Dst`
    //   pointer metadata that addresses the same number of bytes)
    // - If this is possible, any information necessary to perform
    //   the `Src`->`Dst` metadata conversion at runtime.
    //
    // For slice DSTs, destination metadata is an affine function
    // of source metadata:
    //
    //   dst_meta = offset_delta_elems + src_meta * elem_multiple
    //
    // `elem_multiple` scales the destination's trailing element
    // size to the source's. `offset_delta_elems` selects a
    // destination size equal to the source's zero-element size.
    // We then prove that the two complete rounded size formulas
    // produce the same sequence for all metadata. This is
    // necessary because a packed outer DST can retain a nested
    // field's rounding operation; comparing only physical
    // trailing-slice offsets is not sufficient.
    /// Converts between slice DSTs using a size-preserving affine map.
    UnsizedToUnsized { offset_delta_elems: usize, elem_multiple: usize },

    /// Uses the metadata selected for a sized source and a slice DST.
    SizedToUnsized { dst_meta: usize },

    /// Converts between sized layouts with equal sizes.
    SizedToSized,
}

impl CastPlan {
    /// Given a nonzero `dst.elem_size` that exactly divides
    /// `src.elem_size`, produces `true` only when the following
    /// metadata map preserves the complete object size for every
    /// source element count `src_meta`:
    ///
    /// ```text
    /// dst_meta = dst_base + src_meta * (src.elem_size / dst.elem_size)
    /// ```
    ///
    /// This recognizes sufficient conditions for equality. A
    /// `false` result also includes equivalent size sequences
    /// that this test cannot recognize, or an adjustment whose
    /// normalized components cannot be represented in `usize`.
    ///
    /// ```aeneas
    /// spec cast_size_sequences_spec
    ///   requires(raw) positive : 0 < dst.elem_size.val
    ///   requires(raw) divides : src.elem_size.val % dst.elem_size.val = 0
    ///   ensures(raw) same => same = true → ∀ count : Nat,
    ///     (trailingFormula src).size count =
    ///       (trailingFormula dst).size (dst_base.val + count * (src.elem_size.val / dst.elem_size.val))
    /// ```
    const fn size_sequences_match(
        src: TrailingSliceLayout,
        dst: TrailingSliceLayout,
        dst_base: usize,
    ) -> bool {
        let base_bytes = match dst_base.checked_mul(dst.elem_size) {
            Some(bytes) => bytes,
            None => return false,
        };
        let shifted_dst = match dst.advance(base_bytes, src.elem_size) {
            Some(advanced) => advanced,
            None => return false,
        };
        src.has_same_size_sequence(shifted_dst)
    }

    /// Given the complete layouts of `Src` and `Dst`, produces
    /// parameters for a cast that preserves object size.
    ///
    /// A `Some` result establishes that `Src`'s alignment is at
    /// least `Dst`'s and that the metadata map preserves size for
    /// every valid source metadata value.
    ///
    /// Supports casts between sized types of equal size, from a
    /// sized type to a slice DST, and between slice DSTs. A slice
    /// DST destination must have nonzero-sized elements; between
    /// slice DSTs, its element size must exactly divide the
    /// source's nonzero element size.
    ///
    /// Produces `None` for unsupported casts or when this method
    /// cannot establish a size-preserving metadata map. Rejection
    /// does not establish that no such map exists.
    ///
    /// ```aeneas
    /// spec cast_plan_spec
    ///   ensures(raw) plan => castPlanSpec src_layout dst_layout plan
    /// ```
    const fn try_compute(src_layout: &DstLayout, dst_layout: &DstLayout) -> Option<Self> {
        if src_layout.align.get() < dst_layout.align.get() {
            return None;
        }

        let plan = match (src_layout.size_info, dst_layout.size_info) {
            (SizeInfo::Sized { size: src_size }, SizeInfo::Sized { size: dst_size }) => {
                if src_size != dst_size {
                    return None;
                }

                // SAFETY: We checked above that `src_size ==
                // dst_size`.
                CastPlan::SizedToSized
            }
            (SizeInfo::Sized { size: src_size }, SizeInfo::SliceDst(_)) => {
                let dst_meta = match dst_layout.metadata_for_exact_size(src_size) {
                    Some(meta) => meta,
                    None => return None,
                };

                // SAFETY: The preceding math ensures that a `Dst`
                // with `dst_meta` addresses `src_size` bytes.
                CastPlan::SizedToUnsized { dst_meta }
            }
            (SizeInfo::SliceDst(src), SizeInfo::SliceDst(dst)) => {
                let dst_elem_size = if let Some(e) = NonZeroUsize::new(dst.elem_size) {
                    e
                } else {
                    return None;
                };

                if src.elem_size < dst.elem_size {
                    return None;
                }

                let (elem_multiple, described_src_elem_size) =
                    super::max_elems_for_bytes(src.elem_size, dst_elem_size);
                if described_src_elem_size != src.elem_size {
                    return None;
                }

                // Prefer an exact destination-element adjustment
                // between `src.size_offset()` and
                // `dst.size_offset()`. This preserves offset-based
                // cast compatibility and metadata selection when
                // several lengths have the same rounded size. It
                // also avoids choosing a length whose subsequent
                // padding sequence differs from the source's.
                let exact_offset_delta_elems =
                    match src.size_offset().checked_sub(dst.size_offset()) {
                        Some(delta) => {
                            let (elems, described_delta) =
                                super::max_elems_for_bytes(delta, dst_elem_size);
                            if described_delta == delta {
                                Some(elems)
                            } else {
                                None
                            }
                        }
                        None => None,
                    };

                let offset_delta_elems = match exact_offset_delta_elems {
                    Some(elems) if Self::size_sequences_match(src, dst, elems) => elems,
                    _ => {
                        let src_zero_size = match src.size_for_elems(0) {
                            Some(size) => size,
                            None => return None,
                        };
                        let elems = match dst_layout.metadata_for_exact_size(src_zero_size) {
                            Some(elems) => elems,
                            None => return None,
                        };
                        if !Self::size_sequences_match(src, dst, elems) {
                            return None;
                        }
                        elems
                    }
                };

                CastPlan::UnsizedToUnsized {
                    // SAFETY: `size_sequences_match` proves that
                    // this affine metadata map preserves size.
                    offset_delta_elems,
                    // SAFETY: We checked above that this is an exact
                    // ratio of source to destination element size.
                    elem_multiple,
                }
            }
            _ => return None,
        };

        // SAFETY: We checked above that `src.align >= dst.align`.
        Some(plan)
    }

    /// Applies the numerical metadata transformation to an element count.
    ///
    /// # Safety
    ///
    /// For `UnsizedToUnsized`, neither `src_meta * elem_multiple` nor
    /// `offset_delta_elems + src_meta * elem_multiple` may overflow `usize`.
    /// The other variants impose no condition on `src_meta` and ignore it.
    #[inline(always)]
    ///
    /// ```aeneas
    /// spec cast_metadata_spec
    ///   requires(raw) fits : castMetadataFits self src_meta.val
    ///   ensures(raw) metadata => metadata.val = castPlanMetadata self src_meta.val
    /// ```
    unsafe fn cast_metadata(self, src_meta: usize) -> usize {
        match self {
            CastPlan::UnsizedToUnsized { offset_delta_elems, elem_multiple } => {
                // SAFETY: The caller provides the helper's complete
                // no-overflow precondition.
                unsafe { super::add_scaled_metadata(offset_delta_elems, src_meta, elem_multiple) }
            }
            CastPlan::SizedToUnsized { dst_meta } => dst_meta,
            CastPlan::SizedToSized => 0,
        }
    }
}

/// A selected plan associated with the layouts of `Src` and `Dst`.
///
/// The private fields are initialized only by `CAST_PARAMS`, which selects the
/// plan using `Src::LAYOUT` and `Dst::LAYOUT`. The markers retain this type-pair
/// association when the plan is applied to typed pointer metadata at runtime.
///
/// # Safety
///
/// `Src`'s alignment must not be smaller than `Dst`'s alignment.
struct CastParams<Src: ?Sized, Dst: ?Sized> {
    plan: CastPlan,
    _src: PhantomData<Src>,
    _dst: PhantomData<Dst>,
}

impl<Src: ?Sized, Dst: ?Sized> Copy for CastParams<Src, Dst> {}
impl<Src: ?Sized, Dst: ?Sized> Clone for CastParams<Src, Dst> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Src: KnownLayout + ?Sized, Dst: KnownLayout + ?Sized> CastParams<Src, Dst> {
    /// Computes the parameters at compile time, rejecting incompatible layouts
    /// with a post-monomorphization error.
    const CAST_PARAMS: Self = match CastPlan::try_compute(&Src::LAYOUT, &Dst::LAYOUT) {
        // SAFETY: `try_compute` checked that `Src::LAYOUT.align >=
        // Dst::LAYOUT.align`.
        Some(plan) => Self { plan, _src: PhantomData, _dst: PhantomData },
        None => {
            const_panic!("cannot `transmute_ref!` or `transmute_mut!` between incompatible types")
        }
    };

    /// # Safety
    ///
    /// `src_meta` describes a `Src` whose size is no larger than `isize::MAX`.
    ///
    /// The returned metadata describes a `Dst` of the same size as the original
    /// `Src`.
    #[inline(always)]
    unsafe fn cast_metadata(self, src_meta: Src::PointerMetadata) -> Dst::PointerMetadata {
        let src_meta = match self.plan {
            CastPlan::UnsizedToUnsized { .. } => src_meta.to_elem_count(),
            _ => 0,
        };

        // SAFETY: The sized variants perform no unchecked arithmetic.
        // For the affine variant, the selected plan makes the complete source
        // and destination sizes equal and has a positive destination stride.
        // Destination size is at least metadata * stride, so the complete
        // metadata sum is at most source size. The multiplication's result is
        // no larger than that sum. Both therefore fit usize, since the caller
        // bounds source size by isize::MAX. The assertions in
        // checks::assert_cast_preserves_size prove this numerical composition
        // against the independent remainder-based size calculation.
        let dst_meta = unsafe { self.plan.cast_metadata(src_meta) };
        Dst::PointerMetadata::from_elem_count(dst_meta)
    }
}

pub(crate) struct CastFrom<Dst: ?Sized> {
    _never: core::convert::Infallible,
    _marker: PhantomData<Dst>,
}

// SAFETY: The implementation of `Project::project` preserves the address
// of the referent – it only modifies pointer metadata.
unsafe impl<Src, Dst> crate::pointer::cast::Cast<Src, Dst> for CastFrom<Dst>
where
    Src: KnownLayout + ?Sized,
    Dst: KnownLayout + ?Sized,
{
}

// SAFETY: The implementation of `Project::project` preserves the size of
// the referent (see inline comments for a more detailed proof of this).
unsafe impl<Src, Dst> crate::pointer::cast::CastExact<Src, Dst> for CastFrom<Dst>
where
    Src: KnownLayout + ?Sized,
    Dst: KnownLayout + ?Sized,
{
}

// SAFETY: `project` produces a pointer which refers to the same referent
// bytes as its input, or to a subset of them (see inline comments for a
// more detailed proof of this). It does this using provenance-preserving
// operations.
unsafe impl<Src, Dst> crate::pointer::cast::Project<Src, Dst> for CastFrom<Dst>
where
    Src: KnownLayout + ?Sized,
    Dst: KnownLayout + ?Sized,
{
    /// # PME
    ///
    /// Generates a post-monomorphization error if it is not possible to
    /// implement soundly.
    //
    // FIXME(#1817): Support Sized->Unsized and Unsized->Sized casts
    fn project(src: PtrInner<'_, Src>) -> *mut Dst {
        let src_meta = <Src as KnownLayout>::pointer_to_metadata(src.as_ptr());
        let params = CastParams::<Src, Dst>::CAST_PARAMS;

        // SAFETY: `src: PtrInner` guarantees that `src`'s referent is zero
        // bytes or lives in a single allocation, which means that it is no
        // larger than `isize::MAX` bytes [1].
        //
        // [1] https://doc.rust-lang.org/1.92.0/std/ptr/index.html#allocation
        let dst_meta = unsafe { params.cast_metadata(src_meta) };

        <Dst as KnownLayout>::raw_from_ptr_len(src.as_non_null().cast(), dst_meta).as_ptr()
    }
}

// Keep the numerical proof harness next to the pointer adapter it justifies.
// The harness uses no pointers. Its assertion safety proves the size and
// arithmetic part of the adapter's safety argument; pointer construction,
// provenance, and the KnownLayout contract remain separate obligations.
#[allow(dead_code, clippy::manual_map, clippy::needless_nonzero_get)]
mod checks {
    use super::{CastPlan, DstLayout, NonZeroUsize, SizeInfo};
    use crate::layout::{tail_checks, tail_transform_checks};

    fn witness_matches(runtime_layout: DstLayout, align: NonZeroUsize, phase: usize) -> bool {
        match runtime_layout.size_info {
            SizeInfo::Sized { .. } => true,
            SizeInfo::SliceDst(tail) => tail_transform_checks::witness_matches(tail, align, phase),
        }
    }

    // This calculation uses explicit alignment/phase witnesses and the simple
    // remainder-based reference. It does not call the production size formula.
    fn reference_size(
        runtime_layout: DstLayout,
        align: NonZeroUsize,
        phase: usize,
        elems: usize,
    ) -> Option<usize> {
        match runtime_layout.size_info {
            SizeInfo::Sized { size } => Some(size),
            SizeInfo::SliceDst(tail) => tail_checks::reference_size(tail, align, phase, elems),
        }
    }

    fn checked_metadata(plan: CastPlan, src_meta: usize) -> Option<usize> {
        match plan {
            CastPlan::UnsizedToUnsized { offset_delta_elems, elem_multiple } => {
                match src_meta.checked_mul(elem_multiple) {
                    Some(scaled) => offset_delta_elems.checked_add(scaled),
                    None => None,
                }
            }
            CastPlan::SizedToUnsized { dst_meta } => Some(dst_meta),
            CastPlan::SizedToSized => Some(0),
        }
    }

    /// Every selected plan preserves the complete object size and alignment
    /// requirement. For a representable source size, its metadata arithmetic
    /// must fit, and its unchecked implementation must agree with checked
    /// arithmetic. Both source and destination sizes use the independent
    /// remainder-based reference calculation.
    ///
    /// The witness guards identify the compressed alignment/phase encoding;
    /// every valid encoding has witnesses. Rejected plans and unrepresentable
    /// source sizes impose no claim. In particular, overflow of *metadata*
    /// after an accepted plan and representable source size is an assertion
    /// failure, rather than an input exclusion.
    ///
    /// Rust objects have the stronger size bound of isize::MAX. Proving this
    /// for every size fitting usize therefore covers that numerical domain.
    /// The harness does not model pointer provenance or construct references.
    ///
    /// ```aeneas
    /// spec cast_composition_check_spec
    ///   ensures(raw) _ => True
    /// ```
    fn assert_cast_preserves_size(
        src: DstLayout,
        dst: DstLayout,
        src_rounding_align: NonZeroUsize,
        src_phase: usize,
        dst_rounding_align: NonZeroUsize,
        dst_phase: usize,
        src_meta: usize,
    ) {
        if !witness_matches(src, src_rounding_align, src_phase)
            || !witness_matches(dst, dst_rounding_align, dst_phase)
        {
            return;
        }
        let plan = match CastPlan::try_compute(&src, &dst) {
            Some(plan) => plan,
            None => return,
        };
        let src_size = match reference_size(src, src_rounding_align, src_phase, src_meta) {
            Some(size) => size,
            None => return,
        };
        assert!(src.align.get() >= dst.align.get());
        let expected_meta = match checked_metadata(plan, src_meta) {
            Some(meta) => meta,
            None => panic!("selected cast metadata overflowed"),
        };
        // SAFETY: The preceding checked calculation establishes that both
        // the multiplication and addition required by cast_metadata fit.
        let dst_meta = unsafe { plan.cast_metadata(src_meta) };
        assert!(dst_meta == expected_meta);
        assert!(tail_checks::same_optional_usize(
            reference_size(dst, dst_rounding_align, dst_phase, dst_meta),
            Some(src_size),
        ));
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::layout::{RoundingAlignAndPhase, TrailingSliceLayout};

        #[test]
        fn selected_cast_composition() {
            let one = NonZeroUsize::new(1).unwrap();
            let four = NonZeroUsize::new(4).unwrap();
            let sized = DstLayout {
                align: four,
                size_info: SizeInfo::Sized { size: 12 },
                statically_shallow_unpadded: false,
            };
            let dst = DstLayout {
                align: four,
                statically_shallow_unpadded: false,
                size_info: SizeInfo::SliceDst(TrailingSliceLayout {
                    offset: 0,
                    elem_size: 4,
                    size_base: 0,
                    size_rounding_align_and_phase: RoundingAlignAndPhase::new(four, 2),
                }),
            };
            let src = DstLayout {
                align: four,
                statically_shallow_unpadded: false,
                size_info: SizeInfo::SliceDst(TrailingSliceLayout {
                    // Physical offsets deliberately differ from size bases.
                    // Cast planning must compare complete rounded sizes.
                    offset: 3,
                    elem_size: 8,
                    size_base: 8,
                    size_rounding_align_and_phase: RoundingAlignAndPhase::new(four, 2),
                }),
            };
            assert!(CastPlan::try_compute(&sized, &sized).is_some());
            assert!(CastPlan::try_compute(&sized, &dst).is_some());
            assert!(CastPlan::try_compute(&src, &dst).is_some());
            for count in [0, 1, 7, usize::MAX / 16, usize::MAX].iter().copied() {
                // Sized witnesses are ignored, including their phase.
                assert_cast_preserves_size(sized, sized, one, 0, one, 0, count);
                assert_cast_preserves_size(sized, dst, one, 0, four, 2, count);
                assert_cast_preserves_size(src, dst, four, 2, four, 2, count);
            }
        }
    }
}
