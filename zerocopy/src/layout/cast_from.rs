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
/// A raw plan contains no type or layout identity. Its parameters describe the
/// offset/element-size equation below only in relation to the layouts used by
/// `try_compute`; an arbitrary plan is not a witness for a `KnownLayout` pair.
/// `CastParams` carries that association for pointer projection.
#[derive(Copy, Clone)]
enum CastPlan {
    // Assume that `Src` and `Dst` are slice DSTs, and define:
    // - `S_OFF = Src::LAYOUT.size_info.offset`
    // - `S_ELEM = Src::LAYOUT.size_info.elem_size`
    // - `D_OFF = Dst::LAYOUT.size_info.offset`
    // - `D_ELEM = Dst::LAYOUT.size_info.elem_size`
    //
    // We are trying to solve the following equation:
    //
    //   D_OFF + d_meta * D_ELEM = S_OFF + s_meta * S_ELEM
    //
    // At runtime, we will be attempting to compute `d_meta`, given
    // `s_meta` (a runtime value) and all other parameters (which
    // are compile-time values). We can solve like so:
    //
    //   D_OFF + d_meta * D_ELEM = S_OFF + s_meta * S_ELEM
    //
    //   d_meta * D_ELEM = S_OFF - D_OFF + s_meta * S_ELEM
    //
    //   d_meta = (S_OFF - D_OFF + s_meta * S_ELEM)/D_ELEM
    //
    // Since `d_meta` will be a `usize`, we need the right-hand side
    // to be an integer, and this needs to hold for *any* value of
    // `s_meta` (in order for our conversion to be infallible - ie,
    // to not have to reject certain values of `s_meta` at runtime).
    // This means that:
    //
    // - `s_meta * S_ELEM` must be a multiple of `D_ELEM`
    // - Since this must hold for any value of `s_meta`, `S_ELEM`
    //   must be a multiple of `D_ELEM`
    // - `S_OFF - D_OFF` must be a multiple of `D_ELEM`
    //
    // Thus, let `OFFSET_DELTA_ELEMS = (S_OFF - D_OFF)/D_ELEM` and
    // `ELEM_MULTIPLE = S_ELEM/D_ELEM`. We can rewrite the above
    // expression as:
    //
    //   d_meta = (S_OFF - D_OFF + s_meta * S_ELEM)/D_ELEM
    //
    //   d_meta = OFFSET_DELTA_ELEMS + s_meta * ELEM_MULTIPLE
    //
    // Thus, plan selection checks these ratios and stores the parameters
    // needed to compute `d_meta` at runtime. `CastParams` associates the selected
    // plan with the `KnownLayout` types whose layouts were used to select it.
    /// Converts between slice DSTs using the ratios described above.
    UnsizedToUnsized { offset_delta_elems: usize, elem_multiple: usize },

    /// Uses the metadata selected for a sized source and a slice DST.
    SizedToUnsized { dst_meta: usize },

    /// Converts between sized layouts with equal sizes.
    SizedToSized,
}

impl CastPlan {
    /// Selects a plan from layout values without converting typed metadata.
    const fn try_compute(src: &DstLayout, dst: &DstLayout) -> Option<Self> {
        if src.align.get() < dst.align.get() {
            return None;
        }

        let plan = match (src.size_info, dst.size_info) {
            (SizeInfo::Sized { size: src_size }, SizeInfo::Sized { size: dst_size }) => {
                if src_size != dst_size {
                    return None;
                }

                // We checked above that `src_size == dst_size`.
                CastPlan::SizedToSized
            }
            (SizeInfo::Sized { size: src_size }, SizeInfo::SliceDst(dst)) => {
                let offset_delta = if let Some(od) = src_size.checked_sub(dst.offset) {
                    od
                } else {
                    return None;
                };

                let dst_elem_size = if let Some(e) = NonZeroUsize::new(dst.elem_size) {
                    e
                } else {
                    return None;
                };

                // PANICS: `dst_elem_size: NonZeroUsize`, so this won't
                // divide by zero.
                #[allow(clippy::arithmetic_side_effects)]
                let delta_mod_other_elem = offset_delta % dst_elem_size.get();

                if delta_mod_other_elem != 0 {
                    return None;
                }

                // PANICS: `dst_elem_size: NonZeroUsize`, so this won't
                // divide by zero.
                #[allow(clippy::arithmetic_side_effects)]
                let dst_meta = offset_delta / dst_elem_size.get();

                // The preceding math ensures that
                // `dst.offset + dst_meta * dst.elem_size == src_size`.
                CastPlan::SizedToUnsized { dst_meta }
            }
            (SizeInfo::SliceDst(src), SizeInfo::SliceDst(dst)) => {
                let offset_delta = if let Some(od) = src.offset.checked_sub(dst.offset) {
                    od
                } else {
                    return None;
                };

                let dst_elem_size = if let Some(e) = NonZeroUsize::new(dst.elem_size) {
                    e
                } else {
                    return None;
                };

                // PANICS: `dst_elem_size: NonZeroUsize`, so this won't
                // divide by zero.
                #[allow(clippy::arithmetic_side_effects)]
                let delta_mod_other_elem = offset_delta % dst_elem_size.get();

                // PANICS: `dst_elem_size: NonZeroUsize`, so this won't
                // divide by zero.
                #[allow(clippy::arithmetic_side_effects)]
                let elem_remainder = src.elem_size % dst_elem_size.get();

                if delta_mod_other_elem != 0 || src.elem_size < dst.elem_size || elem_remainder != 0
                {
                    return None;
                }

                // PANICS: `dst_elem_size: NonZeroUsize`, so this won't
                // divide by zero.
                #[allow(clippy::arithmetic_side_effects)]
                let offset_delta_elems = offset_delta / dst_elem_size.get();

                // PANICS: `dst_elem_size: NonZeroUsize`, so this won't
                // divide by zero.
                #[allow(clippy::arithmetic_side_effects)]
                let elem_multiple = src.elem_size / dst_elem_size.get();

                CastPlan::UnsizedToUnsized {
                    // We checked above that this is an exact ratio.
                    offset_delta_elems,
                    // We checked above that this is an exact ratio.
                    elem_multiple,
                }
            }
            _ => return None,
        };

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
    unsafe fn cast_metadata(self, src_meta: usize) -> usize {
        #[allow(unused)]
        use crate::util::polyfills::*;

        match self {
            CastPlan::UnsizedToUnsized { offset_delta_elems, elem_multiple } => {
                #[allow(unstable_name_collisions, clippy::multiple_unsafe_ops_per_block)]
                // SAFETY: The caller promises that neither the multiplication
                // nor the addition overflows `usize`.
                unsafe {
                    offset_delta_elems.unchecked_add(src_meta.unchecked_mul(elem_multiple))
                }
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

        // SAFETY: `self.plan` was selected for `Src::LAYOUT` and `Dst::LAYOUT`.
        // For `UnsizedToUnsized`, its parameters satisfy the equation:
        //
        //   D_OFF + d_meta * D_ELEM = S_OFF + s_meta * S_ELEM
        //
        // Since the caller promises that `src_meta` is valid `Src` metadata,
        // this math will not overflow, and the returned value will describe a
        // `Dst` of the same size. The other variants do no unchecked arithmetic.
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
