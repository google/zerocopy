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

use crate::*;

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
        /// The parameters required in order to perform a pointer cast from
        /// `Src` to `Dst`.
        ///
        /// These are a compile-time function of the layouts of `Src`
        /// and `Dst`.
        ///
        /// # Safety
        ///
        /// `Src`'s alignment must not be smaller than `Dst`'s alignment.
        struct CastParams<Src: ?Sized, Dst: ?Sized> {
            inner: CastParamsInner,
            _src: PhantomData<Src>,
            _dst: PhantomData<Dst>,
        }

        #[derive(Copy, Clone)]
        enum CastParamsInner {
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
            /// The parameters required in order to perform an
            /// unsized-to-unsized pointer cast from `Src` to `Dst` as
            /// described above.
            ///
            /// # Safety
            ///
            /// `Src` and `Dst` must both be slice DSTs.
            ///
            /// `offset_delta_elems` and `elem_multiple` must be valid as
            /// described above.
            UnsizedToUnsized { offset_delta_elems: usize, elem_multiple: usize },

            /// The metadata of a `Dst` which has the same size as `Src:
            /// Sized`.
            ///
            /// # Safety
            ///
            /// `Src: Sized` and `Dst` must be a slice DST.
            ///
            /// A raw `Dst` pointer with metadata `dst_meta` must address
            /// `size_of::<Src>()` bytes.
            SizedToUnsized { dst_meta: usize },

            /// The metadata of a `Dst` which has the same size as `Src:
            /// Sized`.
            ///
            /// # Safety
            ///
            /// `Src` and `Dst` must both be `Sized` and `size_of::<Src>()
            /// == size_of::<Dst>()`.
            SizedToSized,
        }

        impl<Src: ?Sized, Dst: ?Sized> Copy for CastParams<Src, Dst> {}
        impl<Src: ?Sized, Dst: ?Sized> Clone for CastParams<Src, Dst> {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<Src: ?Sized, Dst: ?Sized> CastParams<Src, Dst> {
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
                    Some(layout) => layout,
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
            const fn try_compute(
                src_layout: &DstLayout,
                dst_layout: &DstLayout,
            ) -> Option<CastParams<Src, Dst>> {
                if src_layout.align.get() < dst_layout.align.get() {
                    return None;
                }

                let inner = match (src_layout.size_info, dst_layout.size_info) {
                    (
                        SizeInfo::Sized { size: src_size },
                        SizeInfo::Sized { size: dst_size },
                    ) => {
                        if src_size != dst_size {
                            return None;
                        }

                        // SAFETY: We checked above that `src_size ==
                        // dst_size`.
                        CastParamsInner::SizedToSized
                    }
                    (SizeInfo::Sized { size: src_size }, SizeInfo::SliceDst(_)) => {
                        let dst_meta = match dst_layout.metadata_for_exact_size(src_size) {
                            Some(meta) => meta,
                            None => return None,
                        };

                        // SAFETY: The preceding math ensures that a `Dst`
                        // with `dst_meta` addresses `src_size` bytes.
                        CastParamsInner::SizedToUnsized { dst_meta }
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
                                let elems =
                                    match dst_layout.metadata_for_exact_size(src_zero_size) {
                                        Some(elems) => elems,
                                        None => return None,
                                    };
                                if !Self::size_sequences_match(src, dst, elems) {
                                    return None;
                                }
                                elems
                            }
                        };

                        CastParamsInner::UnsizedToUnsized {
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
                Some(CastParams { inner, _src: PhantomData, _dst: PhantomData })
            }
        }

        impl<Src: KnownLayout + ?Sized, Dst: KnownLayout + ?Sized> CastParams<Src, Dst> {
            /// Produces `Dst` metadata describing an object of the same
            /// size as the `Src` described by `src_meta`.
            ///
            /// # Safety
            ///
            /// `src_meta` describes a `Src` whose size is no larger than
            /// `isize::MAX`.
            #[inline(always)]
            unsafe fn cast_metadata(
                self,
                src_meta: Src::PointerMetadata,
            ) -> Dst::PointerMetadata {
                let dst_meta = match self.inner {
                    CastParamsInner::UnsizedToUnsized { offset_delta_elems, elem_multiple } => {
                        let src_meta = src_meta.to_elem_count();
                        // SAFETY: `self` witnesses that this affine map
                        // makes `Src` and `Dst`'s complete rounded size
                        // formulas equal for every source metadata value.
                        // Interpret the arithmetic in this proof over the
                        // mathematical nonnegative integers. Since the
                        // caller promises that `src_meta` is valid `Src`
                        // metadata, the source object size `src_size` it
                        // describes is at most `isize::MAX`. Let
                        // `src_elem_size` and `dst_elem_size` be the
                        // respective trailing-slice element sizes. Then:
                        //
                        //   src_meta * src_elem_size
                        //       <= src_size <= isize::MAX.
                        //
                        // Since `elem_multiple` is the exact ratio
                        // `src_elem_size / dst_elem_size` and
                        // `dst_elem_size >= 1`,
                        //
                        //   src_meta * elem_multiple
                        //       <= src_meta * src_elem_size
                        //       <= isize::MAX <= usize::MAX.
                        //
                        // Thus `scaled_elems = src_meta * elem_multiple`
                        // is representable, and its byte contribution is
                        // `scaled_elems * dst_elem_size = src_meta *
                        // src_elem_size`. Let `base_bytes =
                        // offset_delta_elems * dst_elem_size`.
                        // `size_sequences_match` compares the source
                        // formula with the destination formula advanced by
                        // `base_bytes`. The latter's unrounded term
                        // contains `base_bytes + src_meta * src_elem_size`,
                        // and its complete size is at least that large
                        // (formally checked by Kani in
                        // `prove_size_formula_bounds_size_offset`).
                        // Sequence equality therefore gives, over the
                        // mathematical nonnegative integers,
                        //
                        //   base_bytes + src_meta * src_elem_size
                        //       = (offset_delta_elems + scaled_elems)
                        //           * dst_elem_size
                        //       <= src_size.
                        //
                        // Since `dst_elem_size >= 1`, the metadata sum
                        // `offset_delta_elems + scaled_elems` is also at
                        // most `src_size`, and thus at most `isize::MAX <=
                        // usize::MAX`. The sum is therefore representable,
                        // and the returned metadata describes a `Dst` of
                        // the same size.
                        // SAFETY: The bounds above establish the helper's
                        // complete no-overflow precondition.
                        unsafe {
                            super::add_scaled_metadata(
                                offset_delta_elems,
                                src_meta,
                                elem_multiple,
                            )
                        }
                    }
                    CastParamsInner::SizedToUnsized { dst_meta } => dst_meta,
                    CastParamsInner::SizedToSized => 0,
                };
                Dst::PointerMetadata::from_elem_count(dst_meta)
            }
        }

        trait Params<Src: ?Sized> {
            const CAST_PARAMS: CastParams<Src, Self>;
        }

        impl<Src, Dst> Params<Src> for Dst
        where
            Src: KnownLayout + ?Sized,
            Dst: KnownLayout + ?Sized,
        {
            const CAST_PARAMS: CastParams<Src, Dst> =
                match CastParams::try_compute(&Src::LAYOUT, &Dst::LAYOUT) {
                    Some(params) => params,
                    None => const_panic!(
                        "cannot `transmute_ref!` or `transmute_mut!` between incompatible types"
                    ),
                };
        }

        let src_meta = <Src as KnownLayout>::pointer_to_metadata(src.as_ptr());
        let params = <Dst as Params<Src>>::CAST_PARAMS;

        // SAFETY: `src: PtrInner` guarantees that `src`'s referent is zero
        // bytes or lives in a single allocation, which means that it is no
        // larger than `isize::MAX` bytes [1].
        //
        // [1] https://doc.rust-lang.org/1.92.0/std/ptr/index.html#allocation
        let dst_meta = unsafe { params.cast_metadata(src_meta) };

        <Dst as KnownLayout>::raw_from_ptr_len(src.as_non_null().cast(), dst_meta).as_ptr()
    }
}