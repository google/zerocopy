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
            // Thus, we just need to compute the following and confirm that
            // they have integer solutions in order to both a) determine
            // whether infallible `Src` -> `Dst` casts are possible and, b)
            // pre-compute the parameters necessary to perform those casts
            // at runtime. These parameters are encapsulated in
            // `CastParams`, which acts as a witness that such infallible
            // casts are possible.
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
            const fn try_compute(
                src: &DstLayout,
                dst: &DstLayout,
            ) -> Option<CastParams<Src, Dst>> {
                if src.align.get() < dst.align.get() {
                    return None;
                }

                let inner = match (src.size_info, dst.size_info) {
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

                        // SAFETY: The preceding math ensures that a `Dst`
                        // with `dst_meta` addresses `src_size` bytes.
                        CastParamsInner::SizedToUnsized { dst_meta }
                    }
                    (SizeInfo::SliceDst(src), SizeInfo::SliceDst(dst)) => {
                        let offset_delta = if let Some(od) = src.offset.checked_sub(dst.offset)
                        {
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

                        if delta_mod_other_elem != 0
                            || src.elem_size < dst.elem_size
                            || elem_remainder != 0
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

                        CastParamsInner::UnsizedToUnsized {
                            // SAFETY: We checked above that this is an exact ratio.
                            offset_delta_elems,
                            // SAFETY: We checked above that this is an exact ratio.
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
            /// # Safety
            ///
            /// `src_meta` describes a `Src` whose size is no larger than
            /// `isize::MAX`.
            ///
            /// The returned metadata describes a `Dst` of the same size as
            /// the original `Src`.
            #[inline(always)]
            unsafe fn cast_metadata(
                self,
                src_meta: Src::PointerMetadata,
            ) -> Dst::PointerMetadata {
                #[allow(unused)]
                use crate::util::polyfills::*;

                let dst_meta = match self.inner {
                    CastParamsInner::UnsizedToUnsized { offset_delta_elems, elem_multiple } => {
                        let src_meta = src_meta.to_elem_count();
                        #[allow(
                            unstable_name_collisions,
                            clippy::multiple_unsafe_ops_per_block
                        )]
                        // SAFETY: `self` is a witness that the following
                        // equation holds:
                        //
                        //   D_OFF + d_meta * D_ELEM = S_OFF + s_meta * S_ELEM
                        //
                        // Since the caller promises that `src_meta` is
                        // valid `Src` metadata, this math will not
                        // overflow, and the returned value will describe a
                        // `Dst` of the same size.
                        unsafe {
                            offset_delta_elems
                                .unchecked_add(src_meta.unchecked_mul(elem_multiple))
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
