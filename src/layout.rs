// Copyright 2024 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use core::{mem, num::NonZeroUsize};

/// The target pointer width, counted in bits.
const POINTER_WIDTH_BITS: usize = mem::size_of::<usize>() * 8;

/// The layout of a type which might be dynamically-sized.
///
/// `DstLayout` describes the layout of sized types, slice types, and "slice
/// DSTs" - ie, those that are known by the type system to have a trailing slice
/// (as distinguished from `dyn Trait` types - such types *might* have a
/// trailing slice type, but the type system isn't aware of it).
///
/// Note that `DstLayout` does not have any internal invariants, so no guarantee
/// is made that a `DstLayout` conforms to any of Rust's requirements regarding
/// the layout of real Rust types or instances of types.
#[doc(hidden)]
#[allow(missing_debug_implementations, missing_copy_implementations)]
#[cfg_attr(any(kani, test), derive(Copy, Clone, Debug, PartialEq, Eq))]
pub struct DstLayout {
    pub(crate) align: NonZeroUsize,
    pub(crate) size_info: SizeInfo,
}

#[cfg_attr(any(kani, test), derive(Debug, PartialEq, Eq))]
#[derive(Copy, Clone)]
pub(crate) enum SizeInfo<E = usize> {
    Sized { size: usize },
    SliceDst(TrailingSliceLayout<E>),
}

#[cfg_attr(any(kani, test), derive(Debug, PartialEq, Eq))]
#[derive(Copy, Clone)]
pub(crate) struct TrailingSliceLayout<E = usize> {
    // The offset of the first byte of the trailing slice field. Note that this
    // is NOT the same as the minimum size of the type. For example, consider
    // the following type:
    //
    //   struct Foo {
    //       a: u16,
    //       b: u8,
    //       c: [u8],
    //   }
    //
    // In `Foo`, `c` is at byte offset 3. When `c.len() == 0`, `c` is followed
    // by a padding byte.
    pub(crate) offset: usize,
    // The size of the element type of the trailing slice field.
    pub(crate) elem_size: E,
}

impl SizeInfo {
    /// Attempts to create a `SizeInfo` from `Self` in which `elem_size` is a
    /// `NonZeroUsize`. If `elem_size` is 0, returns `None`.
    #[allow(unused)]
    const fn try_to_nonzero_elem_size(&self) -> Option<SizeInfo<NonZeroUsize>> {
        Some(match *self {
            SizeInfo::Sized { size } => SizeInfo::Sized { size },
            SizeInfo::SliceDst(TrailingSliceLayout { offset, elem_size }) => {
                if let Some(elem_size) = NonZeroUsize::new(elem_size) {
                    SizeInfo::SliceDst(TrailingSliceLayout { offset, elem_size })
                } else {
                    return None;
                }
            }
        })
    }
}

#[doc(hidden)]
#[derive(Copy, Clone)]
#[cfg_attr(test, derive(Debug))]
#[allow(missing_debug_implementations)]
pub enum CastType {
    Prefix,
    Suffix,
}

impl DstLayout {
    /// The minimum possible alignment of a type.
    const MIN_ALIGN: NonZeroUsize = match NonZeroUsize::new(1) {
        Some(min_align) => min_align,
        None => const_unreachable!(),
    };

    /// The maximum theoretic possible alignment of a type.
    ///
    /// For compatibility with future Rust versions, this is defined as the
    /// maximum power-of-two that fits into a `usize`. See also
    /// [`DstLayout::CURRENT_MAX_ALIGN`].
    pub(crate) const THEORETICAL_MAX_ALIGN: NonZeroUsize =
        match NonZeroUsize::new(1 << (POINTER_WIDTH_BITS - 1)) {
            Some(max_align) => max_align,
            None => const_unreachable!(),
        };

    /// The current, documented max alignment of a type \[1\].
    ///
    /// \[1\] Per <https://doc.rust-lang.org/reference/type-layout.html#the-alignment-modifiers>:
    ///
    ///   The alignment value must be a power of two from 1 up to
    ///   2<sup>29</sup>.
    #[cfg(not(kani))]
    pub(crate) const CURRENT_MAX_ALIGN: NonZeroUsize = match NonZeroUsize::new(1 << 28) {
        Some(max_align) => max_align,
        None => const_unreachable!(),
    };

    /// Constructs a `DstLayout` for a zero-sized type with `repr_align`
    /// alignment (or 1). If `repr_align` is provided, then it must be a power
    /// of two.
    ///
    /// # Panics
    ///
    /// This function panics if the supplied `repr_align` is not a power of two.
    ///
    /// # Safety
    ///
    /// Unsafe code may assume that the contract of this function is satisfied.
    #[doc(hidden)]
    #[must_use]
    #[inline]
    pub const fn new_zst(repr_align: Option<NonZeroUsize>) -> DstLayout {
        let align = match repr_align {
            Some(align) => align,
            None => Self::MIN_ALIGN,
        };

        const_assert!(align.get().is_power_of_two());

        DstLayout { align, size_info: SizeInfo::Sized { size: 0 } }
    }

    /// Constructs a `DstLayout` which describes `T`.
    ///
    /// # Safety
    ///
    /// Unsafe code may assume that `DstLayout` is the correct layout for `T`.
    #[doc(hidden)]
    #[must_use]
    #[inline]
    pub const fn for_type<T>() -> DstLayout {
        // SAFETY: `align` is correct by construction. `T: Sized`, and so it is
        // sound to initialize `size_info` to `SizeInfo::Sized { size }`; the
        // `size` field is also correct by construction.
        DstLayout {
            align: match NonZeroUsize::new(mem::align_of::<T>()) {
                Some(align) => align,
                None => const_unreachable!(),
            },
            size_info: SizeInfo::Sized { size: mem::size_of::<T>() },
        }
    }

    /// Constructs a `DstLayout` which describes `[T]`.
    ///
    /// # Safety
    ///
    /// Unsafe code may assume that `DstLayout` is the correct layout for `[T]`.
    pub(crate) const fn for_slice<T>() -> DstLayout {
        // SAFETY: The alignment of a slice is equal to the alignment of its
        // element type, and so `align` is initialized correctly.
        //
        // Since this is just a slice type, there is no offset between the
        // beginning of the type and the beginning of the slice, so it is
        // correct to set `offset: 0`. The `elem_size` is correct by
        // construction. Since `[T]` is a (degenerate case of a) slice DST, it
        // is correct to initialize `size_info` to `SizeInfo::SliceDst`.
        DstLayout {
            align: match NonZeroUsize::new(mem::align_of::<T>()) {
                Some(align) => align,
                None => const_unreachable!(),
            },
            size_info: SizeInfo::SliceDst(TrailingSliceLayout {
                offset: 0,
                elem_size: mem::size_of::<T>(),
            }),
        }
    }

    /// Like `Layout::extend`, this creates a layout that describes a record
    /// whose layout consists of `self` followed by `next` that includes the
    /// necessary inter-field padding, but not any trailing padding.
    ///
    /// In order to match the layout of a `#[repr(C)]` struct, this method
    /// should be invoked for each field in declaration order. To add trailing
    /// padding, call `DstLayout::pad_to_align` after extending the layout for
    /// all fields. If `self` corresponds to a type marked with
    /// `repr(packed(N))`, then `repr_packed` should be set to `Some(N)`,
    /// otherwise `None`.
    ///
    /// This method cannot be used to match the layout of a record with the
    /// default representation, as that representation is mostly unspecified.
    ///
    /// # Safety
    ///
    /// If a (potentially hypothetical) valid `repr(C)` Rust type begins with
    /// fields whose layout are `self`, and those fields are immediately
    /// followed by a field whose layout is `field`, then unsafe code may rely
    /// on `self.extend(field, repr_packed)` producing a layout that correctly
    /// encompasses those two components.
    ///
    /// We make no guarantees to the behavior of this method if these fragments
    /// cannot appear in a valid Rust type (e.g., the concatenation of the
    /// layouts would lead to a size larger than `isize::MAX`).
    #[doc(hidden)]
    #[must_use]
    #[inline]
    pub const fn extend(self, field: DstLayout, repr_packed: Option<NonZeroUsize>) -> Self {
        use crate::util::{max, min, padding_needed_for};

        // If `repr_packed` is `None`, there are no alignment constraints, and
        // the value can be defaulted to `THEORETICAL_MAX_ALIGN`.
        let max_align = match repr_packed {
            Some(max_align) => max_align,
            None => Self::THEORETICAL_MAX_ALIGN,
        };

        const_assert!(max_align.get().is_power_of_two());

        // We use Kani to prove that this method is robust to future increases
        // in Rust's maximum allowed alignment. However, if such a change ever
        // actually occurs, we'd like to be notified via assertion failures.
        #[cfg(not(kani))]
        {
            const_debug_assert!(self.align.get() <= DstLayout::CURRENT_MAX_ALIGN.get());
            const_debug_assert!(field.align.get() <= DstLayout::CURRENT_MAX_ALIGN.get());
            if let Some(repr_packed) = repr_packed {
                const_debug_assert!(repr_packed.get() <= DstLayout::CURRENT_MAX_ALIGN.get());
            }
        }

        // The field's alignment is clamped by `repr_packed` (i.e., the
        // `repr(packed(N))` attribute, if any) [1].
        //
        // [1] Per https://doc.rust-lang.org/reference/type-layout.html#the-alignment-modifiers:
        //
        //   The alignments of each field, for the purpose of positioning
        //   fields, is the smaller of the specified alignment and the alignment
        //   of the field's type.
        let field_align = min(field.align, max_align);

        // The struct's alignment is the maximum of its previous alignment and
        // `field_align`.
        let align = max(self.align, field_align);

        let size_info = match self.size_info {
            // If the layout is already a DST, we panic; DSTs cannot be extended
            // with additional fields.
            SizeInfo::SliceDst(..) => const_panic!("Cannot extend a DST with additional fields."),

            SizeInfo::Sized { size: preceding_size } => {
                // Compute the minimum amount of inter-field padding needed to
                // satisfy the field's alignment, and offset of the trailing
                // field. [1]
                //
                // [1] Per https://doc.rust-lang.org/reference/type-layout.html#the-alignment-modifiers:
                //
                //   Inter-field padding is guaranteed to be the minimum
                //   required in order to satisfy each field's (possibly
                //   altered) alignment.
                let padding = padding_needed_for(preceding_size, field_align);

                // This will not panic (and is proven to not panic, with Kani)
                // if the layout components can correspond to a leading layout
                // fragment of a valid Rust type, but may panic otherwise (e.g.,
                // combining or aligning the components would create a size
                // exceeding `isize::MAX`).
                let offset = match preceding_size.checked_add(padding) {
                    Some(offset) => offset,
                    None => const_panic!("Adding padding to `self`'s size overflows `usize`."),
                };

                match field.size_info {
                    SizeInfo::Sized { size: field_size } => {
                        // If the trailing field is sized, the resulting layout
                        // will be sized. Its size will be the sum of the
                        // preceeding layout, the size of the new field, and the
                        // size of inter-field padding between the two.
                        //
                        // This will not panic (and is proven with Kani to not
                        // panic) if the layout components can correspond to a
                        // leading layout fragment of a valid Rust type, but may
                        // panic otherwise (e.g., combining or aligning the
                        // components would create a size exceeding
                        // `usize::MAX`).
                        let size = match offset.checked_add(field_size) {
                            Some(size) => size,
                            None => const_panic!("`field` cannot be appended without the total size overflowing `usize`"),
                        };
                        SizeInfo::Sized { size }
                    }
                    SizeInfo::SliceDst(TrailingSliceLayout {
                        offset: trailing_offset,
                        elem_size,
                    }) => {
                        // If the trailing field is dynamically sized, so too
                        // will the resulting layout. The offset of the trailing
                        // slice component is the sum of the offset of the
                        // trailing field and the trailing slice offset within
                        // that field.
                        //
                        // This will not panic (and is proven with Kani to not
                        // panic) if the layout components can correspond to a
                        // leading layout fragment of a valid Rust type, but may
                        // panic otherwise (e.g., combining or aligning the
                        // components would create a size exceeding
                        // `usize::MAX`).
                        let offset = match offset.checked_add(trailing_offset) {
                            Some(offset) => offset,
                            None => const_panic!("`field` cannot be appended without the total size overflowing `usize`"),
                        };
                        SizeInfo::SliceDst(TrailingSliceLayout { offset, elem_size })
                    }
                }
            }
        };

        DstLayout { align, size_info }
    }

    /// Like `Layout::pad_to_align`, this routine rounds the size of this layout
    /// up to the nearest multiple of this type's alignment or `repr_packed`
    /// (whichever is less). This method leaves DST layouts unchanged, since the
    /// trailing padding of DSTs is computed at runtime.
    ///
    /// In order to match the layout of a `#[repr(C)]` struct, this method
    /// should be invoked after the invocations of [`DstLayout::extend`]. If
    /// `self` corresponds to a type marked with `repr(packed(N))`, then
    /// `repr_packed` should be set to `Some(N)`, otherwise `None`.
    ///
    /// This method cannot be used to match the layout of a record with the
    /// default representation, as that representation is mostly unspecified.
    ///
    /// # Safety
    ///
    /// If a (potentially hypothetical) valid `repr(C)` type begins with fields
    /// whose layout are `self` followed only by zero or more bytes of trailing
    /// padding (not included in `self`), then unsafe code may rely on
    /// `self.pad_to_align(repr_packed)` producing a layout that correctly
    /// encapsulates the layout of that type.
    ///
    /// We make no guarantees to the behavior of this method if `self` cannot
    /// appear in a valid Rust type (e.g., because the addition of trailing
    /// padding would lead to a size larger than `isize::MAX`).
    #[doc(hidden)]
    #[must_use]
    #[inline]
    pub const fn pad_to_align(self) -> Self {
        use crate::util::padding_needed_for;

        let size_info = match self.size_info {
            // For sized layouts, we add the minimum amount of trailing padding
            // needed to satisfy alignment.
            SizeInfo::Sized { size: unpadded_size } => {
                let padding = padding_needed_for(unpadded_size, self.align);
                let size = match unpadded_size.checked_add(padding) {
                    Some(size) => size,
                    None => const_panic!("Adding padding caused size to overflow `usize`."),
                };
                SizeInfo::Sized { size }
            }
            // For DST layouts, trailing padding depends on the length of the
            // trailing DST and is computed at runtime. This does not alter the
            // offset or element size of the layout, so we leave `size_info`
            // unchanged.
            size_info @ SizeInfo::SliceDst(_) => size_info,
        };

        DstLayout { align: self.align, size_info }
    }

    /// Validates that a cast is sound from a layout perspective.
    ///
    /// Validates that the size and alignment requirements of a type with the
    /// layout described in `self` would not be violated by performing a
    /// `cast_type` cast from a pointer with address `addr` which refers to a
    /// memory region of size `bytes_len`.
    ///
    /// If the cast is valid, `validate_cast_and_convert_metadata` returns
    /// `(elems, split_at)`. If `self` describes a dynamically-sized type, then
    /// `elems` is the maximum number of trailing slice elements for which a
    /// cast would be valid (for sized types, `elem` is meaningless and should
    /// be ignored). `split_at` is the index at which to split the memory region
    /// in order for the prefix (suffix) to contain the result of the cast, and
    /// in order for the remaining suffix (prefix) to contain the leftover
    /// bytes.
    ///
    /// There are three conditions under which a cast can fail:
    /// - The smallest possible value for the type is larger than the provided
    ///   memory region
    /// - A prefix cast is requested, and `addr` does not satisfy `self`'s
    ///   alignment requirement
    /// - A suffix cast is requested, and `addr + bytes_len` does not satisfy
    ///   `self`'s alignment requirement (as a consequence, since all instances
    ///   of the type are a multiple of its alignment, no size for the type will
    ///   result in a starting address which is properly aligned)
    ///
    /// # Safety
    ///
    /// The caller may assume that this implementation is correct, and may rely
    /// on that assumption for the soundness of their code. In particular, the
    /// caller may assume that, if `validate_cast_and_convert_metadata` returns
    /// `Some((elems, split_at))`, then:
    /// - A pointer to the type (for dynamically sized types, this includes
    ///   `elems` as its pointer metadata) describes an object of size `size <=
    ///   bytes_len`
    /// - If this is a prefix cast:
    ///   - `addr` satisfies `self`'s alignment
    ///   - `size == split_at`
    /// - If this is a suffix cast:
    ///   - `split_at == bytes_len - size`
    ///   - `addr + split_at` satisfies `self`'s alignment
    ///
    /// Note that this method does *not* ensure that a pointer constructed from
    /// its return values will be a valid pointer. In particular, this method
    /// does not reason about `isize` overflow, which is a requirement of many
    /// Rust pointer APIs, and may at some point be determined to be a validity
    /// invariant of pointer types themselves. This should never be a problem so
    /// long as the arguments to this method are derived from a known-valid
    /// pointer (e.g., one derived from a safe Rust reference), but it is
    /// nonetheless the caller's responsibility to justify that pointer
    /// arithmetic will not overflow based on a safety argument *other than* the
    /// mere fact that this method returned successfully.
    ///
    /// # Panics
    ///
    /// `validate_cast_and_convert_metadata` will panic if `self` describes a
    /// DST whose trailing slice element is zero-sized.
    ///
    /// If `addr + bytes_len` overflows `usize`,
    /// `validate_cast_and_convert_metadata` may panic, or it may return
    /// incorrect results. No guarantees are made about when
    /// `validate_cast_and_convert_metadata` will panic. The caller should not
    /// rely on `validate_cast_and_convert_metadata` panicking in any particular
    /// condition, even if `debug_assertions` are enabled.
    #[allow(unused)]
    pub(crate) const fn validate_cast_and_convert_metadata(
        &self,
        addr: usize,
        bytes_len: usize,
        cast_type: CastType,
    ) -> Option<(usize, usize)> {
        // `debug_assert!`, but with `#[allow(clippy::arithmetic_side_effects)]`.
        macro_rules! __const_debug_assert {
            ($e:expr $(, $msg:expr)?) => {
                const_debug_assert!({
                    #[allow(clippy::arithmetic_side_effects)]
                    let e = $e;
                    e
                } $(, $msg)?);
            };
        }

        // Note that, in practice, `self` is always a compile-time constant. We
        // do this check earlier than needed to ensure that we always panic as a
        // result of bugs in the program (such as calling this function on an
        // invalid type) instead of allowing this panic to be hidden if the cast
        // would have failed anyway for runtime reasons (such as a too-small
        // memory region).
        //
        // TODO(#67): Once our MSRV is 1.65, use let-else:
        // https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html#let-else-statements
        let size_info = match self.size_info.try_to_nonzero_elem_size() {
            Some(size_info) => size_info,
            None => const_panic!("attempted to cast to slice type with zero-sized element"),
        };

        // Precondition
        __const_debug_assert!(
            addr.checked_add(bytes_len).is_some(),
            "`addr` + `bytes_len` > usize::MAX"
        );

        // Alignment checks go in their own block to avoid introducing variables
        // into the top-level scope.
        {
            // We check alignment for `addr` (for prefix casts) or `addr +
            // bytes_len` (for suffix casts). For a prefix cast, the correctness
            // of this check is trivial - `addr` is the address the object will
            // live at.
            //
            // For a suffix cast, we know that all valid sizes for the type are
            // a multiple of the alignment (and by safety precondition, we know
            // `DstLayout` may only describe valid Rust types). Thus, a
            // validly-sized instance which lives at a validly-aligned address
            // must also end at a validly-aligned address. Thus, if the end
            // address for a suffix cast (`addr + bytes_len`) is not aligned,
            // then no valid start address will be aligned either.
            let offset = match cast_type {
                CastType::Prefix => 0,
                CastType::Suffix => bytes_len,
            };

            // Addition is guaranteed not to overflow because `offset <=
            // bytes_len`, and `addr + bytes_len <= usize::MAX` is a
            // precondition of this method. Modulus is guaranteed not to divide
            // by 0 because `align` is non-zero.
            #[allow(clippy::arithmetic_side_effects)]
            if (addr + offset) % self.align.get() != 0 {
                return None;
            }
        }

        let (elems, self_bytes) = match size_info {
            SizeInfo::Sized { size } => {
                if size > bytes_len {
                    return None;
                }
                (0, size)
            }
            SizeInfo::SliceDst(TrailingSliceLayout { offset, elem_size }) => {
                // Calculate the maximum number of bytes that could be consumed
                // - any number of bytes larger than this will either not be a
                // multiple of the alignment, or will be larger than
                // `bytes_len`.
                let max_total_bytes =
                    crate::util::round_down_to_next_multiple_of_alignment(bytes_len, self.align);
                // Calculate the maximum number of bytes that could be consumed
                // by the trailing slice.
                //
                // TODO(#67): Once our MSRV is 1.65, use let-else:
                // https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html#let-else-statements
                let max_slice_and_padding_bytes = match max_total_bytes.checked_sub(offset) {
                    Some(max) => max,
                    // `bytes_len` too small even for 0 trailing slice elements.
                    None => return None,
                };

                // Calculate the number of elements that fit in
                // `max_slice_and_padding_bytes`; any remaining bytes will be
                // considered padding.
                //
                // Guaranteed not to divide by zero: `elem_size` is non-zero.
                #[allow(clippy::arithmetic_side_effects)]
                let elems = max_slice_and_padding_bytes / elem_size.get();
                // Guaranteed not to overflow on multiplication: `usize::MAX >=
                // max_slice_and_padding_bytes >= (max_slice_and_padding_bytes /
                // elem_size) * elem_size`.
                //
                // Guaranteed not to overflow on addition:
                // - max_slice_and_padding_bytes == max_total_bytes - offset
                // - elems * elem_size <= max_slice_and_padding_bytes == max_total_bytes - offset
                // - elems * elem_size + offset <= max_total_bytes <= usize::MAX
                #[allow(clippy::arithmetic_side_effects)]
                let without_padding = offset + elems * elem_size.get();
                // `self_bytes` is equal to the offset bytes plus the bytes
                // consumed by the trailing slice plus any padding bytes
                // required to satisfy the alignment. Note that we have computed
                // the maximum number of trailing slice elements that could fit
                // in `self_bytes`, so any padding is guaranteed to be less than
                // the size of an extra element.
                //
                // Guaranteed not to overflow:
                // - By previous comment: without_padding == elems * elem_size +
                //   offset <= max_total_bytes
                // - By construction, `max_total_bytes` is a multiple of
                //   `self.align`.
                // - At most, adding padding needed to round `without_padding`
                //   up to the next multiple of the alignment will bring
                //   `self_bytes` up to `max_total_bytes`.
                #[allow(clippy::arithmetic_side_effects)]
                let self_bytes =
                    without_padding + crate::util::padding_needed_for(without_padding, self.align);
                (elems, self_bytes)
            }
        };

        __const_debug_assert!(self_bytes <= bytes_len);

        let split_at = match cast_type {
            CastType::Prefix => self_bytes,
            // Guaranteed not to underflow:
            // - In the `Sized` branch, only returns `size` if `size <=
            //   bytes_len`.
            // - In the `SliceDst` branch, calculates `self_bytes <=
            //   max_toatl_bytes`, which is upper-bounded by `bytes_len`.
            #[allow(clippy::arithmetic_side_effects)]
            CastType::Suffix => bytes_len - self_bytes,
        };

        Some((elems, split_at))
    }
}
