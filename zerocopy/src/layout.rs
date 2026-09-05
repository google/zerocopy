// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2024 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use core::{mem, num::NonZeroUsize};

use crate::util;

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
#[cfg_attr(any(kani, test), derive(Debug, PartialEq, Eq))]
#[derive(Copy, Clone)]
pub struct DstLayout {
    pub(crate) align: NonZeroUsize,
    pub(crate) size_info: SizeInfo,
    // Is it guaranteed statically (without knowing a value's runtime metadata)
    // that the top-level type contains no padding? This does *not* apply
    // recursively - for example, `[(u8, u16)]` has `statically_shallow_unpadded
    // = true` even though this type likely has padding inside each `(u8, u16)`.
    pub(crate) statically_shallow_unpadded: bool,
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
    // When this describes a valid Rust type, `size_align` is a power of two,
    // `size_prefix < size_align`, and, for a trailing slice length `elems`, the
    // size of the enclosing type is:
    //
    //   size_prefix
    //       + round_up(size_offset + elems * elem_size, size_align)
    //
    // `size_prefix` is always less than `size_align`. These fields are
    // separate from `offset` because packing a field changes the field's
    // placement and the enclosing type's alignment, but does not change
    // trailing padding internal to the field's type. In particular, a nested
    // slice DST can require an inner rounding operation whose origin differs
    // from the physical offset of the trailing slice.
    pub(crate) size_prefix: usize,
    pub(crate) size_offset: usize,
    pub(crate) size_align: NonZeroUsize,
}

impl TrailingSliceLayout {
    /// Computes the size described by this layout for `elems` trailing slice
    /// elements.
    #[inline(always)]
    pub(crate) const fn size_for_elems(self, elems: usize) -> Option<usize> {
        let trailing_size = match self.elem_size.checked_mul(elems) {
            Some(size) => size,
            None => return None,
        };
        let without_padding = match self.size_offset.checked_add(trailing_size) {
            Some(size) => size,
            None => return None,
        };
        let with_padding = match without_padding
            .checked_add(util::padding_needed_for(without_padding, self.size_align))
        {
            Some(size) => size,
            None => return None,
        };
        self.size_prefix.checked_add(with_padding)
    }

    /// Returns the largest trailing slice length whose object size is exactly
    /// `size`.
    ///
    /// Returns `None` if there is no such length or if the trailing slice
    /// element is zero-sized.
    #[inline(always)]
    const fn metadata_for_exact_size(self, size: usize) -> Option<usize> {
        if self.elem_size == 0 {
            return None;
        }

        let rounded_size = match size.checked_sub(self.size_prefix) {
            Some(size) => size,
            None => return None,
        };
        #[allow(clippy::arithmetic_side_effects)]
        if rounded_size % self.size_align.get() != 0 {
            return None;
        }
        let available = match rounded_size.checked_sub(self.size_offset) {
            Some(available) => available,
            None => return None,
        };
        // PANICS: `self.elem_size != 0`, as checked above.
        #[allow(clippy::arithmetic_side_effects)]
        let elems = available / self.elem_size;

        match self.size_for_elems(elems) {
            Some(candidate_size) if candidate_size == size => Some(elems),
            _ => None,
        }
    }

    /// Returns whether `self` and `other` describe the same size for every
    /// trailing slice length.
    ///
    /// This recognizes two sufficient forms. If both formulas use the same
    /// rounding alignment and begin at the same residue, each future rounding
    /// decision is identical. If the element size is a multiple of both
    /// rounding alignments, neither formula's padding changes as the length
    /// increases. In both cases, equality at length zero proves equality for
    /// every length.
    #[inline(always)]
    pub(crate) const fn has_same_size_sequence(self, other: Self) -> bool {
        if self.elem_size != other.elem_size {
            return false;
        }

        match (self.size_for_elems(0), other.size_for_elems(0)) {
            (Some(self_size), Some(other_size)) if self_size == other_size => {}
            _ => return false,
        }

        let self_align = self.size_align.get();
        let other_align = other.size_align.get();
        let max_align = if self_align > other_align { self_align } else { other_align };

        // Since valid layout alignments are powers of two, `max_align` is a
        // multiple of both alignments. Every metadata increment therefore
        // adds exactly `elem_size` to both rounded sizes.
        #[allow(clippy::arithmetic_side_effects)]
        if self.elem_size % max_align == 0 {
            return true;
        }

        if self_align != other_align {
            return false;
        }

        // Both formulas visit the same residue after every metadata increment,
        // so they add and remove padding in lockstep.
        #[allow(clippy::arithmetic_side_effects)]
        let self_residue = self.size_offset % self_align;
        #[allow(clippy::arithmetic_side_effects)]
        let other_residue = other.size_offset % other_align;
        self_residue == other_residue
    }
}

impl SizeInfo {
    /// Attempts to create a `SizeInfo` from `Self` in which `elem_size` is a
    /// `NonZeroUsize`. If `elem_size` is 0, returns `None`.
    #[allow(unused)]
    #[cfg_attr(not(zerocopy_inline_always), inline)]
    #[cfg_attr(zerocopy_inline_always, inline(always))]
    const fn try_to_nonzero_elem_size(&self) -> Option<SizeInfo<NonZeroUsize>> {
        Some(match *self {
            SizeInfo::Sized { size } => SizeInfo::Sized { size },
            SizeInfo::SliceDst(TrailingSliceLayout {
                offset,
                elem_size,
                size_prefix,
                size_offset,
                size_align,
            }) => {
                if let Some(elem_size) = NonZeroUsize::new(elem_size) {
                    SizeInfo::SliceDst(TrailingSliceLayout {
                        offset,
                        elem_size,
                        size_prefix,
                        size_offset,
                        size_align,
                    })
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

#[cfg_attr(test, derive(Debug))]
pub(crate) enum MetadataCastError {
    Alignment,
    Size,
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
    #[cfg(not(target_pointer_width = "16"))]
    pub(crate) const CURRENT_MAX_ALIGN: NonZeroUsize = match NonZeroUsize::new(1 << 28) {
        Some(max_align) => max_align,
        None => const_unreachable!(),
    };

    #[cfg(not(kani))]
    #[cfg(target_pointer_width = "16")]
    pub(crate) const CURRENT_MAX_ALIGN: NonZeroUsize = match NonZeroUsize::new(1 << 15) {
        Some(max_align) => max_align,
        None => const_unreachable!(),
    };

    /// The maximum size of an allocation \[1\].
    ///
    /// \[1\] Per <https://doc.rust-lang.org/1.91.1/std/ptr/index.html#allocation>:
    ///
    ///   For any allocation with base `address`, `size`, and a set of `addresses`,
    ///   the following are guaranteed: [..]
    ///
    ///   - `size <= isize::MAX`
    ///
    #[allow(clippy::as_conversions)]
    pub(crate) const MAX_SIZE: usize = isize::MAX as usize;

    /// Assumes that this layout lacks static shallow padding.
    ///
    /// # Panics
    ///
    /// This method does not panic.
    ///
    /// # Safety
    ///
    /// If `self` describes the size and alignment of type that lacks static
    /// shallow padding, unsafe code may assume that the result of this method
    /// accurately reflects the size, alignment, and lack of static shallow
    /// padding of that type.
    const fn assume_shallow_unpadded(self) -> Self {
        Self { statically_shallow_unpadded: true, ..self }
    }

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

        DstLayout {
            align,
            size_info: SizeInfo::Sized { size: 0 },
            statically_shallow_unpadded: true,
        }
    }

    /// Constructs a `DstLayout` which describes `T` and assumes `T` may contain
    /// padding.
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
        // `size` field is also correct by construction. `unpadded` can safely
        // default to `false`.
        DstLayout {
            align: match NonZeroUsize::new(mem::align_of::<T>()) {
                Some(align) => align,
                None => const_unreachable!(),
            },
            size_info: SizeInfo::Sized { size: mem::size_of::<T>() },
            statically_shallow_unpadded: false,
        }
    }

    /// Constructs a `DstLayout` which describes a `T` that does not contain
    /// padding.
    ///
    /// # Safety
    ///
    /// Unsafe code may assume that `DstLayout` is the correct layout for `T`.
    #[doc(hidden)]
    #[must_use]
    #[inline]
    pub const fn for_unpadded_type<T>() -> DstLayout {
        Self::for_type::<T>().assume_shallow_unpadded()
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
                size_prefix: 0,
                size_offset: 0,
                size_align: match NonZeroUsize::new(mem::align_of::<T>()) {
                    Some(align) => align,
                    None => const_unreachable!(),
                },
            }),
            statically_shallow_unpadded: true,
        }
    }

    /// Constructs a complete `DstLayout` reflecting a `repr(C)` struct with the
    /// given alignment modifiers and fields.
    ///
    /// This method cannot be used to match the layout of a record with the
    /// default representation, as that representation is mostly unspecified.
    ///
    /// # Safety
    ///
    /// For any definition of a `repr(C)` struct, if this method is invoked with
    /// alignment modifiers and fields corresponding to that definition, the
    /// resulting `DstLayout` will correctly encode the layout of that struct.
    ///
    /// We make no guarantees to the behavior of this method when it is invoked
    /// with arguments that cannot correspond to a valid `repr(C)` struct.
    #[must_use]
    #[inline]
    pub const fn for_repr_c_struct(
        repr_align: Option<NonZeroUsize>,
        repr_packed: Option<NonZeroUsize>,
        fields: &[DstLayout],
    ) -> DstLayout {
        let mut layout = DstLayout::new_zst(repr_align);

        let mut i = 0;
        #[allow(clippy::arithmetic_side_effects)]
        while i < fields.len() {
            #[allow(clippy::indexing_slicing)]
            let field = fields[i];
            layout = layout.extend(field, repr_packed);
            i += 1;
        }

        layout = layout.pad_to_align();

        // SAFETY: `layout` accurately describes the layout of a `repr(C)`
        // struct with `repr_align` or `repr_packed` alignment modifications and
        // the given `fields`. The `layout` is constructed using a sequence of
        // invocations of `DstLayout::{new_zst,extend,pad_to_align}`. The
        // documentation of these items vows that invocations in this manner
        // will accurately describe a type, so long as:
        //
        //  - that type is `repr(C)`,
        //  - its fields are enumerated in the order they appear,
        //  - the presence of `repr_align` and `repr_packed` are correctly accounted for.
        //
        // We respect all three of these preconditions above.
        layout
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
        use util::{max, min, padding_needed_for};

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

        let (interfield_padding, size_info) = match self.size_info {
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

                (
                    padding,
                    match field.size_info {
                        SizeInfo::Sized { size: field_size } => {
                            // If the trailing field is sized, the resulting layout
                            // will be sized. Its size will be the sum of the
                            // preceding layout, the size of the new field, and the
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
                            size_prefix,
                            size_offset,
                            size_align,
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
                            let trailing_offset = match offset.checked_add(trailing_offset) {
                                Some(offset) => offset,
                                None => const_panic!("`field` cannot be appended without the total size overflowing `usize`"),
                            };

                            // Before normalization, the composite's size is:
                            //
                            //   offset + size_prefix
                            //       + round_up(size_offset + elems * elem_size, size_align)
                            //
                            // Split `offset + size_prefix` into a remainder
                            // less than `size_align` and a multiple of
                            // `size_align`. The multiple can move inside the
                            // rounding operation without changing the result.
                            let unnormalized_prefix = match offset.checked_add(size_prefix) {
                                Some(prefix) => prefix,
                                None => const_panic!("`field` cannot be appended without the total size overflowing `usize`"),
                            };
                            #[allow(clippy::arithmetic_side_effects)]
                            let size_prefix = unnormalized_prefix % size_align.get();
                            // `size_prefix` is a remainder of
                            // `unnormalized_prefix`.
                            #[allow(clippy::arithmetic_side_effects)]
                            let prefix_multiple = unnormalized_prefix - size_prefix;
                            let size_offset = match prefix_multiple.checked_add(size_offset) {
                                Some(offset) => offset,
                                None => const_panic!("`field` cannot be appended without the total size overflowing `usize`"),
                            };

                            SizeInfo::SliceDst(TrailingSliceLayout {
                                offset: trailing_offset,
                                elem_size,
                                size_prefix,
                                size_offset,
                                size_align,
                            })
                        }
                    },
                )
            }
        };

        let statically_shallow_unpadded = self.statically_shallow_unpadded
            && field.statically_shallow_unpadded
            && interfield_padding == 0;

        DstLayout { align, size_info, statically_shallow_unpadded }
    }

    /// Like `Layout::pad_to_align`, this routine rounds the size of this layout
    /// up to the nearest multiple of this type's alignment. For DST layouts,
    /// this updates the runtime size formula to account for trailing padding.
    ///
    /// In order to match the layout of a `#[repr(C)]` struct, this method
    /// should be invoked after the invocations of [`DstLayout::extend`].
    ///
    /// This method cannot be used to match the layout of a record with the
    /// default representation, as that representation is mostly unspecified.
    ///
    /// # Safety
    ///
    /// If a (potentially hypothetical) valid `repr(C)` type begins with fields
    /// whose layout are `self` followed only by zero or more bytes of trailing
    /// padding (not included in `self`), then unsafe code may rely on
    /// `self.pad_to_align()` producing a layout that correctly
    /// encapsulates the layout of that type.
    ///
    /// We make no guarantees to the behavior of this method if `self` cannot
    /// appear in a valid Rust type (e.g., because the addition of trailing
    /// padding would lead to a size larger than `isize::MAX`).
    #[doc(hidden)]
    #[must_use]
    #[inline]
    pub const fn pad_to_align(self) -> Self {
        use util::padding_needed_for;

        let (static_padding, size_info) = match self.size_info {
            // For sized layouts, we add the minimum amount of trailing padding
            // needed to satisfy alignment.
            SizeInfo::Sized { size: unpadded_size } => {
                let padding = padding_needed_for(unpadded_size, self.align);
                let size = match unpadded_size.checked_add(padding) {
                    Some(size) => size,
                    None => const_panic!("Adding padding caused size to overflow `usize`."),
                };
                (padding, SizeInfo::Sized { size })
            }
            // For DST layouts, trailing padding depends on the length of the
            // trailing DST and is computed at runtime. Normalize the composed
            // rounding operation back into the representation documented on
            // `TrailingSliceLayout`.
            SizeInfo::SliceDst(mut trailing) => {
                if trailing.size_align.get() < self.align.get() {
                    // `self.align` and `trailing.size_align` are powers of two,
                    // so `self.align` is a multiple of `trailing.size_align`.
                    // Rounding
                    //
                    //   size_prefix + round_up(x, size_align)
                    //
                    // to `self.align` is equivalent to rounding
                    //
                    //   round_up(size_prefix, size_align) + x
                    //
                    // directly to `self.align`. Since `size_prefix` is less
                    // than `size_align`, its rounded value is either zero or
                    // `size_align`.
                    let prefix =
                        if trailing.size_prefix == 0 { 0 } else { trailing.size_align.get() };
                    trailing.size_offset = match trailing.size_offset.checked_add(prefix) {
                        Some(offset) => offset,
                        None => const_panic!("Adding padding caused size to overflow `usize`."),
                    };
                    trailing.size_prefix = 0;
                    trailing.size_align = self.align;
                } else {
                    // `trailing.size_align` is a multiple of `self.align`, so
                    // the inner rounded size is already aligned to
                    // `self.align`. Only `size_prefix` needs to be rounded.
                    let padding = padding_needed_for(trailing.size_prefix, self.align);
                    let rounded_prefix = match trailing.size_prefix.checked_add(padding) {
                        Some(prefix) => prefix,
                        None => const_panic!("Adding padding caused size to overflow `usize`."),
                    };
                    #[allow(clippy::arithmetic_side_effects)]
                    let size_prefix = rounded_prefix % trailing.size_align.get();
                    #[allow(clippy::arithmetic_side_effects)]
                    let prefix_multiple = rounded_prefix - size_prefix;
                    trailing.size_offset = match trailing.size_offset.checked_add(prefix_multiple) {
                        Some(offset) => offset,
                        None => {
                            const_panic!("Adding padding caused size to overflow `usize`.")
                        }
                    };
                    trailing.size_prefix = size_prefix;
                }

                (0, SizeInfo::SliceDst(trailing))
            }
        };

        let statically_shallow_unpadded = self.statically_shallow_unpadded && static_padding == 0;

        DstLayout { align: self.align, size_info, statically_shallow_unpadded }
    }

    /// Produces `true` if `self` requires static padding; otherwise `false`.
    #[must_use]
    #[inline(always)]
    pub const fn requires_static_padding(self) -> bool {
        !self.statically_shallow_unpadded
    }

    /// Produces `true` if there exists any metadata for which a type of layout
    /// `self` would require dynamic trailing padding; otherwise `false`.
    #[must_use]
    #[inline(always)]
    pub const fn requires_dynamic_padding(self) -> bool {
        // A `% size_align.get()` cannot panic, since `size_align` is non-zero.
        #[allow(clippy::arithmetic_side_effects)]
        match self.size_info {
            SizeInfo::Sized { .. } => false,
            SizeInfo::SliceDst(trailing_slice_layout) => {
                // SAFETY: This predicate is formally proved sound by
                // `proofs::prove_requires_dynamic_padding`.
                let initial_padding = util::padding_needed_for(
                    trailing_slice_layout.size_offset,
                    trailing_slice_layout.size_align,
                );
                let initial_rounded_size =
                    trailing_slice_layout.size_offset.checked_add(initial_padding);
                let initial_size = match initial_rounded_size {
                    Some(size) => trailing_slice_layout.size_prefix.checked_add(size),
                    None => None,
                };

                match initial_size {
                    Some(initial_size) => {
                        initial_size != trailing_slice_layout.offset
                            || trailing_slice_layout.elem_size
                                % trailing_slice_layout.size_align.get()
                                != 0
                    }
                    None => true,
                }
            }
        }
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
    #[inline(always)]
    pub(crate) const fn validate_cast_and_convert_metadata(
        &self,
        addr: usize,
        bytes_len: usize,
        cast_type: CastType,
    ) -> Result<(usize, usize), MetadataCastError> {
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
        // FIXME(#67): Once our MSRV is 1.65, use let-else:
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
                return Err(MetadataCastError::Alignment);
            }
        }

        let (elems, self_bytes) = match size_info {
            SizeInfo::Sized { size } => {
                if size > bytes_len {
                    return Err(MetadataCastError::Size);
                }
                (0, size)
            }
            SizeInfo::SliceDst(TrailingSliceLayout {
                elem_size,
                size_prefix,
                size_offset,
                size_align,
                ..
            }) => {
                let bytes_after_prefix = match bytes_len.checked_sub(size_prefix) {
                    Some(bytes) => bytes,
                    None => return Err(MetadataCastError::Size),
                };
                // The inner portion of every valid size is a multiple of
                // `size_align`. Round the available bytes down to the largest
                // such multiple.
                let max_rounded_bytes =
                    util::round_down_to_next_multiple_of_alignment(bytes_after_prefix, size_align);
                // Calculate the maximum number of bytes that could be consumed
                // by the trailing slice.
                //
                // FIXME(#67): Once our MSRV is 1.65, use let-else:
                // https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html#let-else-statements
                let max_slice_and_padding_bytes = match max_rounded_bytes.checked_sub(size_offset) {
                    Some(max) => max,
                    // `bytes_len` too small even for 0 trailing slice elements.
                    None => return Err(MetadataCastError::Size),
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
                // - max_slice_and_padding_bytes == max_rounded_bytes - size_offset
                // - elems * elem_size <= max_slice_and_padding_bytes
                // - elems * elem_size + size_offset <= max_rounded_bytes
                #[allow(clippy::arithmetic_side_effects)]
                let without_padding = size_offset + elems * elem_size.get();
                // `self_bytes` is equal to the offset bytes plus the bytes
                // consumed by the trailing slice plus any padding bytes
                // required to satisfy the alignment. Note that we have computed
                // the maximum number of trailing slice elements that could fit
                // in `self_bytes`, so any padding is guaranteed to be less than
                // the size of an extra element.
                //
                // Guaranteed not to overflow:
                // - By previous comment: without_padding <= max_rounded_bytes
                // - By construction, `max_rounded_bytes` is a multiple of
                //   `size_align`.
                // - At most, adding padding needed to round `without_padding`
                //   up to the next multiple of `size_align` will bring the
                //   rounded size up to `max_rounded_bytes`.
                #[allow(clippy::arithmetic_side_effects)]
                let rounded =
                    without_padding + util::padding_needed_for(without_padding, size_align);
                // `rounded <= max_rounded_bytes <= bytes_after_prefix`, so
                // adding `size_prefix` cannot overflow and cannot exceed
                // `bytes_len`.
                #[allow(clippy::arithmetic_side_effects)]
                let self_bytes = size_prefix + rounded;
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
            //   bytes_len`.
            #[allow(clippy::arithmetic_side_effects)]
            CastType::Suffix => bytes_len - self_bytes,
        };

        Ok((elems, split_at))
    }
}

pub(crate) use cast_from::CastFrom;
mod cast_from {
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
                //   d_meta = OFFSET_DELTA_ELEMS + s_meta * ELEM_MULTIPLE
                //
                // `ELEM_MULTIPLE` scales the destination's trailing element
                // size to the source's. `OFFSET_DELTA_ELEMS` selects a
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
                /// Returns whether mapping source metadata `n` to destination
                /// metadata `dst_base + n * (src.elem_size / dst.elem_size)`
                /// preserves object size for every `n`.
                const fn size_sequences_match(
                    src: TrailingSliceLayout,
                    dst: TrailingSliceLayout,
                    dst_base: usize,
                ) -> bool {
                    let base_bytes = match dst_base.checked_mul(dst.elem_size) {
                        Some(bytes) => bytes,
                        None => return false,
                    };
                    let size_offset = match dst.size_offset.checked_add(base_bytes) {
                        Some(offset) => offset,
                        None => return false,
                    };
                    let shifted_dst = TrailingSliceLayout {
                        offset: dst.offset,
                        elem_size: src.elem_size,
                        size_prefix: dst.size_prefix,
                        size_offset,
                        size_align: dst.size_align,
                    };
                    src.has_same_size_sequence(shifted_dst)
                }

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
                            let dst_meta = match dst.metadata_for_exact_size(src_size) {
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

                            // PANICS: `dst_elem_size: NonZeroUsize`, so this won't
                            // divide by zero.
                            #[allow(clippy::arithmetic_side_effects)]
                            let elem_remainder = src.elem_size % dst_elem_size.get();

                            if src.elem_size < dst.elem_size || elem_remainder != 0 {
                                return None;
                            }

                            // PANICS: `dst_elem_size: NonZeroUsize`, so this won't
                            // divide by zero.
                            #[allow(clippy::arithmetic_side_effects)]
                            let elem_multiple = src.elem_size / dst_elem_size.get();

                            // Prefer the old exact-inner-offset solution. In
                            // addition to preserving existing accepted casts,
                            // it avoids selecting another metadata value from a
                            // rounding plateau when that value would have a
                            // different future padding sequence.
                            let exact_offset_delta_elems =
                                match src.size_offset.checked_sub(dst.size_offset) {
                                    Some(delta) => {
                                        #[allow(clippy::arithmetic_side_effects)]
                                        let remainder = delta % dst_elem_size.get();
                                        if remainder == 0 {
                                            #[allow(clippy::arithmetic_side_effects)]
                                            let elems = delta / dst_elem_size.get();
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
                                    let elems = match dst.metadata_for_exact_size(src_zero_size) {
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
                            // SAFETY: `self` witnesses that this affine map
                            // makes `Src` and `Dst`'s complete rounded size
                            // formulas equal for every source metadata value.
                            // Since the caller promises that `src_meta` is
                            // valid `Src` metadata, `src_meta * S_ELEM <=
                            // size_of_val(src) <= isize::MAX`. Since
                            // `elem_multiple = S_ELEM / D_ELEM` and
                            // `D_ELEM >= 1`, the multiplication below cannot
                            // overflow. Sequence equality then gives
                            // `(offset_delta_elems + src_meta *
                            // elem_multiple) * D_ELEM <= size_of_val(src)`, so
                            // the addition cannot overflow either. The
                            // returned metadata therefore describes a `Dst`
                            // of the same size.
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
}

// FIXME(#67): For some reason, on our MSRV toolchain, this `allow` isn't
// enforced despite having `#![allow(unknown_lints)]` at the crate root, but
// putting it here works. Once our MSRV is high enough that this bug has been
// fixed, remove this `allow`.
#[allow(unknown_lints)]
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dst_layout_for_slice() {
        let layout = DstLayout::for_slice::<u32>();
        match layout.size_info {
            SizeInfo::SliceDst(TrailingSliceLayout { offset, elem_size, .. }) => {
                assert_eq!(offset, 0);
                assert_eq!(elem_size, 4);
            }
            _ => panic!("Expected SliceDst"),
        }
        assert_eq!(layout.align.get(), 4);
    }

    /// Tests of when a sized `DstLayout` is extended with a sized field.
    #[allow(clippy::decimal_literal_representation)]
    #[test]
    fn test_dst_layout_extend_sized_with_sized() {
        // This macro constructs a layout corresponding to a `u8` and extends it
        // with a zero-sized trailing field of given alignment `n`. The macro
        // tests that the resulting layout has both size and alignment `min(n,
        // P)` for all valid values of `repr(packed(P))`.
        macro_rules! test_align_is_size {
            ($n:expr) => {
                let base = DstLayout::for_type::<u8>();
                let trailing_field = DstLayout::for_type::<elain::Align<$n>>();

                let packs =
                    core::iter::once(None).chain((0..29).map(|p| NonZeroUsize::new(2usize.pow(p))));

                for pack in packs {
                    let composite = base.extend(trailing_field, pack);
                    let max_align = pack.unwrap_or(DstLayout::CURRENT_MAX_ALIGN);
                    let align = $n.min(max_align.get());
                    assert_eq!(
                        composite,
                        DstLayout {
                            align: NonZeroUsize::new(align).unwrap(),
                            size_info: SizeInfo::Sized { size: align },
                            statically_shallow_unpadded: false,
                        }
                    )
                }
            };
        }

        test_align_is_size!(1);
        test_align_is_size!(2);
        test_align_is_size!(4);
        test_align_is_size!(8);
        test_align_is_size!(16);
        test_align_is_size!(32);
        test_align_is_size!(64);
        test_align_is_size!(128);
        test_align_is_size!(256);
        test_align_is_size!(512);
        test_align_is_size!(1024);
        test_align_is_size!(2048);
        test_align_is_size!(4096);
        test_align_is_size!(8192);
        test_align_is_size!(16384);
        test_align_is_size!(32768);
        test_align_is_size!(65536);
        test_align_is_size!(131072);
        test_align_is_size!(262144);
        test_align_is_size!(524288);
        test_align_is_size!(1048576);
        test_align_is_size!(2097152);
        test_align_is_size!(4194304);
        test_align_is_size!(8388608);
        test_align_is_size!(16777216);
        test_align_is_size!(33554432);
        test_align_is_size!(67108864);
        test_align_is_size!(33554432);
        test_align_is_size!(134217728);
        test_align_is_size!(268435456);
    }

    /// Tests of when a sized `DstLayout` is extended with a DST field.
    #[test]
    fn test_dst_layout_extend_sized_with_dst() {
        // Test that for all combinations of real-world alignments and
        // `repr_packed` values, that the extension of a sized `DstLayout`` with
        // a DST field correctly computes the trailing offset in the composite
        // layout.

        let aligns = (0..29).map(|p| NonZeroUsize::new(2usize.pow(p)).unwrap());
        let packs = core::iter::once(None).chain(aligns.clone().map(Some));

        for field_type_align in aligns {
            for pack in packs.clone() {
                let base = DstLayout::for_type::<u8>();
                let elem_size = 42;
                let trailing_field_offset = 11;

                let trailing_field = DstLayout {
                    align: field_type_align,
                    size_info: SizeInfo::SliceDst(TrailingSliceLayout {
                        elem_size,
                        offset: trailing_field_offset,
                        size_prefix: 0,
                        size_offset: trailing_field_offset,
                        size_align: field_type_align,
                    }),
                    statically_shallow_unpadded: false,
                };

                let composite = base.extend(trailing_field, pack);

                let max_align = pack.unwrap_or(DstLayout::CURRENT_MAX_ALIGN).get();

                let align = field_type_align.get().min(max_align);
                let field_offset = align;
                let size_prefix = field_offset % field_type_align.get();
                let size_offset = field_offset - size_prefix + trailing_field_offset;

                assert_eq!(
                    composite,
                    DstLayout {
                        align: NonZeroUsize::new(align).unwrap(),
                        size_info: SizeInfo::SliceDst(TrailingSliceLayout {
                            elem_size,
                            offset: field_offset + trailing_field_offset,
                            size_prefix,
                            size_offset,
                            size_align: field_type_align,
                        }),
                        statically_shallow_unpadded: false,
                    }
                )
            }
        }
    }

    /// Tests that calling `pad_to_align` on a sized `DstLayout` adds the
    /// expected amount of trailing padding.
    #[test]
    fn test_dst_layout_pad_to_align_with_sized() {
        // For all valid alignments `align`, construct a one-byte layout aligned
        // to `align`, call `pad_to_align`, and assert that the size of the
        // resulting layout is equal to `align`.
        for align in (0..29).map(|p| NonZeroUsize::new(2usize.pow(p)).unwrap()) {
            let layout = DstLayout {
                align,
                size_info: SizeInfo::Sized { size: 1 },
                statically_shallow_unpadded: true,
            };

            assert_eq!(
                layout.pad_to_align(),
                DstLayout {
                    align,
                    size_info: SizeInfo::Sized { size: align.get() },
                    statically_shallow_unpadded: align.get() == 1
                }
            );
        }

        // Test explicitly-provided combinations of unpadded and padded
        // counterparts.

        macro_rules! test {
            (unpadded { size: $unpadded_size:expr, align: $unpadded_align:expr }
                    => padded { size: $padded_size:expr, align: $padded_align:expr }) => {
                let unpadded = DstLayout {
                    align: NonZeroUsize::new($unpadded_align).unwrap(),
                    size_info: SizeInfo::Sized { size: $unpadded_size },
                    statically_shallow_unpadded: false,
                };
                let padded = unpadded.pad_to_align();

                assert_eq!(
                    padded,
                    DstLayout {
                        align: NonZeroUsize::new($padded_align).unwrap(),
                        size_info: SizeInfo::Sized { size: $padded_size },
                        statically_shallow_unpadded: false,
                    }
                );
            };
        }

        test!(unpadded { size: 0, align: 4 } => padded { size: 0, align: 4 });
        test!(unpadded { size: 1, align: 4 } => padded { size: 4, align: 4 });
        test!(unpadded { size: 2, align: 4 } => padded { size: 4, align: 4 });
        test!(unpadded { size: 3, align: 4 } => padded { size: 4, align: 4 });
        test!(unpadded { size: 4, align: 4 } => padded { size: 4, align: 4 });
        test!(unpadded { size: 5, align: 4 } => padded { size: 8, align: 4 });
        test!(unpadded { size: 6, align: 4 } => padded { size: 8, align: 4 });
        test!(unpadded { size: 7, align: 4 } => padded { size: 8, align: 4 });
        test!(unpadded { size: 8, align: 4 } => padded { size: 8, align: 4 });

        let current_max_align = DstLayout::CURRENT_MAX_ALIGN.get();

        test!(unpadded { size: 1, align: current_max_align }
                => padded { size: current_max_align, align: current_max_align });

        test!(unpadded { size: current_max_align + 1, align: current_max_align }
                => padded { size: current_max_align * 2, align: current_max_align });
    }

    /// Tests that calling `pad_to_align` on a DST `DstLayout` incorporates the
    /// type's trailing-padding operation into its runtime size formula.
    #[test]
    fn test_dst_layout_pad_to_align_with_dst() {
        for align in (0..29).map(|p| NonZeroUsize::new(2usize.pow(p)).unwrap()) {
            for offset in 0..10 {
                for elem_size in 0..10 {
                    let layout = DstLayout {
                        align,
                        size_info: SizeInfo::SliceDst(TrailingSliceLayout {
                            offset,
                            elem_size,
                            size_prefix: 0,
                            size_offset: offset,
                            size_align: DstLayout::MIN_ALIGN,
                        }),
                        statically_shallow_unpadded: false,
                    };
                    assert_eq!(
                        layout.pad_to_align(),
                        DstLayout {
                            align,
                            size_info: SizeInfo::SliceDst(TrailingSliceLayout {
                                offset,
                                elem_size,
                                size_prefix: 0,
                                size_offset: offset,
                                size_align: align,
                            }),
                            statically_shallow_unpadded: false,
                        }
                    );
                }
            }
        }
    }

    #[test]
    fn test_trailing_slice_layout_size_sequence_equivalence() {
        // These are the two normalized descriptions produced by a
        // `repr(C, packed(2))` wrapper around slice DSTs whose element types
        // both have size four but alignments four and two respectively. Their
        // formulas differ structurally, but both simplify to `2 + 4 * elems`.
        let align4 = TrailingSliceLayout {
            offset: 2,
            elem_size: 4,
            size_prefix: 2,
            size_offset: 0,
            size_align: NonZeroUsize::new(4).unwrap(),
        };
        let align2 = TrailingSliceLayout {
            offset: 2,
            elem_size: 4,
            size_prefix: 0,
            size_offset: 2,
            size_align: NonZeroUsize::new(2).unwrap(),
        };
        assert!(align4.has_same_size_sequence(align2));
        for elems in 0..8 {
            assert_eq!(align4.size_for_elems(elems), Some(2 + 4 * elems));
            assert_eq!(align4.size_for_elems(elems), align2.size_for_elems(elems));
        }

        let dynamically_padded = TrailingSliceLayout { elem_size: 1, ..align4 };
        assert!(!dynamically_padded.has_same_size_sequence(align2));
    }

    // This test takes a long time when running under Miri, so we skip it in
    // that case. This is acceptable because this is a logic test that doesn't
    // attempt to expose UB.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_validate_cast_and_convert_metadata() {
        #[allow(non_local_definitions)]
        impl From<usize> for SizeInfo {
            fn from(size: usize) -> SizeInfo {
                SizeInfo::Sized { size }
            }
        }

        #[allow(non_local_definitions)]
        impl From<(usize, usize)> for SizeInfo {
            fn from((offset, elem_size): (usize, usize)) -> SizeInfo {
                SizeInfo::SliceDst(TrailingSliceLayout {
                    offset,
                    elem_size,
                    size_prefix: 0,
                    size_offset: offset,
                    size_align: DstLayout::MIN_ALIGN,
                })
            }
        }

        fn layout<S: Into<SizeInfo>>(s: S, align: usize) -> DstLayout {
            let align = NonZeroUsize::new(align).unwrap();
            let size_info = match s.into() {
                SizeInfo::SliceDst(mut trailing) => {
                    trailing.size_align = align;
                    SizeInfo::SliceDst(trailing)
                }
                size_info => size_info,
            };
            DstLayout { size_info, align, statically_shallow_unpadded: false }
        }

        /// This macro accepts arguments in the form of:
        ///
        ///           layout(_, _).validate(_, _, _), Ok(Some((_, _)))
        ///                  |  |           |  |  |            |  |
        ///    size ---------+  |           |  |  |            |  |
        ///    align -----------+           |  |  |            |  |
        ///    addr ------------------------+  |  |            |  |
        ///    bytes_len ----------------------+  |            |  |
        ///    cast_type -------------------------+            |  |
        ///    elems ------------------------------------------+  |
        ///    split_at ------------------------------------------+
        ///
        /// `.validate` is shorthand for `.validate_cast_and_convert_metadata`
        /// for brevity.
        ///
        /// Each argument can either be an iterator or a wildcard. Each
        /// wildcarded variable is implicitly replaced by an iterator over a
        /// representative sample of values for that variable. Each `test!`
        /// invocation iterates over every combination of values provided by
        /// each variable's iterator (ie, the cartesian product) and validates
        /// that the results are expected.
        ///
        /// The final argument uses the same syntax, but it has a different
        /// meaning:
        /// - If it is `Ok(pat)`, then the pattern `pat` is supplied to
        ///   a matching assert to validate the computed result for each
        ///   combination of input values.
        /// - If it is `Err(Some(msg) | None)`, then `test!` validates that the
        ///   call to `validate_cast_and_convert_metadata` panics with the given
        ///   panic message or, if the current Rust toolchain version is too
        ///   early to support panicking in `const fn`s, panics with *some*
        ///   message. In the latter case, the `const_panic!` macro is used,
        ///   which emits code which causes a non-panicking error at const eval
        ///   time, but which does panic when invoked at runtime. Thus, it is
        ///   merely difficult to predict the *value* of this panic. We deem
        ///   that testing against the real panic strings on stable and nightly
        ///   toolchains is enough to ensure correctness.
        ///
        /// Note that the meta-variables that match these variables have the
        /// `tt` type, and some valid expressions are not valid `tt`s (such as
        /// `a..b`). In this case, wrap the expression in parentheses, and it
        /// will become valid `tt`.
        macro_rules! test {
                (
                    layout($size:tt, $align:tt)
                    .validate($addr:tt, $bytes_len:tt, $cast_type:tt), $expect:pat $(,)?
                ) => {
                    itertools::iproduct!(
                        test!(@generate_size $size),
                        test!(@generate_align $align),
                        test!(@generate_usize $addr),
                        test!(@generate_usize $bytes_len),
                        test!(@generate_cast_type $cast_type)
                    ).for_each(|(size_info, align, addr, bytes_len, cast_type)| {
                        // Temporarily disable the panic hook installed by the test
                        // harness. If we don't do this, all panic messages will be
                        // kept in an internal log. On its own, this isn't a
                        // problem, but if a non-caught panic ever happens (ie, in
                        // code later in this test not in this macro), all of the
                        // previously-buffered messages will be dumped, hiding the
                        // real culprit.
                        let previous_hook = std::panic::take_hook();
                        // I don't understand why, but this seems to be required in
                        // addition to the previous line.
                        std::panic::set_hook(Box::new(|_| {}));
                        let actual = std::panic::catch_unwind(|| {
                            layout(size_info, align).validate_cast_and_convert_metadata(addr, bytes_len, cast_type)
                        }).map_err(|d| {
                            let msg = d.downcast::<&'static str>().ok().map(|s| *s.as_ref());
                            assert!(msg.is_some() || cfg!(no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0), "non-string panic messages are not permitted when usage of panic in const fn is enabled");
                            msg
                        });
                        std::panic::set_hook(previous_hook);

                        assert!(
                            matches!(actual, $expect),
                            "layout({:?}, {}).validate_cast_and_convert_metadata({}, {}, {:?})" ,size_info, align, addr, bytes_len, cast_type
                        );
                    });
                };
                (@generate_usize _) => { 0..8 };
                // Generate sizes for both Sized and !Sized types.
                (@generate_size _) => {
                    test!(@generate_size (_)).chain(test!(@generate_size (_, _)))
                };
                // Generate sizes for both Sized and !Sized types by chaining
                // specified iterators for each.
                (@generate_size ($sized_sizes:tt | $unsized_sizes:tt)) => {
                    test!(@generate_size ($sized_sizes)).chain(test!(@generate_size $unsized_sizes))
                };
                // Generate sizes for Sized types.
                (@generate_size (_)) => { test!(@generate_size (0..8)) };
                (@generate_size ($sizes:expr)) => { $sizes.into_iter().map(Into::<SizeInfo>::into) };
                // Generate sizes for !Sized types.
                (@generate_size ($min_sizes:tt, $elem_sizes:tt)) => {
                    itertools::iproduct!(
                        test!(@generate_min_size $min_sizes),
                        test!(@generate_elem_size $elem_sizes)
                    ).map(Into::<SizeInfo>::into)
                };
                (@generate_fixed_size _) => { (0..8).into_iter().map(Into::<SizeInfo>::into) };
                (@generate_min_size _) => { 0..8 };
                (@generate_elem_size _) => { 1..8 };
                (@generate_align _) => { [1, 2, 4, 8, 16] };
                (@generate_opt_usize _) => { [None].into_iter().chain((0..8).map(Some).into_iter()) };
                (@generate_cast_type _) => { [CastType::Prefix, CastType::Suffix] };
                (@generate_cast_type $variant:ident) => { [CastType::$variant] };
                // Some expressions need to be wrapped in parentheses in order to be
                // valid `tt`s (required by the top match pattern). See the comment
                // below for more details. This arm removes these parentheses to
                // avoid generating an `unused_parens` warning.
                (@$_:ident ($vals:expr)) => { $vals };
                (@$_:ident $vals:expr) => { $vals };
            }

        const EVENS: [usize; 8] = [0, 2, 4, 6, 8, 10, 12, 14];
        const ODDS: [usize; 8] = [1, 3, 5, 7, 9, 11, 13, 15];

        // base_size is too big for the memory region.
        test!(
            layout(((1..8) | ((1..8), (1..8))), _).validate([0], [0], _),
            Ok(Err(MetadataCastError::Size))
        );
        test!(
            layout(((2..8) | ((2..8), (2..8))), _).validate([0], [1], Prefix),
            Ok(Err(MetadataCastError::Size))
        );
        test!(
            layout(((2..8) | ((2..8), (2..8))), _).validate([0x1000_0000 - 1], [1], Suffix),
            Ok(Err(MetadataCastError::Size))
        );

        // addr is unaligned for prefix cast
        test!(layout(_, [2]).validate(ODDS, _, Prefix), Ok(Err(MetadataCastError::Alignment)));
        test!(layout(_, [2]).validate(ODDS, _, Prefix), Ok(Err(MetadataCastError::Alignment)));

        // addr is aligned, but end of buffer is unaligned for suffix cast
        test!(layout(_, [2]).validate(EVENS, ODDS, Suffix), Ok(Err(MetadataCastError::Alignment)));
        test!(layout(_, [2]).validate(EVENS, ODDS, Suffix), Ok(Err(MetadataCastError::Alignment)));

        // Unfortunately, these constants cannot easily be used in the
        // implementation of `validate_cast_and_convert_metadata`, since
        // `panic!` consumes a string literal, not an expression.
        //
        // It's important that these messages be in a separate module. If they
        // were at the function's top level, we'd pass them to `test!` as, e.g.,
        // `Err(TRAILING)`, which would run into a subtle Rust footgun - the
        // `TRAILING` identifier would be treated as a pattern to match rather
        // than a value to check for equality.
        mod msgs {
            pub(super) const TRAILING: &str =
                "attempted to cast to slice type with zero-sized element";
            pub(super) const OVERFLOW: &str = "`addr` + `bytes_len` > usize::MAX";
        }

        // casts with ZST trailing element types are unsupported
        test!(layout((_, [0]), _).validate(_, _, _), Err(Some(msgs::TRAILING) | None),);

        // addr + bytes_len must not overflow usize
        test!(layout(_, _).validate([usize::MAX], (1..100), _), Err(Some(msgs::OVERFLOW) | None));
        test!(layout(_, _).validate((1..100), [usize::MAX], _), Err(Some(msgs::OVERFLOW) | None));
        test!(
            layout(_, _).validate(
                [usize::MAX / 2 + 1, usize::MAX],
                [usize::MAX / 2 + 1, usize::MAX],
                _
            ),
            Err(Some(msgs::OVERFLOW) | None)
        );

        // Validates that `validate_cast_and_convert_metadata` satisfies its own
        // documented safety postconditions, and also a few other properties
        // that aren't documented but we want to guarantee anyway.
        fn validate_behavior(
            (layout, addr, bytes_len, cast_type): (DstLayout, usize, usize, CastType),
        ) {
            if let Ok((elems, split_at)) =
                layout.validate_cast_and_convert_metadata(addr, bytes_len, cast_type)
            {
                let (size_info, align) = (layout.size_info, layout.align);
                let debug_str = format!(
                    "layout({:?}, {}).validate_cast_and_convert_metadata({}, {}, {:?}) => ({}, {})",
                    size_info, align, addr, bytes_len, cast_type, elems, split_at
                );

                // If this is a sized type (no trailing slice), then `elems` is
                // meaningless, but in practice we set it to 0. Callers are not
                // allowed to rely on this, but a lot of math is nicer if
                // they're able to, and some callers might accidentally do that.
                let sized = matches!(layout.size_info, SizeInfo::Sized { .. });
                assert!(!(sized && elems != 0), "{}", debug_str);

                let resulting_size = match layout.size_info {
                    SizeInfo::Sized { size } => size,
                    SizeInfo::SliceDst(TrailingSliceLayout {
                        elem_size,
                        size_prefix,
                        size_offset,
                        size_align,
                        ..
                    }) => {
                        let padded_size = |elems| {
                            let without_padding = size_offset + elems * elem_size;
                            size_prefix
                                + without_padding
                                + util::padding_needed_for(without_padding, size_align)
                        };

                        let resulting_size = padded_size(elems);
                        // Test that `validate_cast_and_convert_metadata`
                        // computed the largest possible value that fits in the
                        // given range.
                        assert!(padded_size(elems + 1) > bytes_len, "{}", debug_str);
                        resulting_size
                    }
                };

                // Test safety postconditions guaranteed by
                // `validate_cast_and_convert_metadata`.
                assert!(resulting_size <= bytes_len, "{}", debug_str);
                match cast_type {
                    CastType::Prefix => {
                        assert_eq!(addr % align, 0, "{}", debug_str);
                        assert_eq!(resulting_size, split_at, "{}", debug_str);
                    }
                    CastType::Suffix => {
                        assert_eq!(split_at, bytes_len - resulting_size, "{}", debug_str);
                        assert_eq!((addr + split_at) % align, 0, "{}", debug_str);
                    }
                }
            } else {
                let min_size = match layout.size_info {
                    SizeInfo::Sized { size } => size,
                    SizeInfo::SliceDst(TrailingSliceLayout {
                        size_prefix,
                        size_offset,
                        size_align,
                        ..
                    }) => {
                        size_prefix
                            + size_offset
                            + util::padding_needed_for(size_offset, size_align)
                    }
                };

                // If a cast is invalid, it is either because...
                // 1. there are insufficient bytes at the given region for type:
                let insufficient_bytes = bytes_len < min_size;
                // 2. performing the cast would misalign type:
                let base = match cast_type {
                    CastType::Prefix => 0,
                    CastType::Suffix => bytes_len,
                };
                let misaligned = (base + addr) % layout.align != 0;

                assert!(insufficient_bytes || misaligned);
            }
        }

        let sizes = 0..8;
        let elem_sizes = 1..8;
        let size_infos = sizes
            .clone()
            .map(Into::<SizeInfo>::into)
            .chain(itertools::iproduct!(sizes, elem_sizes).map(Into::<SizeInfo>::into));
        let layouts = itertools::iproduct!(size_infos, [1, 2, 4, 8, 16, 32])
                .filter(|(size_info, align)| !matches!(size_info, SizeInfo::Sized { size } if size % align != 0))
                .map(|(size_info, align)| layout(size_info, align));
        itertools::iproduct!(layouts, 0..8, 0..8, [CastType::Prefix, CastType::Suffix])
            .for_each(validate_behavior);

        // Exercise a normalized formula which cannot be represented as
        // `round_up(offset + elems * elem_size, align)`: the physical trailing
        // slice begins at offset 7, while an inner aligned DST contributes the
        // size formula `2 + round_up(5 + elems, 4)` to a packed outer type.
        let nested_packed = DstLayout {
            align: NonZeroUsize::new(2).unwrap(),
            size_info: SizeInfo::SliceDst(TrailingSliceLayout {
                offset: 7,
                elem_size: 1,
                size_prefix: 2,
                size_offset: 5,
                size_align: NonZeroUsize::new(4).unwrap(),
            }),
            statically_shallow_unpadded: false,
        };
        itertools::iproduct!([nested_packed], 0..8, 0..24, [CastType::Prefix, CastType::Suffix])
            .for_each(validate_behavior);

        assert!(matches!(
            nested_packed.validate_cast_and_convert_metadata(0, 8, CastType::Prefix),
            Err(MetadataCastError::Size)
        ));
        assert!(matches!(
            nested_packed.validate_cast_and_convert_metadata(0, 10, CastType::Prefix),
            Ok((3, 10))
        ));
    }

    #[test]
    #[cfg(__ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS)]
    fn test_validate_rust_layout() {
        use core::{
            convert::TryInto as _,
            ptr::{self, NonNull},
        };

        use crate::util::testutil::*;

        // This test synthesizes pointers with various metadata and uses Rust's
        // built-in APIs to confirm that Rust makes decisions about type layout
        // which are consistent with what we believe is guaranteed by the
        // language. If this test fails, it doesn't just mean our code is wrong
        // - it means we're misunderstanding the language's guarantees.

        #[derive(Debug)]
        struct MacroArgs {
            offset: usize,
            align: NonZeroUsize,
            elem_size: Option<usize>,
        }

        /// # Safety
        ///
        /// `test` promises to only call `addr_of_slice_field` on a `NonNull<T>`
        /// which points to a valid `T`.
        ///
        /// `with_elems` must produce a pointer which points to a valid `T`.
        fn test<T: ?Sized, W: Fn(usize) -> NonNull<T>>(
            args: MacroArgs,
            with_elems: W,
            addr_of_slice_field: Option<fn(NonNull<T>) -> NonNull<u8>>,
        ) {
            let dst = args.elem_size.is_some();
            let layout = {
                let size_info = match args.elem_size {
                    Some(elem_size) => SizeInfo::SliceDst(TrailingSliceLayout {
                        offset: args.offset,
                        elem_size,
                        size_prefix: 0,
                        size_offset: args.offset,
                        size_align: args.align,
                    }),
                    None => SizeInfo::Sized {
                        // Rust only supports types whose sizes are a multiple
                        // of their alignment. If the macro created a type like
                        // this:
                        //
                        //   #[repr(C, align(2))]
                        //   struct Foo([u8; 1]);
                        //
                        // ...then Rust will automatically round the type's size
                        // up to 2.
                        size: args.offset + util::padding_needed_for(args.offset, args.align),
                    },
                };
                DstLayout { size_info, align: args.align, statically_shallow_unpadded: false }
            };

            for elems in 0..128 {
                let ptr = with_elems(elems);

                if let Some(addr_of_slice_field) = addr_of_slice_field {
                    let slc_field_ptr = addr_of_slice_field(ptr).as_ptr();
                    // SAFETY: Both `slc_field_ptr` and `ptr` are pointers to
                    // the same valid Rust object.
                    // Work around https://github.com/rust-lang/rust-clippy/issues/12280
                    let offset: usize =
                        unsafe { slc_field_ptr.byte_offset_from(ptr.as_ptr()).try_into().unwrap() };
                    assert_eq!(offset, args.offset);
                }

                // SAFETY: `ptr` points to a valid `T`.
                #[allow(clippy::multiple_unsafe_ops_per_block)]
                let (size, align) = unsafe {
                    (mem::size_of_val_raw(ptr.as_ptr()), mem::align_of_val_raw(ptr.as_ptr()))
                };

                // Avoid expensive allocation when running under Miri.
                let assert_msg = if !cfg!(miri) {
                    format!("\n{:?}\nsize:{}, align:{}", args, size, align)
                } else {
                    String::new()
                };

                let without_padding =
                    args.offset + args.elem_size.map(|elem_size| elems * elem_size).unwrap_or(0);
                assert!(size >= without_padding, "{}", assert_msg);
                assert_eq!(align, args.align.get(), "{}", assert_msg);

                // This encodes the most important part of the test: our
                // understanding of how Rust determines the layout of repr(C)
                // types. Sized repr(C) types are trivial, but DST types have
                // some subtlety. Note that:
                // - For sized types, `without_padding` is just the size of the
                //   type that we constructed for `Foo`. Since we may have
                //   requested a larger alignment, `Foo` may actually be larger
                //   than this, hence `padding_needed_for`.
                // - For unsized types, `without_padding` is dynamically
                //   computed from the offset, the element size, and element
                //   count. We expect that the size of the object should be
                //   `offset + elem_size * elems` rounded up to the next
                //   alignment.
                let expected_size =
                    without_padding + util::padding_needed_for(without_padding, args.align);
                assert_eq!(expected_size, size, "{}", assert_msg);

                // For zero-sized element types,
                // `validate_cast_and_convert_metadata` just panics, so we skip
                // testing those types.
                if args.elem_size.map(|elem_size| elem_size > 0).unwrap_or(true) {
                    let addr = ptr.addr().get();
                    let (got_elems, got_split_at) = layout
                        .validate_cast_and_convert_metadata(addr, size, CastType::Prefix)
                        .unwrap();
                    // Avoid expensive allocation when running under Miri.
                    let assert_msg = if !cfg!(miri) {
                        format!(
                            "{}\nvalidate_cast_and_convert_metadata({}, {})",
                            assert_msg, addr, size,
                        )
                    } else {
                        String::new()
                    };
                    assert_eq!(got_split_at, size, "{}", assert_msg);
                    if dst {
                        assert!(got_elems >= elems, "{}", assert_msg);
                        if got_elems != elems {
                            // If `validate_cast_and_convert_metadata`
                            // returned more elements than `elems`, that
                            // means that `elems` is not the maximum number
                            // of elements that can fit in `size` - in other
                            // words, there is enough padding at the end of
                            // the value to fit at least one more element.
                            // If we use this metadata to synthesize a
                            // pointer, despite having a different element
                            // count, we still expect it to have the same
                            // size.
                            let got_ptr = with_elems(got_elems);
                            // SAFETY: `got_ptr` is a pointer to a valid `T`.
                            let size_of_got_ptr = unsafe { mem::size_of_val_raw(got_ptr.as_ptr()) };
                            assert_eq!(size_of_got_ptr, size, "{}", assert_msg);
                        }
                    } else {
                        // For sized casts, the returned element value is
                        // technically meaningless, and we don't guarantee any
                        // particular value. In practice, it's always zero.
                        assert_eq!(got_elems, 0, "{}", assert_msg)
                    }
                }
            }
        }

        macro_rules! validate_against_rust {
                ($offset:literal, $align:literal $(, $elem_size:literal)?) => {{
                    #[repr(C, align($align))]
                    struct Foo([u8; $offset]$(, [[u8; $elem_size]])?);

                    let args = MacroArgs {
                        offset: $offset,
                        align: $align.try_into().unwrap(),
                        elem_size: {
                            #[allow(unused)]
                            let ret = None::<usize>;
                            $(let ret = Some($elem_size);)?
                            ret
                        }
                    };

                    #[repr(C, align($align))]
                    struct FooAlign;
                    // Create an aligned buffer to use in order to synthesize
                    // pointers to `Foo`. We don't ever load values from these
                    // pointers - we just do arithmetic on them - so having a "real"
                    // block of memory as opposed to a validly-aligned-but-dangling
                    // pointer is only necessary to make Miri happy since we run it
                    // with "strict provenance" checking enabled.
                    let aligned_buf = Align::<_, FooAlign>::new([0u8; 1024]);
                    let with_elems = |elems| {
                        let slc = NonNull::slice_from_raw_parts(NonNull::from(&aligned_buf.t), elems);
                        #[allow(clippy::as_conversions)]
                        NonNull::new(slc.as_ptr() as *mut Foo).unwrap()
                    };
                    let addr_of_slice_field = {
                        #[allow(unused)]
                        let f = None::<fn(NonNull<Foo>) -> NonNull<u8>>;
                        $(
                            // SAFETY: `test` promises to only call `f` with a `ptr`
                            // to a valid `Foo`.
                            let f: Option<fn(NonNull<Foo>) -> NonNull<u8>> = Some(|ptr: NonNull<Foo>| unsafe {
                                NonNull::new(ptr::addr_of_mut!((*ptr.as_ptr()).1)).unwrap().cast::<u8>()
                            });
                            let _ = $elem_size;
                        )?
                        f
                    };

                    test::<Foo, _>(args, with_elems, addr_of_slice_field);
                }};
            }

        // Every permutation of:
        // - offset in [0, 4]
        // - align in [1, 16]
        // - elem_size in [0, 4] (plus no elem_size)
        validate_against_rust!(0, 1);
        validate_against_rust!(0, 1, 0);
        validate_against_rust!(0, 1, 1);
        validate_against_rust!(0, 1, 2);
        validate_against_rust!(0, 1, 3);
        validate_against_rust!(0, 1, 4);
        validate_against_rust!(0, 2);
        validate_against_rust!(0, 2, 0);
        validate_against_rust!(0, 2, 1);
        validate_against_rust!(0, 2, 2);
        validate_against_rust!(0, 2, 3);
        validate_against_rust!(0, 2, 4);
        validate_against_rust!(0, 4);
        validate_against_rust!(0, 4, 0);
        validate_against_rust!(0, 4, 1);
        validate_against_rust!(0, 4, 2);
        validate_against_rust!(0, 4, 3);
        validate_against_rust!(0, 4, 4);
        validate_against_rust!(0, 8);
        validate_against_rust!(0, 8, 0);
        validate_against_rust!(0, 8, 1);
        validate_against_rust!(0, 8, 2);
        validate_against_rust!(0, 8, 3);
        validate_against_rust!(0, 8, 4);
        validate_against_rust!(0, 16);
        validate_against_rust!(0, 16, 0);
        validate_against_rust!(0, 16, 1);
        validate_against_rust!(0, 16, 2);
        validate_against_rust!(0, 16, 3);
        validate_against_rust!(0, 16, 4);
        validate_against_rust!(1, 1);
        validate_against_rust!(1, 1, 0);
        validate_against_rust!(1, 1, 1);
        validate_against_rust!(1, 1, 2);
        validate_against_rust!(1, 1, 3);
        validate_against_rust!(1, 1, 4);
        validate_against_rust!(1, 2);
        validate_against_rust!(1, 2, 0);
        validate_against_rust!(1, 2, 1);
        validate_against_rust!(1, 2, 2);
        validate_against_rust!(1, 2, 3);
        validate_against_rust!(1, 2, 4);
        validate_against_rust!(1, 4);
        validate_against_rust!(1, 4, 0);
        validate_against_rust!(1, 4, 1);
        validate_against_rust!(1, 4, 2);
        validate_against_rust!(1, 4, 3);
        validate_against_rust!(1, 4, 4);
        validate_against_rust!(1, 8);
        validate_against_rust!(1, 8, 0);
        validate_against_rust!(1, 8, 1);
        validate_against_rust!(1, 8, 2);
        validate_against_rust!(1, 8, 3);
        validate_against_rust!(1, 8, 4);
        validate_against_rust!(1, 16);
        validate_against_rust!(1, 16, 0);
        validate_against_rust!(1, 16, 1);
        validate_against_rust!(1, 16, 2);
        validate_against_rust!(1, 16, 3);
        validate_against_rust!(1, 16, 4);
        validate_against_rust!(2, 1);
        validate_against_rust!(2, 1, 0);
        validate_against_rust!(2, 1, 1);
        validate_against_rust!(2, 1, 2);
        validate_against_rust!(2, 1, 3);
        validate_against_rust!(2, 1, 4);
        validate_against_rust!(2, 2);
        validate_against_rust!(2, 2, 0);
        validate_against_rust!(2, 2, 1);
        validate_against_rust!(2, 2, 2);
        validate_against_rust!(2, 2, 3);
        validate_against_rust!(2, 2, 4);
        validate_against_rust!(2, 4);
        validate_against_rust!(2, 4, 0);
        validate_against_rust!(2, 4, 1);
        validate_against_rust!(2, 4, 2);
        validate_against_rust!(2, 4, 3);
        validate_against_rust!(2, 4, 4);
        validate_against_rust!(2, 8);
        validate_against_rust!(2, 8, 0);
        validate_against_rust!(2, 8, 1);
        validate_against_rust!(2, 8, 2);
        validate_against_rust!(2, 8, 3);
        validate_against_rust!(2, 8, 4);
        validate_against_rust!(2, 16);
        validate_against_rust!(2, 16, 0);
        validate_against_rust!(2, 16, 1);
        validate_against_rust!(2, 16, 2);
        validate_against_rust!(2, 16, 3);
        validate_against_rust!(2, 16, 4);
        validate_against_rust!(3, 1);
        validate_against_rust!(3, 1, 0);
        validate_against_rust!(3, 1, 1);
        validate_against_rust!(3, 1, 2);
        validate_against_rust!(3, 1, 3);
        validate_against_rust!(3, 1, 4);
        validate_against_rust!(3, 2);
        validate_against_rust!(3, 2, 0);
        validate_against_rust!(3, 2, 1);
        validate_against_rust!(3, 2, 2);
        validate_against_rust!(3, 2, 3);
        validate_against_rust!(3, 2, 4);
        validate_against_rust!(3, 4);
        validate_against_rust!(3, 4, 0);
        validate_against_rust!(3, 4, 1);
        validate_against_rust!(3, 4, 2);
        validate_against_rust!(3, 4, 3);
        validate_against_rust!(3, 4, 4);
        validate_against_rust!(3, 8);
        validate_against_rust!(3, 8, 0);
        validate_against_rust!(3, 8, 1);
        validate_against_rust!(3, 8, 2);
        validate_against_rust!(3, 8, 3);
        validate_against_rust!(3, 8, 4);
        validate_against_rust!(3, 16);
        validate_against_rust!(3, 16, 0);
        validate_against_rust!(3, 16, 1);
        validate_against_rust!(3, 16, 2);
        validate_against_rust!(3, 16, 3);
        validate_against_rust!(3, 16, 4);
        validate_against_rust!(4, 1);
        validate_against_rust!(4, 1, 0);
        validate_against_rust!(4, 1, 1);
        validate_against_rust!(4, 1, 2);
        validate_against_rust!(4, 1, 3);
        validate_against_rust!(4, 1, 4);
        validate_against_rust!(4, 2);
        validate_against_rust!(4, 2, 0);
        validate_against_rust!(4, 2, 1);
        validate_against_rust!(4, 2, 2);
        validate_against_rust!(4, 2, 3);
        validate_against_rust!(4, 2, 4);
        validate_against_rust!(4, 4);
        validate_against_rust!(4, 4, 0);
        validate_against_rust!(4, 4, 1);
        validate_against_rust!(4, 4, 2);
        validate_against_rust!(4, 4, 3);
        validate_against_rust!(4, 4, 4);
        validate_against_rust!(4, 8);
        validate_against_rust!(4, 8, 0);
        validate_against_rust!(4, 8, 1);
        validate_against_rust!(4, 8, 2);
        validate_against_rust!(4, 8, 3);
        validate_against_rust!(4, 8, 4);
        validate_against_rust!(4, 16);
        validate_against_rust!(4, 16, 0);
        validate_against_rust!(4, 16, 1);
        validate_against_rust!(4, 16, 2);
        validate_against_rust!(4, 16, 3);
        validate_against_rust!(4, 16, 4);
    }
}

#[cfg(kani)]
mod proofs {
    use core::alloc::Layout;

    use super::*;

    fn slice_dst_size_for_trailing_bytes(
        layout: TrailingSliceLayout,
        trailing_size: usize,
    ) -> Option<usize> {
        let without_padding = layout.size_offset.checked_add(trailing_size)?;
        let padding = util::padding_needed_for(without_padding, layout.size_align);
        let rounded = without_padding.checked_add(padding)?;
        layout.size_prefix.checked_add(rounded)
    }

    fn any_layout_align() -> NonZeroUsize {
        let exponent: u8 = kani::any();
        kani::assume(usize::from(exponent) < POINTER_WIDTH_BITS - 1);

        // `exponent < POINTER_WIDTH_BITS`, so the shift is in range and its
        // result is non-zero. This construction is surjective over precisely
        // the power-of-two alignments below `THEORETICAL_MAX_ALIGN`.
        NonZeroUsize::new(1usize << exponent).unwrap()
    }

    impl kani::Arbitrary for DstLayout {
        fn any() -> Self {
            let align = any_layout_align();
            let size_info: SizeInfo = kani::any();

            // For testing purposes, we most care about instantiations of
            // `DstLayout` that can correspond to actual Rust types. We use
            // `Layout` to verify that our `DstLayout` satisfies the validity
            // conditions of Rust layouts.
            kani::assume(
                match size_info {
                    SizeInfo::Sized { size } => Layout::from_size_align(size, align.get()),
                    SizeInfo::SliceDst(trailing) => {
                        // `SliceDst` cannot encode one exact size. Validate its
                        // minimum size and the invariants required of the size
                        // formula for layouts of real Rust types.
                        let padding =
                            util::padding_needed_for(trailing.size_offset, trailing.size_align);
                        let rounded = trailing.size_offset.checked_add(padding);
                        let min_size =
                            rounded.and_then(|size| trailing.size_prefix.checked_add(size));
                        let unrounded_min_size =
                            trailing.size_prefix.checked_add(trailing.size_offset);

                        kani::assume(matches!(
                            unrounded_min_size,
                            Some(size) if size >= trailing.offset
                        ));

                        match min_size {
                            Some(min_size) => Layout::from_size_align(min_size, align.get()),
                            None => Layout::from_size_align(usize::MAX, align.get()),
                        }
                    }
                }
                .is_ok(),
            );

            Self { align: align, size_info: size_info, statically_shallow_unpadded: kani::any() }
        }
    }

    impl kani::Arbitrary for SizeInfo {
        fn any() -> Self {
            let is_sized: bool = kani::any();

            match is_sized {
                true => {
                    let size: usize = kani::any();

                    kani::assume(size <= DstLayout::MAX_SIZE);

                    SizeInfo::Sized { size }
                }
                false => SizeInfo::SliceDst(kani::any()),
            }
        }
    }

    impl kani::Arbitrary for TrailingSliceLayout {
        fn any() -> Self {
            let elem_size: usize = kani::any();
            let offset: usize = kani::any();
            let size_offset: usize = kani::any();
            let size_align = any_layout_align();
            let raw_size_prefix: usize = kani::any();
            // Since `size_align` is a power of two, masking is surjective over
            // precisely the values in `0..size_align`.
            #[allow(clippy::arithmetic_side_effects)]
            let size_prefix = raw_size_prefix & (size_align.get() - 1);

            kani::assume(elem_size < DstLayout::MAX_SIZE);
            kani::assume(offset < DstLayout::MAX_SIZE);
            kani::assume(size_offset < DstLayout::MAX_SIZE);

            TrailingSliceLayout { elem_size, offset, size_prefix, size_offset, size_align }
        }
    }

    #[kani::proof]
    fn prove_requires_dynamic_padding() {
        let layout: DstLayout = kani::any();

        let SizeInfo::SliceDst(size_info) = layout.size_info else {
            kani::assume(false);
            loop {}
        };

        let meta: usize = kani::any();

        let Some(trailing_slice_size) = size_info.elem_size.checked_mul(meta) else {
            // The `trailing_slice_size` exceeds `usize::MAX`; `meta` is invalid.
            kani::assume(false);
            loop {}
        };

        let Some(trailing_slice_end) = size_info.offset.checked_add(trailing_slice_size) else {
            // The trailing slice end exceeds `usize::MAX`; `meta` is invalid.
            kani::assume(false);
            loop {}
        };

        let Some(without_padding) = size_info.size_offset.checked_add(trailing_slice_size) else {
            kani::assume(false);
            loop {}
        };
        let inner_padding = util::padding_needed_for(without_padding, size_info.size_align);
        let Some(rounded_size) = without_padding.checked_add(inner_padding) else {
            kani::assume(false);
            loop {}
        };
        let Some(size) = size_info.size_prefix.checked_add(rounded_size) else {
            kani::assume(false);
            loop {}
        };

        if size > DstLayout::MAX_SIZE || trailing_slice_end > size {
            // This metadata cannot describe a valid instance.
            kani::assume(false);
            loop {}
        }

        if !layout.requires_dynamic_padding() {
            assert_eq!(trailing_slice_end, size);
        }
    }

    #[kani::proof]
    fn prove_dst_layout_extend() {
        use crate::util::{max, min, padding_needed_for};

        let base: DstLayout = kani::any();
        let field: DstLayout = kani::any();
        let packed: Option<NonZeroUsize> = kani::any();

        if let Some(max_align) = packed {
            kani::assume(max_align.is_power_of_two());
            kani::assume(base.align <= max_align);
        }

        // The base can only be extended if it's sized.
        kani::assume(matches!(base.size_info, SizeInfo::Sized { .. }));
        let base_size = if let SizeInfo::Sized { size } = base.size_info {
            size
        } else {
            unreachable!();
        };

        // The field's alignment is clamped by `max_align` (i.e., the
        // `packed` attribute, if any) [1].
        //
        // [1] Per https://doc.rust-lang.org/reference/type-layout.html#the-alignment-modifiers:
        //
        //   The alignments of each field, for the purpose of positioning
        //   fields, is the smaller of the specified alignment and the
        //   alignment of the field's type.
        let field_align = min(field.align, packed.unwrap_or(DstLayout::THEORETICAL_MAX_ALIGN));

        // Compute the minimum amount of inter-field padding needed to
        // satisfy the field's alignment, and offset of the trailing field.
        // [1]
        //
        // [1] Per https://doc.rust-lang.org/reference/type-layout.html#the-alignment-modifiers:
        //
        //   Inter-field padding is guaranteed to be the minimum required in
        //   order to satisfy each field's (possibly altered) alignment.
        let padding = padding_needed_for(base_size, field_align);
        let offset = match base_size.checked_add(padding) {
            Some(offset) => offset,
            None => {
                kani::assume(false);
                loop {}
            }
        };

        // Restrict the proof to fragments whose extension can correspond to a
        // valid Rust layout. Outside this domain, `extend` is permitted to
        // panic.
        match field.size_info {
            SizeInfo::Sized { size } => kani::assume(offset.checked_add(size).is_some()),
            SizeInfo::SliceDst(trailing) => {
                kani::assume(offset.checked_add(trailing.offset).is_some());
                let unnormalized_prefix = offset.checked_add(trailing.size_prefix);
                kani::assume(unnormalized_prefix.is_some());
                let unnormalized_prefix = unnormalized_prefix.unwrap();
                let size_prefix = unnormalized_prefix % trailing.size_align.get();
                let prefix_multiple = unnormalized_prefix - size_prefix;
                kani::assume(prefix_multiple.checked_add(trailing.size_offset).is_some());
            }
        }

        // Under the above conditions, `DstLayout::extend` will not panic.
        let composite = base.extend(field, packed);

        // The struct's alignment is the maximum of its previous alignment and
        // `field_align`.
        assert_eq!(composite.align, max(base.align, field_align));

        // For testing purposes, we'll also construct `alloc::Layout`
        // stand-ins for `DstLayout`, and show that `extend` behaves
        // comparably on both types.
        let base_analog = Layout::from_size_align(base_size, base.align.get()).unwrap();

        match field.size_info {
            SizeInfo::Sized { size: field_size } => {
                if let SizeInfo::Sized { size: composite_size } = composite.size_info {
                    // If the trailing field is sized, the resulting layout will
                    // be sized. Its size will be the sum of the preceding
                    // layout, the size of the new field, and the size of
                    // inter-field padding between the two.
                    assert_eq!(composite_size, offset + field_size);

                    let field_analog =
                        Layout::from_size_align(field_size, field_align.get()).unwrap();

                    if let Ok((actual_composite, actual_offset)) = base_analog.extend(field_analog)
                    {
                        assert_eq!(actual_offset, offset);
                        assert_eq!(actual_composite.size(), composite_size);
                        assert_eq!(actual_composite.align(), composite.align.get());
                    } else {
                        // An error here reflects that composite of `base`
                        // and `field` cannot correspond to a real Rust type
                        // fragment, because such a fragment would violate
                        // the basic invariants of a valid Rust layout. At
                        // the time of writing, `DstLayout` is a little more
                        // permissive than `Layout`, so we don't assert
                        // anything in this branch (e.g., unreachability).
                    }
                } else {
                    panic!("The composite of two sized layouts must be sized.")
                }
            }
            SizeInfo::SliceDst(field_trailing) => {
                if let SizeInfo::SliceDst(composite_trailing) = composite.size_info {
                    // The offset of the trailing slice component is the sum
                    // of the offset of the trailing field and the trailing
                    // slice offset within that field.
                    assert_eq!(composite_trailing.offset, offset + field_trailing.offset);
                    // The elem size is unchanged.
                    assert_eq!(composite_trailing.elem_size, field_trailing.elem_size);

                    // The normalized formula must continue to describe the
                    // size of the field at every trailing byte contribution
                    // for which the checked size computation succeeds. This
                    // is stronger than considering only products of a slice
                    // length and `elem_size`, and avoids a nonlinear
                    // multiplication in the verifier.
                    let trailing_size: usize = kani::any();
                    let field_size =
                        match slice_dst_size_for_trailing_bytes(field_trailing, trailing_size) {
                            Some(size) => size,
                            None => {
                                kani::assume(false);
                                loop {}
                            }
                        };
                    let expected_size = match offset.checked_add(field_size) {
                        Some(size) => size,
                        None => {
                            kani::assume(false);
                            loop {}
                        }
                    };
                    assert_eq!(
                        slice_dst_size_for_trailing_bytes(composite_trailing, trailing_size),
                        Some(expected_size)
                    );

                    // `alloc::Layout` permits sizes which are not a multiple
                    // of alignment, so this represents the unpadded prefix of
                    // the DST through the start of its trailing slice.
                    let field_analog =
                        Layout::from_size_align(field_trailing.offset, field_align.get()).unwrap();

                    if let Ok((actual_composite, actual_offset)) = base_analog.extend(field_analog)
                    {
                        assert_eq!(actual_offset, offset);
                        assert_eq!(actual_composite.size(), composite_trailing.offset);
                        assert_eq!(actual_composite.align(), composite.align.get());
                    } else {
                        // An error here reflects that composite of `base`
                        // and `field` cannot correspond to a real Rust type
                        // fragment, because such a fragment would violate
                        // the basic invariants of a valid Rust layout. At
                        // the time of writing, `DstLayout` is a little more
                        // permissive than `Layout`, so we don't assert
                        // anything in this branch (e.g., unreachability).
                    }
                } else {
                    panic!("The extension of a layout with a DST must result in a DST.")
                }
            }
        }
    }

    #[kani::proof]
    #[kani::should_panic]
    fn prove_dst_layout_extend_dst_panics() {
        let base: DstLayout = kani::any();
        let field: DstLayout = kani::any();
        let packed: Option<NonZeroUsize> = kani::any();

        if let Some(max_align) = packed {
            kani::assume(max_align.is_power_of_two());
            kani::assume(base.align <= max_align);
        }

        kani::assume(matches!(base.size_info, SizeInfo::SliceDst(..)));

        let _ = base.extend(field, packed);
    }

    #[kani::proof]
    fn prove_dst_layout_pad_to_align() {
        use crate::util::padding_needed_for;

        let layout: DstLayout = kani::any();

        if let SizeInfo::SliceDst(trailing) = layout.size_info {
            // Restrict the proof to fragments whose padded layout can
            // correspond to a valid Rust type. Outside this domain,
            // `pad_to_align` is permitted to panic.
            if trailing.size_align.get() < layout.align.get() {
                let prefix = if trailing.size_prefix == 0 { 0 } else { trailing.size_align.get() };
                kani::assume(trailing.size_offset.checked_add(prefix).is_some());
            } else {
                let padding = padding_needed_for(trailing.size_prefix, layout.align);
                let rounded_prefix = trailing.size_prefix.checked_add(padding);
                kani::assume(rounded_prefix.is_some());
                let rounded_prefix = rounded_prefix.unwrap();
                let size_prefix = rounded_prefix % trailing.size_align.get();
                let prefix_multiple = rounded_prefix - size_prefix;
                kani::assume(trailing.size_offset.checked_add(prefix_multiple).is_some());
            }
        }

        let padded = layout.pad_to_align();

        // Calling `pad_to_align` does not alter the `DstLayout`'s alignment.
        assert_eq!(padded.align, layout.align);

        if let SizeInfo::Sized { size: unpadded_size } = layout.size_info {
            if let SizeInfo::Sized { size: padded_size } = padded.size_info {
                // If the layout is sized, it will remain sized after padding is
                // added. Its sum will be its unpadded size and the size of the
                // trailing padding needed to satisfy its alignment
                // requirements.
                let padding = padding_needed_for(unpadded_size, layout.align);
                assert_eq!(padded_size, unpadded_size + padding);

                // Prove that calling `DstLayout::pad_to_align` behaves
                // identically to `Layout::pad_to_align`.
                let layout_analog =
                    Layout::from_size_align(unpadded_size, layout.align.get()).unwrap();
                let padded_analog = layout_analog.pad_to_align();
                assert_eq!(padded_analog.align(), layout.align.get());
                assert_eq!(padded_analog.size(), padded_size);
            } else {
                panic!("The padding of a sized layout must result in a sized layout.")
            }
        } else if let (SizeInfo::SliceDst(unpadded_trailing), SizeInfo::SliceDst(padded_trailing)) =
            (layout.size_info, padded.size_info)
        {
            assert_eq!(padded_trailing.offset, unpadded_trailing.offset);
            assert_eq!(padded_trailing.elem_size, unpadded_trailing.elem_size);

            // Prove the normalization for every trailing byte contribution
            // for which the checked size computation succeeds. This is
            // stronger than considering only products of a slice length and
            // `elem_size`, and avoids a nonlinear multiplication in the
            // verifier.
            let trailing_size: usize = kani::any();
            let unpadded_size =
                match slice_dst_size_for_trailing_bytes(unpadded_trailing, trailing_size) {
                    Some(size) => size,
                    None => {
                        kani::assume(false);
                        loop {}
                    }
                };
            let trailing_padding = padding_needed_for(unpadded_size, layout.align);
            let expected_size = match unpadded_size.checked_add(trailing_padding) {
                Some(size) => size,
                None => {
                    kani::assume(false);
                    loop {}
                }
            };
            assert_eq!(
                slice_dst_size_for_trailing_bytes(padded_trailing, trailing_size),
                Some(expected_size)
            );
        } else {
            panic!("The padding of a DST layout must result in a DST layout.")
        }
    }
}
