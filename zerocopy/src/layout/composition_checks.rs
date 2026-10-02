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

//! A separate numeric reference for layout extension and final padding.
//!
//! The reference keeps alignment and phase as separate integers. It uses
//! remainders and checked arithmetic, and never calls the production layout,
//! rounding, or padding helpers. The assertions compare every observable field,
//! including physical slice offset and the compressed size expression.
//!
//! Runtime witnesses avoid decoding a production rounding word in the reference.
//! Every nonzero rounding word has such a witness: its greatest power of two is
//! the alignment, and subtracting that alignment gives a smaller phase. The
//! assertions quantify over arbitrary witnesses and check their correspondence
//! before calling the production operation.

// Explicit matches expose overflow paths without depending on Option's Try
// trait, which the pinned extraction does not model.
#![allow(clippy::arithmetic_side_effects, clippy::indexing_slicing, clippy::question_mark)]

use super::{DstLayout, NonZeroUsize, SizeInfo};

#[derive(Copy, Clone)]
struct ReferenceTail {
    offset: usize,
    elem_size: usize,
    base: usize,
    round_align: usize,
    phase: usize,
}

#[derive(Copy, Clone)]
#[allow(variant_size_differences)]
enum ReferenceSize {
    Fixed(usize),
    Tail(ReferenceTail),
}

#[derive(Copy, Clone)]
struct ReferenceLayout {
    align: usize,
    size: ReferenceSize,
    unpadded: bool,
}

/// The exact numeric observation compared with the stored representation.
/// A phase must be smaller than its power-of-two alignment; the checked sum
/// prevents the witness relation from hiding a machine-word overflow.
fn matches_reference(runtime_layout: DstLayout, reference: ReferenceLayout) -> bool {
    runtime_layout.align.get() == reference.align
        && runtime_layout.statically_shallow_unpadded == reference.unpadded
        && match (runtime_layout.size_info, reference.size) {
            (SizeInfo::Sized { size }, ReferenceSize::Fixed(expected)) => size == expected,
            (SizeInfo::SliceDst(actual), ReferenceSize::Tail(expected)) => {
                expected.round_align.is_power_of_two()
                    && expected.phase < expected.round_align
                    && actual.offset == expected.offset
                    && actual.elem_size == expected.elem_size
                    && actual.size_base == expected.base
                    && match expected.round_align.checked_add(expected.phase) {
                        Some(encoded) => actual.size_rounding_align_and_phase.0.get() == encoded,
                        None => false,
                    }
            }
            _ => false,
        }
}

/// Round up by the least padding that makes the result divisible by alignment.
fn reference_round_up(bytes: usize, align: usize) -> Option<usize> {
    if align == 0 {
        return None;
    }
    let padding = (align - bytes % align) % align;
    bytes.checked_add(padding)
}

/// Mirrors the production debug-assertion domain without imposing a size bound.
fn extension_alignment(align: usize) -> bool {
    align.is_power_of_two() && align <= 1 << 29
}

/// Append a field, retaining its complete inner size expression.
/// `None` means an alignment check failed, the preceding layout was unsized,
/// or an intermediate required by production overflowed. There is no extra
/// headroom or `isize` restriction.
fn reference_extend(
    preceding: ReferenceLayout,
    field: ReferenceLayout,
    packed: Option<NonZeroUsize>,
) -> Option<ReferenceLayout> {
    if !extension_alignment(preceding.align) || !extension_alignment(field.align) {
        return None;
    }
    let field_align = match packed {
        Some(cap) => {
            if !extension_alignment(cap.get()) {
                return None;
            }
            if field.align < cap.get() {
                field.align
            } else {
                cap.get()
            }
        }
        None => field.align,
    };
    reference_extend_at(preceding, field, field_align)
}

// Keep placement separate from alignment admission so the reference has one
// arithmetic path for packed and unpacked records.
fn reference_extend_at(
    preceding: ReferenceLayout,
    field: ReferenceLayout,
    field_align: usize,
) -> Option<ReferenceLayout> {
    let bytes = match preceding.size {
        ReferenceSize::Fixed(bytes) => bytes,
        ReferenceSize::Tail(_) => return None,
    };
    let offset = match reference_round_up(bytes, field_align) {
        Some(offset) => offset,
        None => return None,
    };
    let size = match field.size {
        ReferenceSize::Fixed(bytes) => match offset.checked_add(bytes) {
            Some(size) => ReferenceSize::Fixed(size),
            None => return None,
        },
        ReferenceSize::Tail(tail) => {
            let slice_offset = match offset.checked_add(tail.offset) {
                Some(offset) => offset,
                None => return None,
            };
            let base = match offset.checked_add(tail.base) {
                Some(base) => base,
                None => return None,
            };
            ReferenceSize::Tail(ReferenceTail { offset: slice_offset, base, ..tail })
        }
    };
    Some(ReferenceLayout {
        align: if preceding.align > field_align { preceding.align } else { field_align },
        size,
        unpadded: preceding.unpadded & field.unpadded & (offset == bytes),
    })
}

/// Add final padding without discarding an inner DST's rounding.
fn reference_pad(reference: ReferenceLayout) -> Option<ReferenceLayout> {
    if !reference.align.is_power_of_two() {
        return None;
    }
    let (size, no_static_padding) = match reference.size {
        ReferenceSize::Fixed(bytes) => match reference_round_up(bytes, reference.align) {
            Some(rounded) => (ReferenceSize::Fixed(rounded), rounded == bytes),
            None => return None,
        },
        ReferenceSize::Tail(tail) => {
            if !tail.round_align.is_power_of_two() || tail.phase >= tail.round_align {
                return None;
            }
            let (base, round_align, phase) = if tail.round_align >= reference.align {
                let base = match reference_round_up(tail.base, reference.align) {
                    Some(base) => base,
                    None => return None,
                };
                (base, tail.round_align, tail.phase)
            } else {
                let rounded_base = match reference_round_up(tail.base, tail.round_align) {
                    Some(base) => base,
                    None => return None,
                };
                let fixed = match rounded_base.checked_add(tail.phase) {
                    Some(fixed) => fixed,
                    None => return None,
                };
                let phase = fixed % reference.align;
                (fixed - phase, reference.align, phase)
            };
            (ReferenceSize::Tail(ReferenceTail { base, round_align, phase, ..tail }), true)
        }
    };
    Some(ReferenceLayout { size, unpadded: reference.unpadded & no_static_padding, ..reference })
}

/// Check extension against every stored reference observation on the exact
/// checked-arithmetic domain where the production operation can succeed.
///
/// ```aeneas
/// spec composition_extend_checks_spec
///   ensures _ => True
/// ```
fn check_extend(
    preceding: DstLayout,
    field: DstLayout,
    packed: Option<NonZeroUsize>,
    preceding_reference: ReferenceLayout,
    field_reference: ReferenceLayout,
) {
    if matches_reference(preceding, preceding_reference)
        && matches_reference(field, field_reference)
    {
        if let Some(expected) = reference_extend(preceding_reference, field_reference, packed) {
            let actual = preceding.extend(field, packed);
            assert!(matches_reference(actual, expected));
        }
    }
}

/// Check trailing padding, including both relative-alignment branches for DSTs.
///
/// ```aeneas
/// spec composition_pad_checks_spec
///   ensures _ => True
/// ```
fn check_pad(runtime_layout: DstLayout, reference: ReferenceLayout) {
    if matches_reference(runtime_layout, reference) {
        if let Some(expected) = reference_pad(reference) {
            let actual = runtime_layout.pad_to_align();
            assert!(matches_reference(actual, expected));
        }
    }
}

