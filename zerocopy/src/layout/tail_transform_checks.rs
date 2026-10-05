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

//! Executable assertions for trailing layout transformations.
//!
//! Explicit alignment and phase witnesses bind the independent calculations
//! to the stored word. Every nonzero word has such witnesses. The references
//! use remainders and checked or wrapping arithmetic; they do not decode the
//! production representation or call its transformation helpers.

// Explicit scalar reads and Option matches keep these arithmetic branches
// visible to reviewers and supported by the pinned Aeneas extraction.
#![allow(clippy::manual_map, clippy::needless_nonzero_get)]

use core::num::NonZeroUsize;

use super::{
    tail_checks::{reference_size, same_optional_usize},
    DstLayout, SizeInfo, TrailingSliceLayout,
};

pub(super) fn witness_matches(
    tail: TrailingSliceLayout,
    align: NonZeroUsize,
    phase: usize,
) -> bool {
    align.get().is_power_of_two()
        && phase < align.get()
        && same_optional_usize(
            align.get().checked_add(phase),
            Some(tail.size_rounding_align_and_phase.0.get()),
        )
}

#[allow(clippy::arithmetic_side_effects)]
fn reference_advance(
    tail: TrailingSliceLayout,
    align: NonZeroUsize,
    phase: usize,
    bytes: usize,
) -> Option<(usize, usize)> {
    // Splitting first avoids overflowing phase + bytes when the normalized
    // result still needs to be classified. Under the witness guard, adding
    // the two remainders always fits. The checked base additions decide
    // exactly whether the new normalized base fits in a machine word.
    let remainder = bytes % align.get();
    let whole_bytes = bytes - remainder;
    match phase.checked_add(remainder) {
        None => None,
        Some(shifted) => {
            let new_phase = shifted % align.get();
            let carry = shifted - new_phase;
            match tail.size_base.checked_add(whole_bytes) {
                None => None,
                Some(base) => match base.checked_add(carry) {
                    None => None,
                    Some(base) => Some((base, new_phase)),
                },
            }
        }
    }
}

#[allow(clippy::arithmetic_side_effects)]
fn reference_wrapping_padding(
    tail: TrailingSliceLayout,
    align: NonZeroUsize,
    phase: usize,
    elems: usize,
) -> usize {
    // The complete padded size and physical slice end are both computed
    // modulo the word size. Their wrapping difference remains meaningful
    // even for overflowing sizes and offsets outside the complete object.
    let trailing_bytes = elems.wrapping_mul(tail.elem_size);
    let rounding_input = phase.wrapping_add(trailing_bytes);
    let remainder = rounding_input % align.get();
    let padding = if remainder == 0 { 0 } else { align.get() - remainder };
    let rounded = rounding_input.wrapping_add(padding);
    let complete = tail.size_base.wrapping_add(rounded);
    let slice_end = tail.offset.wrapping_add(trailing_bytes);
    complete.wrapping_sub(slice_end)
}

/// Compare advance success/failure and every stored output field with an
/// independent normalized base and phase. Advancing preserves the physical
/// offset, installs the requested stride, and stores alignment + new phase.
/// Overflow must agree exactly, including near usize::MAX.
///
/// Also compare the size offset with floor(base / alignment) * alignment +
/// phase, and compare wrapping padding with rounded size minus slice end.
/// No physical-layout, maximum-type-alignment, or signed-size bound is imposed.
///
/// ```aeneas
/// spec tail_transformations_check_spec
///   ensures(raw) _ => True
/// ```
fn tail_transformations_check(
    tail: TrailingSliceLayout,
    align: NonZeroUsize,
    phase: usize,
    bytes: usize,
    replacement_stride: usize,
    elems: usize,
) {
    if witness_matches(tail, align, phase) {
        let actual = tail.advance(bytes, replacement_stride);
        let expected = reference_advance(tail, align, phase, bytes);
        let same = match (actual, expected) {
            (None, None) => true,
            (Some(actual), Some((base, new_phase))) => {
                actual.offset == tail.offset
                    && actual.elem_size == replacement_stride
                    && actual.size_base == base
                    && same_optional_usize(
                        align.get().checked_add(new_phase),
                        Some(actual.size_rounding_align_and_phase.0.get()),
                    )
            }
            _ => false,
        };
        assert!(same);

        #[allow(clippy::arithmetic_side_effects)]
        let floor_base = tail.size_base - tail.size_base % align.get();
        assert!(same_optional_usize(Some(tail.size_offset()), floor_base.checked_add(phase)));
        assert!(
            tail.padding_for_elems(elems) == reference_wrapping_padding(tail, align, phase, elems)
        );
    }
}

/// A positive size-sequence comparison must imply equal independently
/// calculated Option sizes for any runtime element count. This checks the
/// complete result: equality of successful sizes and agreement on overflow.
/// The method's negative result makes no assertion about the sequences.
///
/// ```aeneas
/// spec tail_size_sequence_check_spec
///   ensures(raw) _ => True
/// ```
fn tail_size_sequence_check(
    left: TrailingSliceLayout,
    right: TrailingSliceLayout,
    left_align: NonZeroUsize,
    left_phase: usize,
    right_align: NonZeroUsize,
    right_phase: usize,
    elems: usize,
) {
    if witness_matches(left, left_align, left_phase)
        && witness_matches(right, right_align, right_phase)
        && left.has_same_size_sequence(right)
    {
        assert!(same_optional_usize(
            reference_size(left, left_align, left_phase, elems),
            reference_size(right, right_align, right_phase, elems),
        ));
    }
}

/// Dynamic padding is absent exactly when the independent zero-element size
/// is the physical slice offset and the stride is alignment-divisible. A
/// zero-element size overflow therefore reports dynamic padding. Fixed-size
/// layouts never require dynamic padding.
///
/// ```aeneas
/// spec tail_dynamic_padding_check_spec
///   ensures(raw) _ => True
/// ```
fn tail_dynamic_padding_check(runtime_layout: DstLayout, align: NonZeroUsize, phase: usize) {
    match runtime_layout.size_info {
        SizeInfo::Sized { .. } => assert!(!runtime_layout.requires_dynamic_padding()),
        SizeInfo::SliceDst(tail) => {
            if witness_matches(tail, align, phase) {
                #[allow(clippy::arithmetic_side_effects)]
                let stride_remainder = tail.elem_size % align.get();
                let no_dynamic_padding =
                    same_optional_usize(reference_size(tail, align, phase, 0), Some(tail.offset))
                        && stride_remainder == 0;
                assert!(runtime_layout.requires_dynamic_padding() == !no_dynamic_padding);
            }
        }
    }
}
