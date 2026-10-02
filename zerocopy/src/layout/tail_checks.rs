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

//! Executable assertions for trailing sizes, capacities, and cast metadata.
//!
//! The reference calculations receive an explicit alignment and phase. They
//! use division remainders and checked arithmetic, and never decode the
//! production rounding representation or call production size helpers. The
//! checks bind these independent witnesses to the stored word before comparing
//! results. Every nonzero stored word has such witnesses: its highest set bit
//! is the alignment, and the lower bits are the phase.

// Explicit scalar reads and matches keep the reference independent of extra
// trait dictionaries and higher-order library models in the pinned extraction.
#![allow(clippy::needless_nonzero_get, clippy::manual_map)]

use core::num::NonZeroUsize;

use super::{CastType, DstLayout, MetadataCastError, SizeInfo, TrailingSliceLayout};

pub(super) fn same_optional_usize(left: Option<usize>, right: Option<usize>) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => left == right,
        (None, None) => true,
        _ => false,
    }
}

#[allow(clippy::arithmetic_side_effects)]
fn reference_round_up(bytes: usize, align: NonZeroUsize) -> Option<usize> {
    let remainder = bytes % align.get();
    let padding = if remainder == 0 { 0 } else { align.get() - remainder };
    bytes.checked_add(padding)
}

pub(super) fn reference_size(
    tail: TrailingSliceLayout,
    align: NonZeroUsize,
    phase: usize,
    elems: usize,
) -> Option<usize> {
    match elems.checked_mul(tail.elem_size) {
        None => None,
        Some(bytes) => match phase.checked_add(bytes) {
            None => None,
            Some(input) => match reference_round_up(input, align) {
                None => None,
                Some(rounded) => tail.size_base.checked_add(rounded),
            },
        },
    }
}

#[allow(clippy::arithmetic_side_effects)]
fn reference_capacity(
    tail: TrailingSliceLayout,
    align: NonZeroUsize,
    phase: usize,
    budget: usize,
) -> Option<usize> {
    match budget.checked_sub(tail.size_base) {
        None => None,
        Some(after_base) => {
            let rounded_budget = after_base - after_base % align.get();
            rounded_budget.checked_sub(phase)
        }
    }
}

fn reference_metadata(
    runtime_layout: DstLayout,
    align: NonZeroUsize,
    phase: usize,
    size: usize,
) -> Option<usize> {
    match runtime_layout.size_info {
        SizeInfo::Sized { .. } => None,
        SizeInfo::SliceDst(tail) => {
            if tail.elem_size == 0 {
                return None;
            }
            match reference_capacity(tail, align, phase, size) {
                None => None,
                Some(bytes) => {
                    #[allow(clippy::arithmetic_side_effects)]
                    let elems = bytes / tail.elem_size;
                    if same_optional_usize(reference_size(tail, align, phase, elems), Some(size)) {
                        Some(elems)
                    } else {
                        None
                    }
                }
            }
        }
    }
}

#[allow(clippy::arithmetic_side_effects)]
fn reference_cast(
    runtime_layout: DstLayout,
    align: NonZeroUsize,
    phase: usize,
    addr: usize,
    length: usize,
    side: CastType,
) -> Result<(usize, usize), MetadataCastError> {
    // The caller checks address addition and excludes the zero-stride panic
    // before either the production or reference cast is evaluated.
    let anchor = match side {
        CastType::Prefix => addr,
        CastType::Suffix => addr + length,
    };
    // Alignment failure has priority over insufficient size.
    if anchor % runtime_layout.align.get() != 0 {
        return Err(MetadataCastError::Alignment);
    }
    let candidate = match runtime_layout.size_info {
        SizeInfo::Sized { size } => {
            if size <= length {
                Some((0, size))
            } else {
                None
            }
        }
        SizeInfo::SliceDst(tail) => match reference_capacity(tail, align, phase, length) {
            None => None,
            Some(bytes) => {
                let elems = bytes / tail.elem_size;
                match reference_size(tail, align, phase, elems) {
                    Some(size) => Some((elems, size)),
                    None => None,
                }
            }
        },
    };
    match candidate {
        None => Err(MetadataCastError::Size),
        Some((elems, size)) => {
            let split = match side {
                CastType::Prefix => size,
                CastType::Suffix => length - size,
            };
            Ok((elems, split))
        }
    }
}

/// Check the entire optional size and capacity results, including overflow.
///
/// Physical slice offset does not constrain this claim: a raw layout can have
/// its slice outside the complete object. Nor is rounding alignment restricted
/// to Rust's maximum type alignment; every nonzero encoding is covered.
///
/// ```aeneas
/// spec trailing_arithmetic_check_spec
///   ensures(raw) _ => True
/// ```
fn trailing_arithmetic_check(
    tail: TrailingSliceLayout,
    align: NonZeroUsize,
    phase: usize,
    elems: usize,
    budget: usize,
) {
    if align.get().is_power_of_two()
        && phase < align.get()
        && same_optional_usize(
            align.get().checked_add(phase),
            Some(tail.size_rounding_align_and_phase.0.get()),
        )
    {
        assert!(same_optional_usize(
            tail.size_for_elems(elems),
            reference_size(tail, align, phase, elems),
        ));
        assert!(same_optional_usize(
            tail.max_trailing_bytes(budget),
            reference_capacity(tail, align, phase, budget),
        ));
    }
}

/// Check exact-size metadata and complete cast results against independent
/// calculations. A successful cast must select the greatest fitting element
/// count and its padded prefix/suffix split; errors must have the same kind.
///
/// The address guard is the production method's no-overflow premise. The
/// explicit zero-stride guard excludes its documented panic, even when an
/// alignment error would otherwise be returned. Exact-size inference itself
/// is also checked for zero-stride tails, for which it must return `None`.
///
/// ```aeneas
/// spec layout_observations_check_spec
///   ensures(raw) _ => True
/// ```
fn layout_observations_check(
    runtime_layout: DstLayout,
    align: NonZeroUsize,
    phase: usize,
    size: usize,
    addr: usize,
    length: usize,
    side: CastType,
) {
    let encoding_matches = match runtime_layout.size_info {
        SizeInfo::Sized { .. } => true,
        SizeInfo::SliceDst(tail) => {
            align.get().is_power_of_two()
                && phase < align.get()
                && same_optional_usize(
                    align.get().checked_add(phase),
                    Some(tail.size_rounding_align_and_phase.0.get()),
                )
        }
    };
    if encoding_matches {
        assert!(same_optional_usize(
            runtime_layout.metadata_for_exact_size(size),
            reference_metadata(runtime_layout, align, phase, size),
        ));
        let nonzero_stride = match runtime_layout.size_info {
            SizeInfo::Sized { .. } => true,
            SizeInfo::SliceDst(tail) => tail.elem_size != 0,
        };
        if addr.checked_add(length).is_some() && nonzero_stride {
            let actual = runtime_layout.validate_cast_and_convert_metadata(addr, length, side);
            let expected = reference_cast(runtime_layout, align, phase, addr, length, side);
            let same = match (actual, expected) {
                (Ok((elems, split)), Ok((expected_elems, expected_split))) => {
                    elems == expected_elems && split == expected_split
                }
                (Err(MetadataCastError::Alignment), Err(MetadataCastError::Alignment))
                | (Err(MetadataCastError::Size), Err(MetadataCastError::Size)) => true,
                _ => false,
            };
            assert!(same);
        }
    }
}
