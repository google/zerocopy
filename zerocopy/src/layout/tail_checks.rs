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

use super::TrailingSliceLayout;

pub(crate) fn same_optional_usize(left: Option<usize>, right: Option<usize>) -> bool {
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

pub(crate) fn reference_size(
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
