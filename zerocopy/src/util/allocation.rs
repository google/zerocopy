// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(dead_code, clippy::needless_nonzero_get)]

use core::num::NonZeroUsize;

use crate::DstLayout;

/// Prepares the actual metadata size without changing allocator arguments.
///
/// `None` propagates metadata sizing overflow. A present size and alignment are
/// preserved exactly, including zero size. Allocator validity additionally
/// requires the completed KnownLayout contract and valid metadata; this helper
/// does not infer those facts from an arbitrary size or decoded layout.
///
/// ```aeneas
/// spec allocation_prepare_spec
///   ensures(raw) result =>
///     result.map (fun pair => (pair.1.val, pair.2.val.val)) =
///       size.map (fun s => (s.val, align.val.val))
/// ```
#[inline]
// The explicit match keeps this extraction independent of closure translation.
#[allow(clippy::manual_map)]
pub(super) fn prepare(size: Option<usize>, align: NonZeroUsize) -> Option<(usize, NonZeroUsize)> {
    match size {
        Some(size) => Some((size, align)),
        None => None,
    }
}

/// Checks exact preparation against the supplied optional metadata size.
///
/// Every input is covered, including `None`, zero, unaligned sizes, sizes above
/// `isize::MAX`, and non-power-of-two alignments. Acceptance here asserts only
/// unchanged numerical arguments. The separate mathematical admitted-layout
/// domain requires power-of-two alignment, aligned complete size, and the
/// signed-size bound before concluding allocator validity.
///
/// ```aeneas
/// spec allocation_preparation_check_spec
///   ensures(raw) _ => True
/// ```
fn assert_preparation(size: Option<usize>, align: NonZeroUsize) {
    let prepared = prepare(size, align);
    match size {
        None => assert!(prepared.is_none()),
        Some(size) => match prepared {
            Some((actual_size, actual_align)) => {
                assert!(actual_size == size);
                assert!(actual_align.get() == align.get());
            }
            None => panic!("metadata size disappeared during preparation"),
        },
    }
}

/// Checks the concrete metadata-to-allocation numerical dataflow.
///
/// The independent reference keeps complete object rounding, including inner
/// padding. Encoding witnesses are checked before use. Numerical overflow
/// is a covered sizing outcome; allocator validity has a separate domain. The
/// final containment assertion also needs a physical-offset premise: it is
/// checked only when
/// the tail starts within the unrounded fixed region. Recursive completed
/// layouts have a separate containment theorem; decoding alone is insufficient.
///
/// ```aeneas
/// spec allocation_size_check_spec
///   ensures(raw) _ => True
/// ```
fn assert_allocation_size(
    runtime_layout: DstLayout,
    rounding_align: NonZeroUsize,
    phase: usize,
    metadata: usize,
) {
    use crate::layout::SizeInfo;
    let (actual, expected) = match runtime_layout.size_info {
        SizeInfo::Sized { size } => {
            (crate::pointer_metadata_unit_size_for_metadata(runtime_layout), Some(size))
        }
        SizeInfo::SliceDst(tail) => {
            if !crate::layout::tail_transform_checks::witness_matches(tail, rounding_align, phase) {
                return;
            }
            (
                crate::pointer_metadata_usize_size_for_metadata(metadata, runtime_layout),
                crate::layout::tail_checks::reference_size(tail, rounding_align, phase, metadata),
            )
        }
    };
    assert!(crate::layout::tail_checks::same_optional_usize(actual, expected));
    assert_preparation(actual, runtime_layout.align);
    let size = match prepare(actual, runtime_layout.align) {
        Some((size, _align)) => size,
        None => return,
    };
    assert!(crate::layout::tail_checks::same_optional_usize(expected, Some(size)));
    if let SizeInfo::SliceDst(tail) = runtime_layout.size_info {
        let unrounded_start = match tail.size_base.checked_add(phase) {
            Some(start) => start,
            None => panic!("accepted complete size has an overflowing fixed region"),
        };
        if tail.offset > unrounded_start {
            return;
        }
        let bytes = match metadata.checked_mul(tail.elem_size) {
            Some(bytes) => bytes,
            None => panic!("accepted complete size has an overflowing tail"),
        };
        let tail_end = match tail.offset.checked_add(bytes) {
            Some(end) => end,
            None => panic!("accepted complete size has an overflowing tail end"),
        };
        assert!(tail_end <= size);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::{RoundingAlignAndPhase, SizeInfo, TrailingSliceLayout};

    #[test]
    fn preparation_boundaries() {
        for alignment in [1, 2, 4, 8, 3, 1 << (usize::BITS - 1)] {
            let alignment = NonZeroUsize::new(alignment).unwrap();
            assert_preparation(None, alignment);
            for size in [0, 1, 7, 8, 9, DstLayout::MAX_SIZE, DstLayout::MAX_SIZE + 1, usize::MAX] {
                assert_preparation(Some(size), alignment);
            }
        }
    }

    #[test]
    fn metadata_preparation_boundaries() {
        let one = NonZeroUsize::new(1).unwrap();
        let eight = NonZeroUsize::new(8).unwrap();
        for size in [0, 1, 8, DstLayout::MAX_SIZE, DstLayout::MAX_SIZE + 1, usize::MAX] {
            let layout = DstLayout {
                align: one,
                size_info: SizeInfo::Sized { size },
                statically_shallow_unpadded: false,
            };
            assert_allocation_size(layout, one, 0, 0);
        }
        for (base, phase, stride, offset) in [(0, 0, 0, 0), (0, 0, 1, 0), (8, 1, 1, 9)] {
            let layout = DstLayout {
                align: one,
                size_info: SizeInfo::SliceDst(TrailingSliceLayout {
                    offset,
                    elem_size: stride,
                    size_base: base,
                    size_rounding_align_and_phase: RoundingAlignAndPhase::new(eight, phase),
                }),
                statically_shallow_unpadded: false,
            };
            for metadata in [0, 1, 7, DstLayout::MAX_SIZE, usize::MAX] {
                assert_allocation_size(layout, eight, phase, metadata);
            }
        }
    }
}
