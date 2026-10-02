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

//! These assertions make the primitive constructor promises readable in Rust.
//!
//! Aeneas proves successful execution, including the assertions, for arbitrary
//! inputs to each harness. The standard-library size and alignment reads are
//! the reference observations; the explicit Rust layout premise explains how
//! their extracted inputs correspond to the compiler's actual ABI.

#![allow(dead_code)]

use super::{mem, DstLayout, NonZeroUsize, SizeInfo};

/// Compares the three primitive constructors with Rust's size and alignment.
///
/// Rust type alignments are nonzero powers of two. The explicit guard also
/// makes the admitted ABI inputs visible when those reads are modeled as
/// unconstrained data during extraction.
///
/// ```aeneas
/// spec primitive_layout_checks_spec
///   ensures _ => True
/// ```
fn check_primitive_layouts<T>() {
    let size = mem::size_of::<T>();
    let align = mem::align_of::<T>();
    if !align.is_power_of_two() {
        return;
    }

    let fixed = DstLayout::for_type::<T>();
    assert!(fixed.align.get() == align);
    assert!(matches!(fixed.size_info, SizeInfo::Sized { size: actual } if actual == size));
    assert!(!fixed.statically_shallow_unpadded);

    let unpadded = DstLayout::for_unpadded_type::<T>();
    assert!(unpadded.align.get() == align);
    assert!(matches!(unpadded.size_info, SizeInfo::Sized { size: actual } if actual == size));
    assert!(unpadded.statically_shallow_unpadded);

    let slice = DstLayout::for_slice::<T>();
    assert!(slice.align.get() == align);
    assert!(slice.statically_shallow_unpadded);
    match slice.size_info {
        SizeInfo::SliceDst(tail) => {
            assert!(tail.offset == 0);
            assert!(tail.elem_size == size);
            assert!(tail.size_base == 0);
            // Alignment plus a zero phase has exactly this encoding.
            assert!(tail.size_rounding_align_and_phase.0.get() == align);
        }
        SizeInfo::Sized { .. } => panic!("slice constructor returned a sized layout"),
    }
}

/// Checks the empty layout constructor, including its optional alignment.
///
/// ```aeneas
/// spec empty_layout_checks_spec
///   ensures _ => True
/// ```
fn check_empty_layout(repr_align: Option<NonZeroUsize>) {
    let expected_align = match repr_align {
        Some(align) => align.get(),
        None => 1,
    };
    if !expected_align.is_power_of_two() {
        return;
    }
    let empty = DstLayout::new_zst(repr_align);
    assert!(empty.align.get() == expected_align);
    assert!(matches!(empty.size_info, SizeInfo::Sized { size: 0 }));
    assert!(empty.statically_shallow_unpadded);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primitive_examples() {
        check_primitive_layouts::<()>();
        check_primitive_layouts::<u8>();
        check_primitive_layouts::<u64>();
        check_primitive_layouts::<(u8, u64)>();
        check_primitive_layouts::<[u64; 3]>();
        check_empty_layout(None);
        for align in [1, 2, 8, 3] {
            check_empty_layout(NonZeroUsize::new(align));
        }
    }
}
