// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Independent arithmetic for nested `repr(C)` slice DSTs.
//!
//! The layers run from outermost to innermost. Packing caps placement
//! alignment, while every containing layer retains its field's complete size.
//! These descriptors also model arithmetic combinations Rust rejects as types,
//! including simultaneous packing and explicit alignment. No pointer or
//! allocation operation consumes these synthetic layouts.

// The pinned extraction does not model Option's Try trait. Explicit matches
// also leave the overflow paths visible in this independent reference.
#![allow(clippy::question_mark, clippy::manual_map)]

/// One containing record, before placing its final field.
///
/// Plain words make the descriptor's mathematical decoding total. The Rust
/// functions below check the domain explicitly, including zero alignments.
#[derive(Copy, Clone)]
#[cfg_attr(test, derive(Debug))]
pub(super) struct NestedLayer {
    pub(super) packed: usize,
    pub(super) min_align: usize,
    pub(super) prefix_bytes: usize,
}

/// Returns the least multiple of `align` at least `size`, if representable.
///
/// Zero alignment returns `None`. The remainder rule is independent of the
/// production padding utility and works for every positive alignment.
///
/// ```aeneas
/// spec nested_round_up_spec
///   ensures(raw) rounded => rounded.map UScalar.val =
///     if align.val = 0 then none
///     else if LayoutMath.roundUp size.val align.val ≤ Usize.max
///       then some (LayoutMath.roundUp size.val align.val) else none
/// ```
#[allow(clippy::arithmetic_side_effects)]
pub(super) fn round_up(size: usize, align: usize) -> Option<usize> {
    if align == 0 {
        return None;
    }
    let remainder = size % align;
    if remainder == 0 {
        Some(size)
    } else {
        size.checked_add(align - remainder)
    }
}

fn apply_layer(layer: NestedLayer, size: usize, alignment: usize) -> Option<(usize, usize)> {
    if !layer.packed.is_power_of_two()
        || !layer.min_align.is_power_of_two()
        || layer.min_align > layer.packed
    {
        return None;
    }
    let field_align = if alignment < layer.packed { alignment } else { layer.packed };
    let offset = match round_up(layer.prefix_bytes, field_align) {
        Some(offset) => offset,
        None => return None,
    };
    let alignment = if layer.min_align < field_align { field_align } else { layer.min_align };
    let unpadded_size = match offset.checked_add(size) {
        Some(size) => size,
        None => return None,
    };
    let size = match round_up(unpadded_size, alignment) {
        Some(size) => size,
        None => return None,
    };
    Some((size, alignment))
}

/// Computes complete recursive size at any element count.
///
/// `None` means an invalid descriptor or `usize` overflow. An element size of
/// zero is valid at every power-of-two alignment. Sizes above `isize::MAX`
/// remain valid arithmetic results; no allocation is performed here.
///
/// ```aeneas
/// spec nested_reference_size_spec
///   ensures(raw) result => result.map UScalar.val =
///     NestedReference.checkedSize leading.val elem_size.val leaf_align.val elems.val
/// ```
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
pub(super) fn size_for_metadata(
    leading: &[NestedLayer],
    elem_size: usize,
    leaf_align: usize,
    elems: usize,
) -> Option<usize> {
    if !leaf_align.is_power_of_two() || elem_size % leaf_align != 0 {
        return None;
    }
    let mut state = match elem_size.checked_mul(elems) {
        Some(size) => Some((size, leaf_align)),
        None => None,
    };
    let mut i = leading.len();
    while i != 0 {
        i -= 1;
        let layer = leading[i];
        state = match state {
            Some((size, alignment)) => apply_layer(layer, size, alignment),
            None => None,
        };
    }
    match state {
        Some((size, _)) => Some(size),
        None => None,
    }
}
