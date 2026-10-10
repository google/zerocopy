// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Extraction controls, never executed as Rust.
//!
//! The invalid producers intentionally violate Boolean bit validity. We prove
//! that their extracted executions are forbidden, rather than running Rust UB.
//! The helper is opaque, with the same u8-to-bool interpretation as production.
//! This fixture tests translation of calls, not certification of its union body.
#![allow(dead_code)]

pub mod util {
    use core::mem::ManuallyDrop;

    /// The caller must supply a bit-valid representation of `Dst` with equal
    /// size. Only `u8` to `bool` is selected in these extraction controls.
    pub const unsafe fn transmute_unchecked<Src, Dst>(src: Src) -> Dst {
        union Bits<Src, Dst> {
            src: ManuallyDrop<Src>,
            dst: ManuallyDrop<Dst>,
        }
        // SAFETY: This requires the documented caller obligations. The bad
        // fixtures below deliberately violate them and must never be executed.
        ManuallyDrop::into_inner(unsafe { Bits { src: ManuallyDrop::new(src) }.dst })
    }
}

pub fn valid(byte: u8) -> Option<bool> {
    if byte < 2 {
        // SAFETY: Both one-byte types have equal size; 0 and 1 are valid bools.
        Some(unsafe { util::transmute_unchecked(byte) })
    } else {
        None
    }
}

/// No call to this extraction fixture is permitted.
pub unsafe fn ignored() {
    // Deliberate UB for a negative control. Do not execute this Rust function.
    let _ = unsafe { util::transmute_unchecked::<u8, bool>(2u8) };
}

/// No call to this extraction fixture is permitted, including when its caller
/// would accept divergence. UB happens before the loop begins.
pub unsafe fn before_divergence(escape: bool) {
    // Deliberate UB for a negative control. Do not execute this Rust function.
    let _ = unsafe { util::transmute_unchecked::<u8, bool>(2u8) };
    // Keep a syntactic exit: the pinned extractor rejects loops with no break.
    // The Lean control chooses false, so an accepted execution could not exit.
    loop {
        if escape {
            break;
        }
    }
}
