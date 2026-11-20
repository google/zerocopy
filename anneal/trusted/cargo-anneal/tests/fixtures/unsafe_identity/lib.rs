// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Compile-only input for the caller-contract association regression.
//!
//! The harness captures these functions and never executes them natively.
//! Reviewed caller requirements in `Spec.lean` follow the exported names,
//! regardless of which implementation occupies each compiler inventory slot.

#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::mir::*;

/// # Safety
///
/// The caller must satisfy the requirement for this exported name in
/// `Spec.lean`. The harness never calls this capture-only test input.
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub unsafe fn locked() -> u64 {
    mir! {
        { Unreachable() }
    }
}

/// # Safety
///
/// The caller must satisfy the requirement for this exported name in
/// `Spec.lean`. The harness never calls this capture-only test input.
pub unsafe fn open() -> u64 { 0 }
