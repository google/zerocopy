// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Verification clients for the actual Rust validity dictionaries.
//!
//! The bodies need no memory access. Their postconditions demonstrate that a
//! Rust bound supplies the exact law checked at its implementation, including
//! when execution does not use the dictionary. These are content implications,
//! not proofs that a pointer cast or simultaneous access is permitted.

#![allow(dead_code)]

use super::{
    invariant::{CastableFrom, Initialized, Safe, Uninit},
    TransmuteFrom,
};

/// ```aeneas
/// spec require_transfer_spec
///   ensures(raw) _ => Referent.transmuteFrom Src Dst SV DV
/// ```
fn require_transfer<Src: ?Sized, Dst, SV, DV>()
where
    Dst: TransmuteFrom<Src, SV, DV> + ?Sized,
{
}

/// ```aeneas
/// spec require_type_independent_spec
///   ensures(raw) _ => Referent.typeIndependentPair SV DV
/// ```
fn require_type_independent<Src: ?Sized, Dst, SV, DV>()
where
    Dst: CastableFrom<Src, SV, DV> + ?Sized,
{
}

/// Intermediate width equality is a real premise: each individual transfer
/// promises nothing when its own endpoint sizes differ.
///
/// ```aeneas
/// spec compose_safe_transfers_spec
///   requires(raw) first_size : AeneasSpecs.RustModel.sameSize Src Mid
///   ensures(raw) _ => Referent.transmuteFrom Src Dst
///     Zerocopy.pointer.invariant.Safe Zerocopy.pointer.invariant.Safe
/// ```
fn compose_safe_transfers<Src, Mid, Dst>()
where
    Mid: TransmuteFrom<Src, Safe, Safe>,
    Dst: TransmuteFrom<Mid, Safe, Safe>,
{
}

/// Select real blanket and wrapper implementations, rather than supplying
/// standalone Lean dictionaries that merely resemble them.
///
/// ```aeneas
/// spec concrete_transfers_spec
///   ensures(raw) _ =>
///     Referent.transmuteFrom Bool U8
///       Zerocopy.pointer.invariant.Safe Zerocopy.pointer.invariant.Initialized ∧
///     Referent.transmuteFrom U8 Bool
///       Zerocopy.pointer.invariant.Initialized Zerocopy.pointer.invariant.Uninit ∧
///     Referent.typeIndependentPair Zerocopy.pointer.invariant.Initialized
///       Zerocopy.pointer.invariant.Initialized
/// ```
fn concrete_transfers() {
    require_transfer::<bool, u8, Safe, Initialized>();
    require_transfer::<[u8; 4], u32, Initialized, Safe>();
    require_transfer::<u8, bool, Initialized, Uninit>();
    require_transfer::<core::mem::ManuallyDrop<u8>, u8, Safe, Safe>();
    require_type_independent::<u8, bool, Initialized, Initialized>();
    require_type_independent::<bool, u32, Uninit, Uninit>();
}
