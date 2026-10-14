// Copyright 2026 The Fuchsia Authors
// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

//! Executable prototypes for six Rust-for-Linux integration opportunities.
//! See the accompanying README for source mappings and integration limits.
#![deny(unsafe_op_in_unsafe_fn)]

pub mod address_projection;
pub mod binder;
pub mod conversions;
pub mod device_ids;
pub mod firmware;
pub mod typed_init;

// Compile the original RfL implementation only for differential unit tests.
// Its doctests require the kernel crate and are not part of this host harness.
#[cfg(test)]
#[allow(dead_code)]
#[path = "../../rfl-linux/rust/kernel/transmute.rs"]
mod rfl_transmute;
