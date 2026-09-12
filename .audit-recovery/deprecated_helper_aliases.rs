// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![allow(warnings)]

include!("include.rs");

// Each alias must register the helper itself. Another derive on the same
// item could register it instead and hide a regression.
#[derive(::zerocopy_derive::FromZeroes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct LegacyZeros(u8);

util_assert_impl_all!(LegacyZeros: imp::FromZeros, imp::TryFromBytes);

#[derive(::zerocopy_derive::AsBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct LegacyBytes(u8);

util_assert_impl_all!(LegacyBytes: imp::IntoBytes);
