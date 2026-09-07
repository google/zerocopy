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

//! Kani proof families for definitions in the crate root.
//!
//! Each child module owns the scope, oracle, and non-goal documentation for one
//! proof family. Keeping the coordinator free of proof mechanics makes each
//! family discoverable without coupling unrelated harnesses.

#[cfg(feature = "derive")]
mod derived;
mod into_bytes;
