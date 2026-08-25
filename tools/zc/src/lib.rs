// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Shared, typed access to repository configuration and CI behavior.

pub mod baseline;
pub mod ci;
pub mod cli;
pub mod execution;
pub mod github;
pub mod inventory;
pub mod metadata;
pub mod plan;
pub mod policy;
pub mod workflow;
