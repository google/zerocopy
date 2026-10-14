// Copyright 2026 The Fuchsia Authors
// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

//! Minimal kernel scaffolding to compile the unchanged RfL projection engine.
//! Build-error paths panic in this host shim; Kbuild link-error behavior is not
//! modeled. The tested field/index projection paths use the original source.

#[derive(Debug)]
pub struct Error;
pub const ERANGE: Error = Error;

#[macro_export]
macro_rules! build_error {
    ($($message:tt)*) => {
        panic!("build_error in host baseline")
    };
}

#[macro_export]
macro_rules! build_assert {
    ($condition:expr $(, $message:expr)?) => {
        assert!($condition)
    };
}

pub mod prelude {
    pub use crate::{build_assert, build_error, Error, ERANGE};
    pub type Result<T = ()> = core::result::Result<T, Error>;
}

#[path = "../../../../rfl-linux/rust/kernel/ptr/projection.rs"]
pub mod projection_impl;

pub mod ptr {
    pub use crate::{project_pointer as project, projection_impl as projection};
}
