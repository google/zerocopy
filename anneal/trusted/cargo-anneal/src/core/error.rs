// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Structured error model shared across `cargo-anneal` and `anneal-audit`.

use std::io;

/// Represents a structured audit or verification failure distinguishing
/// reported frontend/source or policy rejections (`code == 1`) from
/// operational or environment failures (`code == 2`).
///
/// A rejection does not establish that the requested proposition is false.
#[derive(Debug, Clone, Eq, thiserror::Error)]
#[error("{message}")]
pub struct Failure {
    /// Holds the process exit code (`1` for rejection, `2` for operational
    /// failure).
    pub code: i32,
    /// Names the phase in which the failure occurred.
    pub phase: String,
    /// Contains the human-readable diagnostic message.
    pub message: String,
    /// Optional structured sub-reason for classified proof failures (such as
    /// `"heartbeat_limit_exceeded"` or `"recursion_depth_exceeded"`), omitted
    /// for ordinary elaboration and operational failures.
    pub reason: Option<String>,
    io_kind: Option<io::ErrorKind>,
    read_only_fs: bool,
}

impl PartialEq for Failure {
    fn eq(&self, other: &Self) -> bool {
        self.code == other.code
            && self.phase == other.phase
            && self.message == other.message
            && self.reason == other.reason
    }
}

impl Failure {
    /// Construct a new [`Failure`] preserving explicit exit code `1` vs `2`.
    pub fn new(code: i32, phase: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            code,
            phase: phase.into(),
            message: message.into(),
            reason: None,
            io_kind: None,
            read_only_fs: false,
        }
    }

    /// Attach a structured sub-reason (for example `"heartbeat_limit_exceeded"`
    /// or `"recursion_depth_exceeded"`).
    pub fn with_reason(mut self, reason: impl Into<String>) -> Self {
        self.reason = Some(reason.into());
        self
    }

    /// Construct a policy-rejection [`Failure`] (`code == 1`).
    pub fn policy(phase: impl Into<String>, message: impl Into<String>) -> Self {
        Self::new(1, phase, message)
    }

    /// Construct an operational or environment [`Failure`] (`code == 2`).
    pub fn operational(phase: impl Into<String>, message: impl Into<String>) -> Self {
        Self::new(2, phase, message)
    }

    /// Construct an operational [`Failure`] capturing structured I/O metadata.
    pub fn operational_io_kind(
        phase: impl Into<String>,
        message: impl Into<String>,
        io_kind: io::ErrorKind,
        read_only_fs: bool,
    ) -> Self {
        Self {
            code: 2,
            phase: phase.into(),
            message: message.into(),
            reason: None,
            io_kind: Some(io_kind),
            read_only_fs,
        }
    }

    /// Return `true` when this failure represents a read-only filesystem or
    /// permission denial during best-effort cache initialization.
    pub const fn is_unwritable_io_error(&self) -> bool {
        self.read_only_fs
            || matches!(
                self.io_kind,
                Some(io::ErrorKind::PermissionDenied | io::ErrorKind::ReadOnlyFilesystem)
            )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn error_kinds_preserve_exit_codes_and_io_metadata() {
        assert_eq!(Failure::policy("audit", "bad").code, 1);
        assert!(Failure::policy("audit", "bad").reason.is_none());
        let limited =
            Failure::policy("compile-Proof", "limit").with_reason("heartbeat_limit_exceeded");
        assert_eq!(limited.reason.as_deref(), Some("heartbeat_limit_exceeded"));
        assert_ne!(limited, Failure::policy("compile-Proof", "limit"));
        assert_eq!(Failure::operational("io", "boom").code, 2);

        let rofs = Failure::operational_io_kind(
            "olean-cache",
            "erofs",
            io::ErrorKind::ReadOnlyFilesystem,
            true,
        );
        assert!(rofs.is_unwritable_io_error());
        assert_eq!(rofs, Failure::operational("olean-cache", "erofs"));

        let denied = Failure::operational_io_kind(
            "olean-cache",
            "eacces",
            io::ErrorKind::PermissionDenied,
            false,
        );
        assert!(denied.is_unwritable_io_error());

        let other =
            Failure::operational_io_kind("olean-cache", "missing", io::ErrorKind::NotFound, false);
        assert!(!other.is_unwritable_io_error());
        assert_eq!(other, Failure::operational("olean-cache", "missing"));
    }
}
