// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Admits Lean 4.34.1 toolchains against locked digests and verifies external
//! target theorems (`cargo-anneal`).
//!
//! External callers construct a [`Checker`] over a staged bundle root and pass
//! a [`TargetAuditRequest`] to [`Checker::run_target`]. Each run stages the
//! declared [`TargetModule`] sources into a private `0o700` directory, enforces
//! [`TargetRole::allows`] over parsed imports and compiled kernel declaration
//! edges, replays logically reached declarations onto `foundation-lock.json`,
//! and verifies exact definitional equality against the canonical obligation.
//!
//! Admission hashes the `lean` executable, the `foundation-lock.json` modules,
//! the sysroot `{Init,Std,Lean}*` `.olean` manifest
//! (`LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`), the `x86_64` Linux Lean
//! runtime shared libraries (`LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS`), and the
//! 4-tree `Init`/`Std` sysroot digests in `library-lock.json`. Sysroot
//! `.ir`/`.ir.sig` companions outside the locks (and Lean shared libraries on
//! uncatalogued triples) are identified only by `lean --version`, under the
//! uncompromised execution environment that `THREAT_MODEL.md` assumes.

#[doc(hidden)]
pub mod bundle;
mod olean_cache;
#[doc(hidden)]
pub mod cli;
#[doc(hidden)]
pub mod core;
mod diagnostics;
mod init;
#[doc(hidden)]
pub mod sandbox;
#[cfg(feature = "setup")]
#[doc(hidden)]
pub mod setup;
mod stage;
#[doc(hidden)]
pub mod sys_util;
mod target;
mod toolchain;
mod trusted_bundle;
mod verify;

#[doc(hidden)]
pub const EMBEDDED_BUNDLE_SOURCES: &[(&str, &str)] = verify::EMBEDDED_BUNDLE_SOURCES;
#[doc(hidden)]
pub const EMBEDDED_CORRESPONDENCE_PROVENANCE_JSON: &str =
    verify::EMBEDDED_CORRESPONDENCE_PROVENANCE_JSON;

pub use core::Failure;
#[doc(hidden)]
pub use core::{
    IR_PARTS, ImportEdge, ModuleArtifacts, OLEAN_PARTS, PARTS, is_clean_relative_path,
    is_lean_ident, is_sha256_hex, sha256_bytes, topo_sort_modules,
};
#[doc(hidden)]
pub use sys_util::{SafeFs, SysSanitizer, TempFileGuard};
pub use sandbox::{ActiveSandbox, SandboxMode};
pub use stage::{Checker, source_starts_with_module_keyword};
pub use target::{TargetAuditRequest, TargetBindings, TargetModule, TargetRole};
#[doc(hidden)]
pub use toolchain::{
    AdmittedToolchain, FOUNDATION_AXIOMS, LOCKED_LEAN_SHA256,
    LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS, LOCKED_LEAN_X86_64_LINUX_SHA256,
    LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256, ParallelDagPlan, PreflightHeader, PreflightResult,
    TOOLCHAIN, UNPINNED_FOUNDATION_MODULES, default_compile_workers,
    default_lean_search_bases_from_env, read_regular_file_deref, read_regular_file_strict,
    regular, run_parallel_dag, sha256_file, sha256_file_deref, stage_regular_file,
    verify_sysroot_foundation_dir, verify_sysroot_runtime_libs_for_sha,
};
pub use toolchain::{Json, default_lean_path};
