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
//! (`LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`), and the imported
//! `library-lock.json` modules. Sysroot `.ir`/`.ir.sig` companions outside the
//! locks and the Lean shared libraries are identified only by
//! `lean --version`, under the uncompromised execution environment that
//! `THREAT_MODEL.md` assumes.

#[doc(hidden)]
pub mod bundle;
mod stage;
mod target;
mod toolchain;

pub use stage::Checker;
pub use target::{TargetAuditRequest, TargetBindings, TargetModule, TargetRole};
#[doc(hidden)]
pub use toolchain::{
    AdmittedToolchain, FOUNDATION_AXIOMS, IR_PARTS, ImportEdge, LOCKED_LEAN_SHA256,
    LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256, ModuleArtifacts, OLEAN_PARTS, PARTS,
    ParallelDagPlan, PreflightHeader, PreflightResult, TOOLCHAIN, UNPINNED_FOUNDATION_MODULES,
    default_compile_workers, default_lean_search_bases_from_env, is_clean_relative_path,
    is_lean_ident, is_sha256_hex, read_regular_file_deref, read_regular_file_strict, regular,
    run_parallel_dag, sha256_bytes, sha256_file, sha256_file_deref, stage_regular_file,
    topo_sort_modules, verify_sysroot_foundation_dir,
};
pub use toolchain::{Failure, Json, default_lean_path};
