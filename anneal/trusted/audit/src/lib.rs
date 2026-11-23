// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Audits Anneal's repository trust boundary and compiled `.olean`
//! environments (`anneal-audit`).
//!
//! `anneal-audit` pairs with `trusted/audit/TrustedBoundary.lean` and builds on
//! `cargo_anneal`'s private Lean toolchain and staging substrate to enforce
//! Anneal's repository-CI invariants across Pass 1 (`trusted/lean/` +
//! `theory/`, Cargo DAG containment, `root-manifest.sha256`, and
//! `bundled_resources.rs` parity) and Pass 2 (`vendor/lean-miri/`,
//! `trusted/correspondence/`, and `correspondence/`).

mod cargo_boundary;
#[doc(hidden)]
pub mod cli;
mod miri_pin;
mod repo_audit;

pub use cargo_anneal::{
    AdmittedToolchain, Failure, IR_PARTS, ImportEdge, Json, LOCKED_LEAN_SHA256,
    LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS, LOCKED_LEAN_X86_64_LINUX_SHA256, ModuleArtifacts,
    OLEAN_PARTS, PARTS, TOOLCHAIN, TargetAuditRequest, TargetBindings, TargetModule, TargetRole,
    bundle, default_lean_path, is_clean_relative_path, is_lean_ident, is_sha256_hex, regular,
    sha256_bytes, sha256_file, stage_regular_file, topo_sort_modules,
};
pub use cargo_boundary::{check_cargo_boundary, verify_bundled_resources};
pub use miri_pin::{
    LOCKED_MIRI_COMMIT, LOCKED_PATCHED_MIRI_FILES, LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256,
    LOCKED_UPSTREAM_PIN_SHA256, MiriClosureEntry, PatchedMiriFile, SourceLock,
    SourceLockAcquisition, SourceLockCargoPackage, SourceLockComponentPin,
    SourceLockExternalDependencies, SourceLockPins, SourceLockResolutionFile,
    SourceLockRustcPrivateCrate, SourceLockSelectedArchivePaths, SupportingFileRecord, UpstreamPin,
    UpstreamSubPins, VendorFileEntry, VendorTree, ensure_miri_cache_outside_checkout,
    verify_source_lock_bytes, verify_sysroot_foundation_dir, verify_upstream_pin,
};
pub use repo_audit::{CandidateFeature, Checker, InspectorRequest, TrustTier, scan_lean_tree};
