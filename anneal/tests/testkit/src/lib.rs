// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Shared test scaffolding for Anneal's fenced `tests/` workspace crates.
//!
//! `anneal-testkit` centralizes canonical tool discovery ([`toolchain`]),
//! typestate-enforced temporary workspaces and read-only permission guards
//! ([`workspace`]), process-group and subreaper execution ([`process`]),
//! hermetic ELF/Nix split-store simulation ([`store_sim`]), polarity-locked
//! corpus directives ([`corpora`]), and typed receipt/report assertions
//! ([`assertions`]). It intentionally holds zero `rustc_private` dependencies
//! so it compiles cleanly on both stable and nightly Rust toolchains.

pub mod assertions;
pub mod audit_fixture;
pub mod case_runner;
pub mod corpora;
pub mod digest;
pub mod mir_wp_fixture;
pub mod process;
pub mod store_sim;
pub mod toolchain;
pub mod workspace;

pub use assertions::{
    AuditReport, CaptureFailureStatus, CaptureStatus, CaptureSuccessStatus,
    TimingMs, VerifyFailureReceipt, VerifyReceipt, VerifySuccessReceipt,
    assert_audit_passed, assert_capture_rejected, assert_captured,
    assert_outcome_exit, assert_rejected, assert_verified_untainted,
};
pub use audit_fixture::{
    DEFAULT_VETTED_HEADER, LeanAuditFixture, OleanCachePolicy,
    SharedOleanCache,
};
pub use case_runner::{CaseDirectory, RunDirectory, select_cases};
pub use corpora::{
    BlessPatch, CaseExpectationResult, CaseOutcome, DirectiveParser,
    FailureStage, FixtureCase, PrimaryExpectation, StageFailure,
    apply_bless_patches, evaluate_case, format_stage, parse_fixture_file,
};
pub use digest::{sha256_bytes, sha256_hex};
pub use mir_wp_fixture::{
    CORE_WP_CLAIMS, MirWpFixtureSpec, PUBLIC_MIR_ALIASES, SYNTHETIC_CANARIES,
    SyntheticCanary,
};
pub use process::{
    Invocation, ProcessOutcome, ProcessSupervisor, Termination,
    ensure_child_subreaper, reject_symlink_components, write_json,
    write_regular_file,
};
pub use store_sim::{
    Elf64Info, ElfStoreBuilder, ElfStoreCell, FiveCellElfLayout,
    SimulatedStoreConfig, inspect_elf64, run_in_simulated_nix_store,
};
pub use toolchain::{
    ToolchainEnv, ToolchainMode, cargo_subcommand_invocation,
    default_lean_path, default_rust_sysroot, lean_prefix,
};
pub use workspace::{
    Building, ExecutedRun, RawOutput, ReadOnlyTreeGuard, StagedWorkspace,
    WorkspaceBuilder,
};

/// Result alias used across `anneal-testkit` scaffolding and test suites.
pub type TestResult<T = ()> = Result<T, String>;
