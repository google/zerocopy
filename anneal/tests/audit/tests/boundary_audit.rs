// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Integration tests for the `trusted/audit` repository boundary gate and
//! `TrustedBoundary.lean` kernel-environment inspector.
//!
//! The tests live in domain submodules under `tests/boundary_audit/`, which
//! share this file's imports through `use super::*`. They stay in this one
//! test target so that the slow-test overrides in `.config/nextest.toml`,
//! which select the `boundary_audit` binary, keep applying to them.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    env, fs,
    os::unix::fs::symlink,
    path::{Path, PathBuf},
    process::Command,
};

use anneal_audit::{
    CandidateFeature, Checker, ImportEdge, InspectorRequest, Json, MiriClosureEntry,
    ModuleArtifacts, PARTS, TrustTier, bundle, check_cargo_boundary, default_lean_path,
    ensure_miri_cache_outside_checkout, scan_lean_tree, sha256_bytes, sha256_file,
    verify_sysroot_foundation_dir,
};
use anneal_testkit::mir_wp_fixture::MirWpFixtureSpec;
use serde_json::json;

mod common;
use common::{
    HEADER, TempFixture, compile_forged_module, copy_cargo_workspace, copy_dir_all,
    correspondence_dsl::{
        ClaimsSpec, CorrAuditRequestBuilder, CorrespondenceHarness, ProofsSpec,
        REQUIRED_MIRI_PRIMITIVES, VALID_BYTES_CODEC_DEF, VALID_D11_DEF, VALID_D12_DEF,
        VALID_D13_DEF, assert_policy_rejection,
    },
    repo_root, run_lean_script,
};

#[path = "boundary_audit/bundle_parity_and_dag.rs"]
mod bundle_parity_and_dag;
#[path = "boundary_audit/cargo_boundary.rs"]
mod cargo_boundary;
#[path = "boundary_audit/compiler_overrides.rs"]
mod compiler_overrides;
#[path = "boundary_audit/forged_olean_replay.rs"]
mod forged_olean_replay;
#[path = "boundary_audit/foundation_and_sysroot.rs"]
mod foundation_and_sysroot;
#[path = "boundary_audit/pass1_cpp_semantics.rs"]
mod pass1_cpp_semantics;
#[path = "boundary_audit/pass1_mir_wp_gates.rs"]
mod pass1_mir_wp_gates;
#[path = "boundary_audit/pass1_preflight.rs"]
mod pass1_preflight;
#[path = "boundary_audit/pass1_tiers_and_theory.rs"]
mod pass1_tiers_and_theory;
#[path = "boundary_audit/pass1_universes_and_framework.rs"]
mod pass1_universes_and_framework;
#[path = "boundary_audit/pass2_correspondence_audit.rs"]
mod pass2_correspondence_audit;
#[path = "boundary_audit/pass2_correspondence_non_backsliding.rs"]
mod pass2_correspondence_non_backsliding;
#[path = "boundary_audit/pass2_import_graph.rs"]
mod pass2_import_graph;
#[path = "boundary_audit/pass2_miri_cache_and_sandbox.rs"]
mod pass2_miri_cache_and_sandbox;
#[path = "boundary_audit/pass2_miri_pin.rs"]
mod pass2_miri_pin;
#[path = "boundary_audit/pass2_module_isolation.rs"]
mod pass2_module_isolation;
#[path = "boundary_audit/pass2_syntax_preflight.rs"]
mod pass2_syntax_preflight;

fn materialize_mir_wp(spec: &MirWpFixtureSpec) -> TempFixture {
    let fix = TempFixture::new(Some(HEADER));
    spec.materialize_into(&fix.inner).unwrap();
    fix
}
