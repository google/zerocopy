// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Standalone integration test runner for `anneal_audit::check_cargo_boundary`,
//! delegating to the shared cases also executed by `boundary_audit`.

mod cargo_boundary_cases;

#[test]
fn accepts_real_repository_cargo_boundary() {
    cargo_boundary_cases::assert_accepts_real_repository();
}

#[test]
fn accepts_valid_explicit_implicit_targets_and_in_member_rust_closure() {
    cargo_boundary_cases::assert_accepts_valid_explicit_implicit_targets_and_in_member_rust_closure(
    );
}

#[cfg(unix)]
#[test]
fn rejects_symlinked_and_hardlinked_member_directories_and_files() {
    cargo_boundary_cases::assert_rejects_symlinked_and_hardlinked_directories_and_files();
}

#[test]
fn distinguishes_workspace_members_from_workspace_exclude() {
    cargo_boundary_cases::assert_distinguishes_workspace_members_from_workspace_exclude();
}

#[cfg(unix)]
#[test]
fn rejects_symlinked_implicit_and_explicit_target_sources() {
    cargo_boundary_cases::assert_rejects_symlinked_implicit_and_explicit_target_sources();
}

#[test]
fn rejects_manifest_targets_edition_doctest_proc_macros_dep_renames_and_auto_fields() {
    cargo_boundary_cases::assert_rejects_manifest_targets_edition_doctest_proc_macros_dep_renames_and_auto_fields();
}

#[test]
fn rejects_rust_source_closure_escapes_and_smuggling() {
    cargo_boundary_cases::assert_rejects_rust_source_closure_escapes_and_smuggling();
}

#[test]
fn rejects_case_folded_aliases_unlisted_overrides_submodules_and_manifest_bidi() {
    cargo_boundary_cases::assert_rejects_case_folded_aliases_unlisted_overrides_submodules_and_manifest_bidi();
}

#[test]
fn requires_text_mode_root_manifest_and_rejects_tampering() {
    cargo_boundary_cases::assert_requires_text_mode_root_manifest_and_rejects_tampering();
}
