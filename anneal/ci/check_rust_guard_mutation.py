# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Guard-mutation CI check for Anneal's Rust TCB crates.

Why this check exists
---------------------

Positive unit and integration tests cannot catch a silent weakening or
accidental deletion of a Rust Trusted Computing Base (TCB) security guard
unless a negative test directly depends on that exact check. If a refactor
drops a Cargo boundary check, relaxes a root-manifest or bundle digest check,
permits an unapproved Lean axiom, disables a symlink/`O_NOFOLLOW` rejection, or
omits Tier 1 `bwrap --seccomp` flags, happy-path tests continue passing while
trust invariants quietly erode.

This script closes that blind spot by performing single-guard mutation testing
in isolated temporary copies (never modifying the repository working tree):

1. Against the unmodified staged workspace, every baseline
   `cargo test --locked` binary/lib target compiles and every targeted guard
   test passes with at least one executed test.
2. For each cataloged `RustGuard`, the runner weakens only that single guard
   inside a temporary copy, verifies via `cargo test --locked ... --no-run` that
   the mutated crate STILL compiles cleanly (so syntax or type errors are
   reported as `ERROR` and never masquerade as kills), and confirms that the
   guard's targeted `--exact` test fails cleanly with `FAILED`.
3. The check exits `0` only if 100% of cataloged guards are killed.

What this check guarantees — and what it does NOT guarantee
-----------------------------------------------------------

- **Guarantees:** Every security guard listed in `RUST_GUARDS` is active under
  its configured mutation, compiles when weakened, and is exercised by its
  targeted `anneal-audit` or `cargo-anneal` test.
- **Does NOT guarantee:** Coverage of uncataloged branches, Lean-side checks
  (covered by `ci/check_guard_mutation.py`), or `rustc-capture/` / `stage.rs` /
  `olean_cache.rs` internals excluded from this standalone harness.

How to add a new guard
----------------------

Whenever adding a new security guard under `trusted/audit/src/` or
`trusted/cargo-anneal/src/`:

1. Add a focused test in the crate's unit or integration test suite that fails
   when that guard is bypassed.
2. Add a `RustGuard` entry in `RUST_GUARDS` whose `anchor` uniquely matches the
   live source and whose `replacement` weakens only that guard cleanly without
   introducing compile errors.
3. Run `python3 -I -B ci/check_rust_guard_mutation.py` and confirm a 100% kill
   rate (`0` survived, `0` errors).
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, dataclass
import json
import os
from pathlib import Path
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import time


ALLOWED_SUITES: dict[str, tuple[str, str]] = {
    "anneal_audit": ("anneal-audit", "trusted/audit/"),
    "cargo_anneal": ("cargo-anneal", "trusted/cargo-anneal/"),
}

# Integration tests (`--test <name>`) reside in non-TCB Zone-1 test crates
# under `anneal/tests/` that depend on the mutated `trusted/` crates.
INTEGRATION_TEST_PACKAGES: dict[str, tuple[str, str]] = {
    "anneal-audit": ("anneal-audit-tests", "tests/audit"),
    "cargo-anneal": ("cargo-anneal-tests", "tests/cargo-anneal"),
}

EXCLUDED_TARGET_SUBSTRINGS: tuple[str, ...] = (
    "stage.rs",
    "olean_cache.rs",
    "rustc-capture",
)


@dataclass(frozen=True)
class RustGuard:
    """Single-guard mutation entry targeting a Rust TCB crate."""

    guard_id: str
    suite: str  # "anneal_audit" | "cargo_anneal"
    target_file: str  # path relative to `anneal/`
    description: str
    anchor: str
    replacement: str
    package: str  # "anneal-audit" | "cargo-anneal"
    test_args: tuple[str, ...]
    test_name: str


@dataclass(frozen=True)
class GuardResult:
    """Outcome of executing one Rust guard-mutation check."""

    suite: str
    guard_id: str
    target_file: str
    status: str  # KILLED | SURVIVED | ERROR
    duration_sec: float
    detail: str


RUST_GUARDS: tuple[RustGuard, ...] = (
    # ------------------------------------------------------------------
    # anneal-audit: cargo_boundary.rs (7 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="cargo_boundary_member_outside_trusted",
        suite="anneal_audit",
        target_file="trusted/audit/src/cargo_boundary.rs",
        description="Reject Cargo workspace members outside trusted/ or tests/",
        anchor=(
            "    } else {\n"
            "        Err(Failure::new(\n"
            "            1,\n"
            '            "cargo-boundary",\n'
            '            format!("workspace member outside trusted/ or tests/: {rel_path}"),\n'
            "        ))\n"
            "    }"
        ),
        replacement="    } else {\n        Ok(WorkspaceZone::Trusted)\n    }",
        package="anneal-audit",
        test_args=("--test", "boundary_audit"),
        test_name="rejects_cargo_workspace_members_and_path_deps_outside_trusted",
    ),
    RustGuard(
        guard_id="cargo_boundary_path_dep_outside_trusted",
        suite="anneal_audit",
        target_file="trusted/audit/src/cargo_boundary.rs",
        description="Reject workspace member path dependencies pointing outside trusted/ or tests/",
        anchor=(
            "        let dst_zone = classify_member_zone(&rel_str).map_err(|_| {\n"
            "            Failure::new(\n"
            "                1,\n"
            "                phase,\n"
            '                format!("{member} path dependency points outside trusted/ or tests/: {rel_str}"),\n'
            "            )\n"
            "        })?;"
        ),
        replacement="        let dst_zone = classify_member_zone(&rel_str).unwrap_or(WorkspaceZone::Trusted);",
        package="anneal-audit",
        test_args=("--test", "boundary_audit"),
        test_name="rejects_cargo_workspace_members_and_path_deps_outside_trusted",
    ),
    RustGuard(
        guard_id="cargo_boundary_root_manifest_digest",
        suite="anneal_audit",
        target_file="trusted/audit/src/cargo_boundary.rs",
        description="Reject root-manifest.sha256 SHA-256 digest mismatch on root build files",
        anchor=(
            "        if !actual_hex.eq_ignore_ascii_case(expected_hex) {\n"
            "            return Err(Failure::new("
        ),
        replacement="        if false {\n            return Err(Failure::new(",
        package="anneal-audit",
        test_args=("--test", "boundary_audit"),
        test_name="rejects_cargo_workspace_members_and_path_deps_outside_trusted",
    ),
    RustGuard(
        guard_id="cargo_boundary_cargo_lock_source",
        suite="anneal_audit",
        target_file="trusted/audit/src/cargo_boundary.rs",
        description="Reject non-crates.io external sources in Cargo.lock",
        anchor=(
            "            Some(other_src) => {\n"
            "                return Err(Failure::new(\n"
            "                    1,\n"
            "                    phase,\n"
            "                    format!(\n"
            '                        "untrusted dependency source in Cargo.lock for {pkg_name}: {other_src}"\n'
            "                    ),\n"
            "                ));\n"
            "            }"
        ),
        replacement=(
            "            Some(other_src) => {\n"
            "                let _ = (pkg_name, other_src);\n"
            "            }"
        ),
        package="anneal-audit",
        test_args=("--test", "boundary_audit"),
        test_name="rejects_cargo_workspace_members_and_path_deps_outside_trusted",
    ),
    RustGuard(
        guard_id="cargo_boundary_cargo_lock_rogue_local",
        suite="anneal_audit",
        target_file="trusted/audit/src/cargo_boundary.rs",
        description="Reject source-less local packages in Cargo.lock outside workspace members",
        anchor=(
            "                if pkg.checksum.is_some() || !member_pkg_names.contains(pkg_name) {\n"
            "                    return Err(Failure::new("
        ),
        replacement="                if false {\n                    return Err(Failure::new(",
        package="anneal-audit",
        test_args=("--test", "boundary_audit"),
        test_name="rejects_cargo_workspace_members_and_path_deps_outside_trusted",
    ),
    RustGuard(
        guard_id="cargo_boundary_bundled_resources_parity",
        suite="anneal_audit",
        target_file="trusted/audit/src/cargo_boundary.rs",
        description="Reject drifted compiled-in cargo-anneal BUNDLE bytes",
        anchor=(
            "        if exp_path != emb_path || exp_src.as_str() != *emb_src {\n"
            "            return Err(Failure::policy("
        ),
        replacement="        if false {\n            return Err(Failure::policy(",
        package="anneal-audit",
        test_args=("--test", "boundary_audit"),
        test_name="enforces_bundled_resources_parity_and_regular_files",
    ),
    RustGuard(
        guard_id="cargo_boundary_legacy_bundled_resources_absent",
        suite="anneal_audit",
        target_file="trusted/audit/src/cargo_boundary.rs",
        description="Reject reintroduced legacy src/bundled_resources.rs",
        anchor=(
            "    let legacy_destination = checkout.join(LEGACY_BUNDLE_DESTINATION);\n"
            "    match fs::symlink_metadata(&legacy_destination) {\n"
            "        Ok(_) => {\n"
            "            return Err(Failure::policy(\n"
            "                phase,\n"
            "                format!(\n"
            '                    "legacy checked-in bundled_resources.rs must be absent: {}",\n'
            "                    legacy_destination.display()\n"
            "                ),\n"
            "            ));\n"
            "        }"
        ),
        replacement=(
            "    let legacy_destination = checkout.join(LEGACY_BUNDLE_DESTINATION);\n"
            "    match fs::symlink_metadata(&legacy_destination) {\n"
            "        Ok(_) => {}"
        ),
        package="anneal-audit",
        test_args=("--test", "boundary_audit"),
        test_name="enforces_bundled_resources_parity_and_regular_files",
    ),
    # ------------------------------------------------------------------
    # anneal-audit: miri_pin.rs (5 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="miri_pin_unauthorized_patched_file",
        suite="anneal_audit",
        target_file="trusted/audit/src/miri_pin.rs",
        description="Reject unauthorized patched files outside LOCKED_PATCHED_MIRI_FILES",
        anchor=(
            "        if !LOCKED_PATCHED_MIRI_FILES.contains(&pf.path.as_str()) {\n"
            "            return Err(Failure::policy(\n"
            "                phase,\n"
            "                format!(\n"
            '                    "unauthorized patched file in UPSTREAM_PIN.json: {}",'
        ),
        replacement=(
            "        if false {\n"
            "            return Err(Failure::policy(\n"
            "                phase,\n"
            "                format!(\n"
            '                    "unauthorized patched file in UPSTREAM_PIN.json: {}",'
        ),
        package="anneal-audit",
        test_args=("--lib",),
        test_name="miri_pin::tests::rejects_unauthorized_patched_files_and_bad_closure_in_pin_bytes",
    ),
    RustGuard(
        guard_id="miri_pin_nosymlink_cache_root",
        suite="anneal_audit",
        target_file="trusted/audit/src/miri_pin.rs",
        description="Reject symlinked Miri .olean cache root directory",
        anchor=(
            "    match fs::symlink_metadata(cache_dir) {\n"
            "        Ok(meta) => {\n"
            "            if !meta.file_type().is_dir() {\n"
            "                return Err(Failure::policy(\n"
            "                    phase,\n"
            "                    format!(\n"
            '                        "cache root must be a regular directory (not a symlink or file): {}",'
        ),
        replacement=(
            "    match fs::symlink_metadata(cache_dir) {\n"
            "        Ok(meta) => {\n"
            "            let _ = meta;\n"
            "            if false {\n"
            "                return Err(Failure::policy(\n"
            "                    phase,\n"
            "                    format!(\n"
            '                        "cache root must be a regular directory (not a symlink or file): {}",'
        ),
        package="anneal-audit",
        test_args=("--lib",),
        test_name="miri_pin::tests::rejects_symlinks_in_miri_cache_dir",
    ),
    RustGuard(
        guard_id="miri_pin_nosymlink_cache_entry",
        suite="anneal_audit",
        target_file="trusted/audit/src/miri_pin.rs",
        description="Reject symlink or non-regular file at Miri cache leaf entry",
        anchor=(
            "fn ensure_cache_dst_regular_or_absent(dst: &Path, phase: &str) -> Result<CacheEntryState, Failure> {\n"
            "    match fs::symlink_metadata(dst) {\n"
            "        Ok(meta) => {\n"
            "            if meta.file_type().is_symlink() || !meta.file_type().is_file() {"
        ),
        replacement=(
            "fn ensure_cache_dst_regular_or_absent(dst: &Path, phase: &str) -> Result<CacheEntryState, Failure> {\n"
            "    match fs::symlink_metadata(dst) {\n"
            "        Ok(meta) => {\n"
            "            let _ = meta;\n"
            "            if false {"
        ),
        package="anneal-audit",
        test_args=("--lib",),
        test_name="miri_pin::tests::rejects_symlinks_in_miri_cache_dir",
    ),
    RustGuard(
        guard_id="miri_pin_cache_outside_checkout",
        suite="anneal_audit",
        target_file="trusted/audit/src/miri_pin.rs",
        description="Reject --miri-cache-dir paths residing inside checkout",
        anchor=(
            "    if lexical_cache.starts_with(&canonical_checkout)\n"
            "        || resolved_cache.starts_with(&canonical_checkout)\n"
            "    {"
        ),
        replacement="    if false {",
        package="anneal-audit",
        test_args=("--test", "boundary_audit"),
        test_name="rejects_miri_cache_dir_inside_checkout",
    ),
    RustGuard(
        guard_id="miri_pin_source_lock_stray_hash",
        suite="anneal_audit",
        target_file="trusted/audit/src/miri_pin.rs",
        description="Reject stray **HASH** annotations outside the allowlisted legacy record",
        anchor=(
            "            LegacyStrayHash::Null | LegacyStrayHash::NonNull => {\n"
            "                return Err(Failure::policy(\n"
            "                    phase,\n"
            "                    format!(\n"
            '                        "unexpected `**HASH**` field in `{section}` record for {}",\n'
            "                        record.path\n"
            "                    ),\n"
            "                ));\n"
            "            }"
        ),
        replacement=(
            "            LegacyStrayHash::Null | LegacyStrayHash::NonNull => {\n"
            "                let _ = record;\n"
            "            }"
        ),
        package="anneal-audit",
        test_args=("--test", "boundary_audit"),
        test_name="verifies_source_lock_schema_and_rejects_malformed_records",
    ),
    # ------------------------------------------------------------------
    # anneal-audit: repo_audit.rs (3 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="repo_audit_correspondence_miri_replay",
        suite="anneal_audit",
        target_file="trusted/audit/src/repo_audit.rs",
        description="Require miriReplay == true in correspondence audit report",
        anchor=(
            '    if result.get("miriReplay").and_then(Json::as_bool) != Some(true) {\n'
            "        return Err(Failure::policy(\n"
            "            phase,\n"
            '            "correspondence audit did not confirm vendor Miri kernel replay",\n'
            "        ));\n"
            "    }"
        ),
        replacement="    if false {\n        return Err(Failure::policy(phase, \"disabled\"));\n    }",
        package="anneal-audit",
        test_args=("--lib",),
        test_name="repo_audit::tests::validates_correspondence_replay_fields_fail_closed",
    ),
    RustGuard(
        guard_id="repo_audit_correspondence_count_parity",
        suite="anneal_audit",
        target_file="trusted/audit/src/repo_audit.rs",
        description="Require replayed correspondence declaration count to equal declared count",
        anchor=(
            "    if corr_replayed != corr_decls {\n"
            "        return Err(Failure::policy("
        ),
        replacement="    if false {\n        return Err(Failure::policy(",
        package="anneal-audit",
        test_args=("--lib",),
        test_name="repo_audit::tests::validates_correspondence_replay_fields_fail_closed",
    ),
    RustGuard(
        guard_id="repo_audit_preflight_vetted_tier_isolation",
        suite="anneal_audit",
        target_file="trusted/audit/src/repo_audit.rs",
        description="Enforce module-level trust-tier isolation on vetted module imports",
        anchor=(
            "                if !foundation_graph.contains_key(imp_mod) {\n"
            "                    match module_tiers.get(imp_mod) {"
        ),
        replacement=(
            "                if false {\n"
            "                    match module_tiers.get(imp_mod) {"
        ),
        package="anneal-audit",
        test_args=("--lib",),
        test_name="repo_audit::tests::preflight_tier_imports_isolate_vetted_modules",
    ),
    # ------------------------------------------------------------------
    # cargo-anneal: sandbox.rs (6 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="sandbox_reject_forbidden_loader_env",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/core/elf.rs",
        description="Block dynamic linker environment variables (LD_*, DYLD_*) in sandbox extra_env",
        anchor=(
            "        if FORBIDDEN_LOADER_ENV_PREFIXES.iter().any(|prefix| key.starts_with(prefix)) {\n"
            "            return Err(Failure::operational("
        ),
        replacement="        if false {\n            return Err(Failure::operational(",
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="sandbox::tests::reject_forbidden_loader_env_blocks_ld_and_dyld_overrides",
    ),
    RustGuard(
        guard_id="sandbox_pt_interp_reject_reserved_bwrap_roots",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/sandbox.rs",
        description="Reject reserved bwrap child mount roots (/work, /toolchain, /dev, /proc, /etc) for PT_INTERP dirs",
        anchor=(
            "    if is_reserved_bwrap_child_path(dir) {\n"
            "        return Err(Failure::operational(\n"
            '            "sandbox",\n'
            '            format!("refusing reserved sandbox path {} as {role}", dir.display()),\n'
            "        ));\n"
            "    }"
        ),
        replacement=(
            "    if false {\n"
            "        return Err(Failure::operational(\n"
            '            "sandbox",\n'
            '            format!("refusing reserved sandbox path {} as {role}", dir.display()),\n'
            "        ));\n"
            "    }"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="sandbox::tests::resolve_pt_interp_lib_dirs_skips_standard_allows_custom_sysroot_and_rejects_broad_roots",
    ),
    RustGuard(
        guard_id="sandbox_path_mapper_reject_parent_traversal",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/sandbox.rs",
        description="Reject `..` path traversal components in sandbox PathMapper",
        anchor=(
            "    fn map_bwrap_exact(&self, path: &Path) -> Option<PathBuf> {\n"
            "        if Self::has_parent_dir(path) {\n"
            "            return None;\n"
            "        }"
        ),
        replacement=(
            "    fn map_bwrap_exact(&self, path: &Path) -> Option<PathBuf> {\n"
            "        let _ = Self::has_parent_dir(path);\n"
            "        if false {\n"
            "            return None;\n"
            "        }"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="sandbox::tests::path_mapper_maps_bwrap_roots_and_rejects_unmounted_paths",
    ),
    RustGuard(
        guard_id="sandbox_door1_reject_extra_inspector_output",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/sandbox.rs",
        description="Reject unexpected extra files in TrustedBoundary inspector out_dir in Door 1",
        anchor=(
            "    if entries.len() != 1 || entries[0].0 != expected_filename {\n"
            '        let names: Vec<&str> = entries.iter().map(|(n, _)| n.as_str()).collect();\n'
            "        return Err(Failure::operational(\n"
            '            "door1",\n'
            "            format!(\n"
            '                "unexpected inspector outputs in {}: expected [{expected_filename}], found {names:?}",'
        ),
        replacement=(
            "    if false {\n"
            '        let names: Vec<&str> = entries.iter().map(|(n, _)| n.as_str()).collect();\n'
            "        return Err(Failure::operational(\n"
            '            "door1",\n'
            "            format!(\n"
            '                "unexpected inspector outputs in {}: expected [{expected_filename}], found {names:?}",'
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="sandbox::tests::door1_inspector_result_handles_empty_valid_and_extra_files",
    ),
    RustGuard(
        guard_id="sandbox_door1_require_olean_v2_magic",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/core/identifiers.rs",
        description="Enforce strict v2 .olean magic header check in validate_olean_v2_header",
        anchor=(
            "    if &prefix[..OLEAN_V2_MAGIC.len()] != OLEAN_V2_MAGIC {\n"
            "        return Err(Failure::operational(\n"
            "            phase,\n"
            "            format!(\n"
            '                "unsupported or malformed .olean header in {label}: expected v2 magic {:02x?}, got {:02x?}",'
        ),
        replacement=(
            "    if false {\n"
            "        return Err(Failure::operational(\n"
            "            phase,\n"
            "            format!(\n"
            '                "unsupported or malformed .olean header in {label}: expected v2 magic {:02x?}, got {:02x?}",'
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="sandbox::tests::door1_rejects_non_v2_olean_headers",
    ),
    RustGuard(
        guard_id="sandbox_bwrap_attach_seccomp_flag",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/sandbox.rs",
        description="Attach --seccomp BPF filter FD to Tier 1 bwrap command",
        anchor=(
            "        if let Some(fd) = &seccomp_read_fd {\n"
            '            cmd.arg("--seccomp").arg(fd.as_raw_fd().to_string());\n'
            "        }"
        ),
        replacement="        let _ = &seccomp_read_fd;",
        package="cargo-anneal",
        test_args=("--test", "sandbox_escape"),
        test_name="tier1_bwrap_enforces_seccomp_and_disables_nested_userns",
    ),
    # ------------------------------------------------------------------
    # cargo-anneal: toolchain.rs (4 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="toolchain_unpinned_reject_non_init_std",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/toolchain.rs",
        description="Restrict unpinned sysroot modules strictly to Init and Std namespaces",
        anchor='&& matches!(module.split(\'.\').next(), Some("Init" | "Std"))',
        replacement="&& true",
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="toolchain::unpinned_sysroot_tests::sysroot_guard_rejects_lean_lake_and_non_init_std_modules",
    ),
    RustGuard(
        guard_id="toolchain_unpinned_foundation_init_only",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/toolchain.rs",
        description="Ensure unpinned foundation closure cannot escape Init.* into Std.*",
        anchor=(
            '        if module.split(\'.\').next() != Some("Init") {\n'
            "            return Err(Failure::policy(\n"
            '                "sysroot",\n'
            '                format!("foundation closure exceeded Init.*: {module}"),'
        ),
        replacement=(
            "        if false {\n"
            "            return Err(Failure::policy(\n"
            '                "sysroot",\n'
            '                format!("foundation closure exceeded Init.*: {module}"),'
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="toolchain::unpinned_sysroot_tests::sysroot_guard_rejects_lean_lake_and_non_init_std_modules",
    ),
    RustGuard(
        guard_id="toolchain_unpinned_require_foundation_closure",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/toolchain.rs",
        description="Require all six Init foundation modules in unpinned foundation closure",
        anchor=(
            "    for required in UNPINNED_FOUNDATION_MODULES {\n"
            "        if !closure.contains(required) {\n"
            "            return Err(Failure::policy(\n"
            '                "sysroot",\n'
            '                format!("missing required foundation module {required}"),'
        ),
        replacement=(
            "    for required in UNPINNED_FOUNDATION_MODULES {\n"
            "        if false {\n"
            "            return Err(Failure::policy(\n"
            '                "sysroot",\n'
            '                format!("missing required foundation module {required}"),'
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="toolchain::unpinned_sysroot_tests::foundation_closure_rejects_missing_core_or_foundation_modules",
    ),
    RustGuard(
        guard_id="toolchain_open_regular_o_nofollow",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/sys_util.rs",
        description="Open regular files with O_NOFOLLOW | O_NONBLOCK to reject symlinks and FIFOs",
        anchor="        opts.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);",
        replacement="        opts.custom_flags(libc::O_NONBLOCK);",
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="toolchain::unpinned_sysroot_tests::safe_regular_file_primitives_reject_fifos_without_blocking",
    ),
    # ------------------------------------------------------------------
    # cargo-anneal: verify.rs (6 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="verify_taint_monoid_unsandboxed",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/verify.rs",
        description="Record UnsandboxedElaboration taint whenever --allow-unsandboxed-elaboration is set",
        anchor=(
            "    if args.allow_unsandboxed_elaboration {\n"
            "        taints.insert(VerificationTaint::UnsandboxedElaboration);\n"
            "    }"
        ),
        replacement=(
            "    if false {\n"
            "        taints.insert(VerificationTaint::UnsandboxedElaboration);\n"
            "    }"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="verify::tests::taint_monoid_projects_all_eight_flag_subsets_canonically",
    ),
    RustGuard(
        guard_id="verify_audit_require_replay_and_exact_type",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/verify.rs",
        description="Require kernel replay == true and exactType == true in target audit receipt",
        anchor=(
            '    if audit.get("replay").and_then(Value::as_bool) != Some(true)\n'
            '        || audit.get("exactType").and_then(Value::as_bool) != Some(true)\n'
            "    {"
        ),
        replacement="    if false {",
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="verify::tests::validate_sorry_declarations_enforces_flag_and_axiom_consistency",
    ),
    RustGuard(
        guard_id="verify_audit_reject_unapproved_axiom",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/verify.rs",
        description="Reject axioms outside the closed three-axiom allowlist",
        anchor="        } else if !ALLOWED_AXIOMS.contains(&name) {",
        replacement="        } else if false {",
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="verify::tests::validate_sorry_declarations_enforces_flag_and_axiom_consistency",
    ),
    RustGuard(
        guard_id="verify_reject_compiler_overrides",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/verify.rs",
        description="Reject Cargo/toolchain override files and dangling symlinks under target crate",
        anchor=(
            '            Ok(meta) if forbidden != ".cargo" || !meta.is_dir() => {\n'
            "                return Err(error(\n"
            '                    "unsupported",\n'
            '                    "cargo",\n'
            '                    "compiler overrides need an explicit configured compilation",\n'
            "                ));\n"
            "            }"
        ),
        replacement=(
            "            Ok(meta) => {\n"
            "                let _ = meta;\n"
            "            }"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="verify::tests::compiler_override_check_rejects_dangling_and_directory_symlinks",
    ),
    RustGuard(
        guard_id="verify_reserved_proof_module",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/verify.rs",
        description="Block authored proof/spec modules from claiming runner-owned or Lean namespaces",
        anchor='Some("Trusted" | "Anneal" | "Init" | "Std" | "Lean" | "Lake" | "TrustedBoundary")',
        replacement='Some("Expected")',
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="verify::tests::proof_modules_cannot_claim_runner_owned_names",
    ),
    RustGuard(
        guard_id="verify_env_binding_reject_equals_smuggling",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/verify.rs",
        description="Reject `--env` binding keys containing `=` to prevent arg smuggling",
        anchor=(
            "    if key.contains('=') {\n"
            "        return Err(format!(\"environment variable name must not contain '=': {key:?}\"));\n"
            "    }"
        ),
        replacement=(
            "    if false {\n"
            "        return Err(format!(\"environment variable name must not contain '=': {key:?}\"));\n"
            "    }"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="verify::tests::env_binding_validation_blocks_empty_keys_equals_smuggling_and_nul",
    ),
    # ------------------------------------------------------------------
    # cargo-anneal: bundle.rs (3 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="bundle_theory_sha256_parity",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/bundle.rs",
        description="Reject embedded bundled_theory.json entries with tampered SHA-256 digests",
        anchor=(
            "        if actual != entry.sha256 {\n"
            "            return Err(BundleError::Policy(format!(\n"
            '                "embedded theory bundle SHA-256 mismatch for {}: expected {}, got {actual}",'
        ),
        replacement=(
            "        let _ = actual;\n"
            "        if false {\n"
            "            return Err(BundleError::Policy(format!(\n"
            '                "embedded theory bundle SHA-256 mismatch for {}: expected {}, got {actual}",'
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="bundle::tests::parse_bundled_theory_rejects_tampered_and_invalid_payloads",
    ),
    RustGuard(
        guard_id="bundle_theory_require_mir_wp",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/bundle.rs",
        description="Require core theory/Anneal/MirWp.lean module in bundled theory manifest",
        anchor=(
            "    if !has_required {\n"
            "        return Err(BundleError::Policy(format!(\n"
            '            "{label} missing required theory module: {REQUIRED_THEORY_BUNDLE_PATH}"'
        ),
        replacement=(
            "    let _ = has_required;\n"
            "    if false {\n"
            "        return Err(BundleError::Policy(format!(\n"
            '            "{label} missing required theory module: {REQUIRED_THEORY_BUNDLE_PATH}"'
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="bundle::tests::parse_bundled_theory_rejects_tampered_and_invalid_payloads",
    ),
    RustGuard(
        guard_id="bundle_theory_require_anneal_subdir",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/bundle.rs",
        description="Reject top-level theory/Anneal.lean or non-Anneal module paths in theory bundle",
        anchor=(
            "    if components.len() < 2\n"
            '        || components[0] != "Anneal"\n'
            "        || !components.iter().copied().all(is_lean_ident)\n"
            "    {"
        ),
        replacement="    let _ = components;\n    if false {",
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="bundle::tests::parse_bundled_theory_rejects_tampered_and_invalid_payloads",
    ),
)


def apply_single_guard_mutation(
    source_text: str,
    anchor: str,
    replacement: str,
    *,
    guard_id: str,
) -> str:
    """Replace `anchor` with `replacement`, requiring exactly one occurrence."""
    occurrences = source_text.count(anchor)
    if occurrences != 1:
        raise ValueError(
            f"guard {guard_id!r}: expected anchor to match exactly once, "
            f"found {occurrences} occurrences"
        )
    if anchor == replacement:
        raise ValueError(
            f"guard {guard_id!r}: replacement must differ from anchor"
        )
    return source_text.replace(anchor, replacement, 1)


def _crate_dir_for_package(anneal_root: Path, package: str) -> Path:
    if package == "anneal-audit":
        return anneal_root / "trusted/audit"
    if package == "cargo-anneal":
        return anneal_root / "trusted/cargo-anneal"
    raise ValueError(f"unknown package {package!r}")


def _test_package_and_dir_for_guard(
    anneal_root: Path, guard: RustGuard
) -> tuple[str, Path]:
    """Return `(cargo_package, crate_dir)` where `guard`'s test lives."""
    if len(guard.test_args) == 2 and guard.test_args[0] == "--test":
        if guard.package not in INTEGRATION_TEST_PACKAGES:
            raise ValueError(f"no integration test crate for {guard.package!r}")
        test_pkg, test_rel = INTEGRATION_TEST_PACKAGES[guard.package]
        return test_pkg, anneal_root / test_rel
    return guard.package, _crate_dir_for_package(anneal_root, guard.package)


def _find_rust_test_function(
    anneal_root: Path,
    guard: RustGuard,
    file_cache: dict[Path, str] | None = None,
) -> Path | None:
    """Locate the Rust test function matching `guard.test_name`, if present."""
    _, crate_dir = _test_package_and_dir_for_guard(anneal_root, guard)
    leaf = guard.test_name.rsplit("::", 1)[-1]
    fn_re = re.compile(rf"^\s*(?:pub\s+)?fn\s+{re.escape(leaf)}\s*\(", re.MULTILINE)
    if guard.test_args == ("--lib",) or (
        len(guard.test_args) == 2 and guard.test_args[0] == "--bin"
    ):
        candidates = sorted((crate_dir / "src").rglob("*.rs"))
    elif len(guard.test_args) == 2 and guard.test_args[0] == "--test":
        candidates = [crate_dir / "tests" / f"{guard.test_args[1]}.rs"]
    else:
        return None
    for path in candidates:
        if not path.is_file():
            continue
        if file_cache is not None and path in file_cache:
            content = file_cache[path]
        else:
            content = path.read_text(encoding="utf-8")
            if file_cache is not None:
                file_cache[path] = content
        if fn_re.search(content):
            return path
    return None


def validate_catalog_invariants(anneal_root: Path) -> list[str]:
    """Validate static Rust guard catalog invariants without invoking Cargo."""
    errors: list[str] = []
    if len(RUST_GUARDS) < 18:
        errors.append(
            f"expected >= 18 Rust guards, found {len(RUST_GUARDS)}"
        )

    seen_ids: set[str] = set()
    suite_counts = {suite: 0 for suite in ALLOWED_SUITES}
    file_cache: dict[Path, str] = {}

    for guard in RUST_GUARDS:
        if guard.guard_id in seen_ids:
            errors.append(f"duplicate guard_id: {guard.guard_id}")
        seen_ids.add(guard.guard_id)

        if guard.suite not in ALLOWED_SUITES:
            errors.append(f"{guard.guard_id}: unknown suite {guard.suite!r}")
            continue
        expected_pkg, expected_prefix = ALLOWED_SUITES[guard.suite]
        suite_counts[guard.suite] += 1

        if guard.package != expected_pkg:
            errors.append(
                f"{guard.guard_id}: suite {guard.suite!r} expects package "
                f"{expected_pkg!r}, got {guard.package!r}"
            )
        if not guard.target_file.startswith(expected_prefix):
            errors.append(
                f"{guard.guard_id}: target_file {guard.target_file!r} must "
                f"start with {expected_prefix!r}"
            )
        for excluded in EXCLUDED_TARGET_SUBSTRINGS:
            if excluded in guard.target_file:
                errors.append(
                    f"{guard.guard_id}: target_file touches excluded path "
                    f"{excluded!r}: {guard.target_file}"
                )
        if not guard.test_name.strip():
            errors.append(f"{guard.guard_id}: test_name must be non-empty")
        valid_lib = guard.test_args == ("--lib",)
        valid_bin = (
            len(guard.test_args) == 2
            and guard.test_args[0] == "--bin"
            and bool(guard.test_args[1].strip())
        )
        valid_int = (
            len(guard.test_args) == 2
            and guard.test_args[0] == "--test"
            and bool(guard.test_args[1].strip())
        )
        if not (valid_lib or valid_bin or valid_int):
            errors.append(
                f"{guard.guard_id}: invalid test_args {guard.test_args!r}"
            )

        target_path = anneal_root / guard.target_file
        if not target_path.is_file():
            errors.append(f"{guard.guard_id}: missing target_file {target_path}")
        else:
            if target_path not in file_cache:
                file_cache[target_path] = target_path.read_text(encoding="utf-8")
            text = file_cache[target_path]
            try:
                apply_single_guard_mutation(
                    text,
                    guard.anchor,
                    guard.replacement,
                    guard_id=guard.guard_id,
                )
            except ValueError as exc:
                errors.append(str(exc))

        if (valid_lib or valid_bin or valid_int) and _find_rust_test_function(
            anneal_root, guard, file_cache
        ) is None:
            _, test_crate_dir = _test_package_and_dir_for_guard(anneal_root, guard)
            errors.append(
                f"{guard.guard_id}: test function for {guard.test_name!r} "
                f"not found under {test_crate_dir}"
            )

    for suite, count in suite_counts.items():
        if count == 0:
            errors.append(f"suite {suite!r} has zero cataloged guards")

    return errors


_RUNNING_RE = re.compile(r"^running\s+(\d+)\s+tests?\b", re.MULTILINE)
_RESULT_RE = re.compile(
    r"^test result:\s+(ok|FAILED)\.\s+(\d+)\s+passed;\s+(\d+)\s+failed;",
    re.MULTILINE,
)


def classify_rust_test_outcome(
    returncode: int,
    combined_output: str,
    test_name: str,
) -> tuple[str, str]:
    """Classify a `cargo test ... -- --exact <test_name>` run strictly.

    Returns `(status, detail)` where `status` is `KILLED`, `SURVIVED`, or
    `ERROR`. Test-count `0`, compiler/harness failures, and signals never pass
    on baseline or masquerade as mutant kills.
    """
    if returncode < 0:
        return (
            "ERROR",
            f"cargo test terminated by signal {-returncode}",
        )

    running_matches = [int(m.group(1)) for m in _RUNNING_RE.finditer(combined_output)]
    result_matches = list(_RESULT_RE.finditer(combined_output))
    if not running_matches or not result_matches:
        return (
            "ERROR",
            f"missing cargo test runner summary (rc={returncode}): "
            f"{combined_output.strip()[:260]}",
        )

    ran = running_matches[-1]
    res_match = result_matches[-1]
    summary_word = res_match.group(1)
    passed_count = int(res_match.group(2))
    failed_count = int(res_match.group(3))

    if ran == 0 or (passed_count + failed_count) == 0:
        return (
            "ERROR",
            f"0 tests executed for --exact {test_name}",
        )

    test_pass_re = re.compile(
        rf"^\s*test\s+{re.escape(test_name)}\s+\.\.\.\s+ok\b",
        re.MULTILINE,
    )
    test_fail_re = re.compile(
        rf"^\s*test\s+{re.escape(test_name)}\s+\.\.\.\s+FAILED\b",
        re.MULTILINE,
    )

    if (
        returncode == 0
        and summary_word == "ok"
        and failed_count == 0
        and passed_count >= 1
        and test_pass_re.search(combined_output)
    ):
        return (
            "SURVIVED",
            f"targeted test {test_name} still passed ({passed_count} passed)",
        )

    if (
        returncode == 101
        and summary_word == "FAILED"
        and failed_count >= 1
        and test_fail_re.search(combined_output)
    ):
        return (
            "KILLED",
            f"targeted test {test_name} failed cleanly ({failed_count} failed)",
        )

    return (
        "ERROR",
        f"unexpected cargo test outcome rc={returncode} summary={summary_word!r} "
        f"passed={passed_count} failed={failed_count}: "
        f"{combined_output.strip()[:240]}",
    )


def _select_guards(
    suite: str,
    name_filter: str | None,
) -> list[RustGuard]:
    guards = [
        g
        for g in RUST_GUARDS
        if suite == "all" or g.suite == suite
    ]
    if name_filter:
        guards = [g for g in guards if name_filter in g.guard_id]
    return guards


def _run_cargo(
    cargo_bin: Path,
    args: list[str],
    *,
    cwd: Path,
    target_dir: Path,
    timeout_sec: int,
) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["CARGO_TARGET_DIR"] = str(target_dir)
    # Disable color noise for deterministic parsing.
    env["CARGO_TERM_COLOR"] = "never"
    return subprocess.run(
        [str(cargo_bin), *args],
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout_sec,
    )


def _bump_mtime_if_needed(path: Path, prev_mtime_ns: int) -> None:
    """Advance file mtime by 1 ms if unchanged so Cargo never skips rebuild."""
    st = path.stat()
    if st.st_mtime_ns <= prev_mtime_ns:
        os.utime(path, ns=(st.st_atime_ns, prev_mtime_ns + 1_000_000))


def _check_one_guard(
    guard: RustGuard,
    *,
    cargo_bin: Path,
    worker_pool: queue.Queue[tuple[Path, Path]],
    timeout_sec: int,
) -> GuardResult:
    t0 = time.monotonic()
    worker_anneal, worker_target = worker_pool.get()
    try:
        src_path = worker_anneal / guard.target_file
        if src_path.is_symlink():
            raise RuntimeError(f"refusing symlinked target file: {src_path}")
        orig_bytes = src_path.read_bytes()
        orig_text = orig_bytes.decode("utf-8")
        try:
            mutated_text = apply_single_guard_mutation(
                orig_text,
                guard.anchor,
                guard.replacement,
                guard_id=guard.guard_id,
            )
        except ValueError as exc:
            return GuardResult(
                suite=guard.suite,
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status="ERROR",
                duration_sec=time.monotonic() - t0,
                detail=str(exc),
            )

        pre_stat = src_path.stat()
        try:
            src_path.write_text(mutated_text, encoding="utf-8")
            _bump_mtime_if_needed(src_path, pre_stat.st_mtime_ns)

            # Gate 1 (Anti-fake-kill): compile target first with `--no-run`.
            # Any compile error must report `ERROR`, never `KILLED`.
            test_package, _ = _test_package_and_dir_for_guard(worker_anneal, guard)
            compile_args = [
                "test",
                "--locked",
                "-p",
                test_package,
                *guard.test_args,
                "--no-run",
            ]
            try:
                comp = _run_cargo(
                    cargo_bin,
                    compile_args,
                    cwd=worker_anneal,
                    target_dir=worker_target,
                    timeout_sec=timeout_sec,
                )
            except subprocess.TimeoutExpired:
                return GuardResult(
                    suite=guard.suite,
                    guard_id=guard.guard_id,
                    target_file=guard.target_file,
                    status="ERROR",
                    duration_sec=time.monotonic() - t0,
                    detail=f"mutant compile timed out after {timeout_sec}s",
                )

            if comp.returncode != 0:
                combined_comp = (comp.stdout + "\n" + comp.stderr).strip()
                return GuardResult(
                    suite=guard.suite,
                    guard_id=guard.guard_id,
                    target_file=guard.target_file,
                    status="ERROR",
                    duration_sec=time.monotonic() - t0,
                    detail=(
                        f"mutated crate failed to compile (rc={comp.returncode}): "
                        f"{combined_comp[:300]}"
                    ),
                )

            # Gate 2: execute targeted test with `-- --exact`.
            test_args = [
                "test",
                "--locked",
                "-p",
                test_package,
                *guard.test_args,
                "--",
                "--exact",
                guard.test_name,
            ]
            try:
                test_res = _run_cargo(
                    cargo_bin,
                    test_args,
                    cwd=worker_anneal,
                    target_dir=worker_target,
                    timeout_sec=timeout_sec,
                )
            except subprocess.TimeoutExpired:
                return GuardResult(
                    suite=guard.suite,
                    guard_id=guard.guard_id,
                    target_file=guard.target_file,
                    status="ERROR",
                    duration_sec=time.monotonic() - t0,
                    detail=f"targeted test timed out after {timeout_sec}s",
                )

            combined = test_res.stdout + "\n" + test_res.stderr
            status, detail = classify_rust_test_outcome(
                test_res.returncode, combined, guard.test_name
            )
            return GuardResult(
                suite=guard.suite,
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                status=status,
                duration_sec=time.monotonic() - t0,
                detail=detail,
            )
        finally:
            mut_mtime = src_path.stat().st_mtime_ns
            src_path.write_bytes(orig_bytes)
            _bump_mtime_if_needed(src_path, mut_mtime)
    finally:
        worker_pool.put((worker_anneal, worker_target))


def run_rust_guard_mutation_suite(
    *,
    anneal_root: Path,
    cargo_bin: Path,
    suite: str = "all",
    name_filter: str | None = None,
    jobs: int = 4,
    timeout_sec: int = 120,
) -> dict[str, object]:
    """Validate baseline builds/tests and execute all selected Rust guard checks."""
    t_start = time.monotonic()
    catalog_errors = validate_catalog_invariants(anneal_root)
    if catalog_errors:
        raise RuntimeError(
            "Rust guard catalog validation failed:\n  - "
            + "\n  - ".join(catalog_errors)
        )

    guards = _select_guards(suite, name_filter)
    if not guards:
        raise RuntimeError(
            f"no Rust guards matched suite={suite!r} filter={name_filter!r}"
        )

    ignore_patterns = shutil.ignore_patterns("target", ".lake", "__pycache__", ".git")
    with tempfile.TemporaryDirectory(prefix="anneal-rgmut-") as root_tmp:
        root_path = Path(root_tmp)
        base_root = root_path / "worker-0"
        base_anneal = base_root / "anneal"
        base_target = base_root / "target"
        base_root.mkdir()
        base_target.mkdir()
        shutil.copytree(
            anneal_root,
            base_anneal,
            ignore=ignore_patterns,
            symlinks=True,
        )

        t_base = time.monotonic()
        # 1. Baseline compile per distinct `(test_package, test_args)` target.
        seen_builds: set[tuple[str, tuple[str, ...]]] = set()
        for g in guards:
            test_pkg, _ = _test_package_and_dir_for_guard(base_anneal, g)
            key = (test_pkg, g.test_args)
            if key in seen_builds:
                continue
            seen_builds.add(key)
            comp = _run_cargo(
                cargo_bin,
                ["test", "--locked", "-p", test_pkg, *g.test_args, "--no-run"],
                cwd=base_anneal,
                target_dir=base_target,
                timeout_sec=timeout_sec,
            )
            if comp.returncode != 0:
                raise RuntimeError(
                    f"baseline build failed for {test_pkg} {' '.join(g.test_args)}:\n"
                    f"{comp.stdout}\n{comp.stderr}"
                )

        # 2. Verify each distinct baseline targeted test passes (>= 1 test).
        seen_tests: set[tuple[str, tuple[str, ...], str]] = set()
        for g in guards:
            test_pkg, _ = _test_package_and_dir_for_guard(base_anneal, g)
            tkey = (test_pkg, g.test_args, g.test_name)
            if tkey in seen_tests:
                continue
            seen_tests.add(tkey)
            base_res = _run_cargo(
                cargo_bin,
                [
                    "test",
                    "--locked",
                    "-p",
                    test_pkg,
                    *g.test_args,
                    "--",
                    "--exact",
                    g.test_name,
                ],
                cwd=base_anneal,
                target_dir=base_target,
                timeout_sec=timeout_sec,
            )
            combined = base_res.stdout + "\n" + base_res.stderr
            cls_status, cls_detail = classify_rust_test_outcome(
                base_res.returncode, combined, g.test_name
            )
            if cls_status != "SURVIVED":
                raise RuntimeError(
                    f"baseline test failed for {test_pkg} {g.test_name}: "
                    f"[{cls_status}] {cls_detail}"
                )
        baseline_sec = time.monotonic() - t_base

        # 3. Seed worker checkout + warm target copies for `--jobs > 1`.
        worker_count = max(1, min(jobs, len(guards)))
        worker_pool: queue.Queue[tuple[Path, Path]] = queue.Queue()
        worker_pool.put((base_anneal, base_target))
        for idx in range(1, worker_count):
            w_root = root_path / f"worker-{idx}"
            w_anneal = w_root / "anneal"
            w_target = w_root / "target"
            w_root.mkdir()
            shutil.copytree(base_anneal, w_anneal, symlinks=True)
            shutil.copytree(base_target, w_target, symlinks=True)
            worker_pool.put((w_anneal, w_target))

        # 4. Run single-guard mutations concurrently across worker workspaces.
        by_id: dict[str, GuardResult] = {}
        with ThreadPoolExecutor(max_workers=worker_count) as pool:
            futs = {
                pool.submit(
                    _check_one_guard,
                    g,
                    cargo_bin=cargo_bin,
                    worker_pool=worker_pool,
                    timeout_sec=timeout_sec,
                ): g
                for g in guards
            }
            for fut in as_completed(futs):
                res = fut.result()
                by_id[res.guard_id] = res

    results = [by_id[g.guard_id] for g in guards]
    total = len(results)
    killed = sum(1 for r in results if r.status == "KILLED")
    survived = sum(1 for r in results if r.status == "SURVIVED")
    errors = sum(1 for r in results if r.status == "ERROR")
    return {
        "total": total,
        "killed": killed,
        "survived": survived,
        "errors": errors,
        "kill_rate_pct": (100.0 * killed / total) if total else 0.0,
        "baseline_sec": round(baseline_sec, 3),
        "total_sec": round(time.monotonic() - t_start, 3),
        "results": [asdict(r) for r in results],
    }


def _default_anneal_root() -> Path:
    return Path(__file__).resolve().parent.parent


def _resolve_cargo_binary(explicit: Path | None) -> Path:
    if explicit is not None:
        if not explicit.is_file():
            raise SystemExit(f"Cargo binary not found: {explicit}")
        return explicit
    for env_key in ("ANNEAL_CARGO", "CARGO"):
        val = os.environ.get(env_key)
        if val:
            cand = Path(val)
            if cand.is_file():
                return cand
    found = shutil.which("cargo")
    if found:
        return Path(found)
    raise SystemExit(
        "Cargo binary not specified; pass --cargo <path> or set ANNEAL_CARGO / CARGO"
    )


def _format_summary(report: dict[str, object]) -> str:
    lines: list[str] = []
    for entry in report["results"]:  # type: ignore[index]
        lines.append(
            f"[{entry['status']:8s}] ({entry['suite']:12s}) "
            f"{entry['guard_id']:42s} {entry['duration_sec']:5.2f}s  "
            f"{entry['detail']}"
        )
    lines.append(
        f"Rust guard-mutation summary: {report['killed']}/{report['total']} killed "
        f"({report['kill_rate_pct']:.1f}%), {report['survived']} survived, "
        f"{report['errors']} errors "
        f"(baseline {report['baseline_sec']:.2f}s, total {report['total_sec']:.2f}s)"
    )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Run single-guard mutation checks against trusted/audit/src/ "
            "and trusted/cargo-anneal/src/."
        )
    )
    parser.add_argument(
        "--anneal-root",
        type=Path,
        default=_default_anneal_root(),
        help="Path to the `anneal/` directory (defaults to script parent).",
    )
    parser.add_argument(
        "--cargo",
        type=Path,
        default=None,
        help="Path to the `cargo` executable (falls back to ANNEAL_CARGO / CARGO / PATH).",
    )
    parser.add_argument(
        "--suite",
        choices=("all", *ALLOWED_SUITES),
        default="all",
        help="Which Rust guard-mutation suite(s) to execute.",
    )
    parser.add_argument(
        "--filter",
        dest="name_filter",
        default=None,
        help="Optional substring filter on guard_id.",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=min(4, os.cpu_count() or 1),
        help="Maximum parallel worker workspaces (default: min(4, CPU count)).",
    )
    parser.add_argument(
        "--timeout-sec",
        type=int,
        default=120,
        help="Per-Cargo-invocation timeout in seconds (default: 120).",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=None,
        help="Optional file path to write the structured JSON report.",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="Validate static catalog invariants, list all guards, and exit.",
    )
    args = parser.parse_args(argv)

    if args.jobs < 1:
        parser.error("--jobs must be >= 1")
    if args.timeout_sec < 1:
        parser.error("--timeout-sec must be >= 1")

    if args.list:
        errors = validate_catalog_invariants(args.anneal_root)
        if errors:
            for err in errors:
                print(f"ERROR: {err}", file=sys.stderr)
            return 1
        selected = _select_guards(args.suite, args.name_filter)
        for g in selected:
            print(f"{g.suite:14s} {g.guard_id:42s} {g.target_file}")
        print(f"Total cataloged Rust guards: {len(selected)}")
        return 0

    cargo_bin = _resolve_cargo_binary(args.cargo)
    try:
        report = run_rust_guard_mutation_suite(
            anneal_root=args.anneal_root,
            cargo_bin=cargo_bin,
            suite=args.suite,
            name_filter=args.name_filter,
            jobs=args.jobs,
            timeout_sec=args.timeout_sec,
        )
    except RuntimeError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1

    print(_format_summary(report))
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8"
        )

    if report["killed"] != report["total"] or report["errors"] != 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
