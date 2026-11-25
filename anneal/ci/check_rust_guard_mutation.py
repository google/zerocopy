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
  targeted `anneal-audit`, `cargo-anneal`, or `anneal-rustc-capture` test.
- **Does NOT guarantee:** Coverage of uncataloged branches or Lean-side checks
  (covered by `ci/check_guard_mutation.py`).

How to add a new guard
----------------------

Whenever adding a new security guard under `trusted/audit/src/`,
`trusted/cargo-anneal/src/`, or `trusted/rustc-capture/src/`:

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
    "rustc_capture": ("anneal-rustc-capture", "trusted/rustc-capture/"),
}

WORKSPACE_SUITES: frozenset[str] = frozenset({"anneal_audit", "cargo_anneal"})

SUITE_CHOICES: tuple[str, ...] = (
    "all",
    "workspace",
    *ALLOWED_SUITES,
)

# Integration tests (`--test <name>`) reside in non-TCB Zone-1 test crates
# under `anneal/tests/` that depend on the mutated `trusted/` crates.
INTEGRATION_TEST_PACKAGES: dict[str, tuple[str, str]] = {
    "anneal-audit": ("anneal-audit-tests", "tests/audit"),
    "cargo-anneal": ("cargo-anneal-tests", "tests/cargo-anneal"),
    "anneal-rustc-capture": ("anneal-rustc-capture-tests", "tests/rustc-capture"),
}

DEFAULT_NIGHTLY_TOOLCHAIN = "nightly-2026-05-31"


@dataclass(frozen=True)
class RustGuard:
    """Single-guard mutation entry targeting a Rust TCB crate."""

    guard_id: str
    suite: str  # "anneal_audit" | "cargo_anneal" | "rustc_capture"
    target_file: str  # path relative to `anneal/`
    description: str
    anchor: str
    replacement: str
    package: str  # "anneal-audit" | "cargo-anneal" | "anneal-rustc-capture"
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
    # ------------------------------------------------------------------
    # cargo-anneal: stage.rs (6 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="stage_compile_args_disable_auto_implicit",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/stage.rs",
        description="Pass -DautoImplicit=false and -DrelaxedAutoImplicit=false when requested for specs",
        anchor=(
            "    if disable_auto_implicit {\n"
            "        // Prevent undeclared typos in `TargetRole::Specification` signatures\n"
            "        // from silently binding universally quantified auto-implicit variables.\n"
            '        compile_args.push("-DautoImplicit=false".to_string());\n'
            '        compile_args.push("-DrelaxedAutoImplicit=false".to_string());\n'
            "    }"
        ),
        replacement=(
            "    let _ = disable_auto_implicit;\n"
            "    if false {\n"
            '        compile_args.push("-DautoImplicit=false".to_string());\n'
            '        compile_args.push("-DrelaxedAutoImplicit=false".to_string());\n'
            "    }"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="stage::process_tests::build_lean_compile_args_disables_auto_implicit_only_when_requested",
    ),
    RustGuard(
        guard_id="stage_launch_lean_env_clear",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/stage.rs",
        description="Clear ambient host environment variables before launching Lean child processes",
        anchor="        cmd.args(arguments).current_dir(&self.stage).env_clear().envs(&self.environment);",
        replacement="        cmd.args(arguments).current_dir(&self.stage).envs(&self.environment);",
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="stage::process_tests::launches_with_only_the_filtered_environment",
    ),
    RustGuard(
        guard_id="stage_export_oleans_gated_rejects_symlink_dest",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/stage.rs",
        description="Reject symlink or non-directory export destinations before clearing",
        anchor=(
            "            Ok(meta) if meta.file_type().is_symlink() || !meta.file_type().is_dir() => {\n"
            "                return Err(Failure::operational(\n"
            '                    "export-lean-lib",\n'
            '                    format!("unexpected non-directory destination {}", dest.display()),\n'
            "                ));\n"
            "            }"
        ),
        replacement=(
            "            Ok(meta) if false && meta.file_type().is_symlink() => {\n"
            "                return Err(Failure::operational(\n"
            '                    "export-lean-lib",\n'
            '                    format!("unexpected non-directory destination {}", dest.display()),\n'
            "                ));\n"
            "            }"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="stage::process_tests::export_target_oleans_gated_rejects_invalid_and_trailing_slash_symlink_dests",
    ),
    RustGuard(
        guard_id="stage_export_oleans_gated_ledger_hash_check",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/stage.rs",
        description="Reject promoted .olean artifacts whose SHA-256 changed before gated export",
        anchor=(
            "            if !actual_sha.eq_ignore_ascii_case(expected_sha) {\n"
            "                return Err(Failure::operational(\n"
            '                    "export-lean-lib",\n'
            "                    format!(\n"
            '                        "promoted artifact {} changed before export",\n'
            "                        entry.path().display()\n"
            "                    ),\n"
            "                ));\n"
            "            }"
        ),
        replacement=(
            "            let _ = (&actual_sha, expected_sha);\n"
            "            if false {\n"
            "                return Err(Failure::operational(\n"
            '                    "export-lean-lib",\n'
            "                    format!(\n"
            '                        "promoted artifact {} changed before export",\n'
            "                        entry.path().display()\n"
            "                    ),\n"
            "                ));\n"
            "            }"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="stage::process_tests::export_target_oleans_gated_is_atomic_on_validation_failure",
    ),
    RustGuard(
        guard_id="stage_export_oleans_gated_missing_artifact_check",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/stage.rs",
        description="Fail closed when a ledgered .olean artifact is missing before gated export",
        anchor=(
            "        for ledger_path in expected_ledger_paths {\n"
            "            if !validated_ledger.contains(ledger_path) {\n"
            "                return Err(Failure::operational(\n"
            '                    "export-lean-lib",\n'
            "                    format!(\n"
            '                        "promoted artifact {} missing before export",'
        ),
        replacement=(
            "        for ledger_path in expected_ledger_paths {\n"
            "            if false {\n"
            "                return Err(Failure::operational(\n"
            '                    "export-lean-lib",\n'
            "                    format!(\n"
            '                        "promoted artifact {} missing before export",'
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="stage::process_tests::export_target_oleans_gated_is_atomic_on_validation_failure",
    ),
    RustGuard(
        guard_id="stage_verify_artifact_ledger_inspector_olean",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/stage.rs",
        description="Reject tampered precompiled TrustedBoundary.olean in artifact ledger check",
        anchor=(
            "        if let Some((olean_path, expected_olean_sha)) = &adm.inspector_olean {\n"
            '            let actual = sha256_file(olean_path, "artifact-ledger")?;\n'
            "            if !actual.eq_ignore_ascii_case(expected_olean_sha) {"
        ),
        replacement=(
            "        if let Some((olean_path, expected_olean_sha)) = &adm.inspector_olean {\n"
            '            let actual = sha256_file(olean_path, "artifact-ledger")?;\n'
            "            let _ = (&actual, expected_olean_sha);\n"
            "            if false {"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="stage::process_tests::artifact_ledger_catches_tampered_inspector_olean",
    ),
    # ------------------------------------------------------------------
    # cargo-anneal: target.rs (5 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="target_audit_report_require_replay_and_exact_type",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/target.rs",
        description="Require replay == true and exactType == true in target-audit report",
        anchor=(
            "    if !report.replay || !report.exact_type {\n"
            "        return Err(Failure::operational(\n"
            '            "target-audit",\n'
            "            format!(\n"
            '                "target-audit did not certify replay and exactType (replay={}, exactType={})",'
        ),
        replacement=(
            "    if false {\n"
            "        return Err(Failure::operational(\n"
            '            "target-audit",\n'
            "            format!(\n"
            '                "target-audit did not certify replay and exactType (replay={}, exactType={})",'
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="target::tests::target_audit_report_schema_rejects_unknown_fields_mismatches_and_unapproved_axioms",
    ),
    RustGuard(
        guard_id="target_audit_report_reject_unapproved_axiom",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/target.rs",
        description="Reject target axioms outside ALLOWED_TARGET_FOUNDATION_AXIOMS",
        anchor="        } else if !ALLOWED_TARGET_FOUNDATION_AXIOMS.contains(&ax.as_str()) {",
        replacement="        } else if false {",
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="target::tests::target_audit_report_schema_rejects_unknown_fields_mismatches_and_unapproved_axioms",
    ),
    RustGuard(
        guard_id="target_audit_report_reject_sorry_ax_without_flag",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/target.rs",
        description="Reject sorryAx in target-audit report unless allow_sorry_in_proof is enabled",
        anchor=(
            '        if ax == "sorryAx" {\n'
            "            if !request.allow_sorry_in_proof {\n"
            "                return Err(Failure::operational("
        ),
        replacement=(
            '        if ax == "sorryAx" {\n'
            "            if false {\n"
            "                return Err(Failure::operational("
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="target::tests::target_audit_report_schema_rejects_unknown_fields_mismatches_and_unapproved_axioms",
    ),
    RustGuard(
        guard_id="target_audit_report_reject_graph_mismatch",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/target.rs",
        description="Reject target-audit report whose import graph diverges from admitted DAG",
        anchor=(
            "    if &report.graph != expected_graph {\n"
            "        return Err(Failure::operational(\n"
            '            "target-audit",\n'
            '            "target-audit reported import graph differing from admitted DAG",'
        ),
        replacement=(
            "    if false {\n"
            "        return Err(Failure::operational(\n"
            '            "target-audit",\n'
            '            "target-audit reported import graph differing from admitted DAG",'
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="target::tests::target_audit_report_schema_rejects_unknown_fields_mismatches_and_unapproved_axioms",
    ),
    RustGuard(
        guard_id="target_run_target_reject_reserved_sysroot_module",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/target.rs",
        description="Reject target modules whose names collide with locked or reserved sysroot modules",
        anchor=(
            "            if !target_name_valid(&module.module)\n"
            "                || roles.contains_key(&module.module)\n"
            "                || collides_with_sysroot\n"
            "            {"
        ),
        replacement=(
            "            let _ = collides_with_sysroot;\n"
            "            if !target_name_valid(&module.module)\n"
            "                || roles.contains_key(&module.module)\n"
            "            {"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="target::admission_tests::run_target_rejects_modules_named_like_locked_modules",
    ),
    # ------------------------------------------------------------------
    # cargo-anneal: olean_cache.rs (5 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="olean_cache_key_sensitive_to_source_digest",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/olean_cache.rs",
        description="Bind .olean cache keys to the module source SHA-256 digest",
        anchor="        feed_len_str(&mut h, &self.source_sha256.to_ascii_lowercase());",
        replacement='        feed_len_str(&mut h, "fixed-source-sha");',
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="olean_cache::tests::cache_key_is_deterministic_and_sensitive_to_every_field",
    ),
    RustGuard(
        guard_id="olean_cache_key_sensitive_to_compile_flags",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/olean_cache.rs",
        description="Bind .olean cache keys to canonical compiler flags",
        anchor=(
            "        h.update((self.flags.len() as u64).to_le_bytes());\n"
            "        for flag in &self.flags {\n"
            "            feed_len_str(&mut h, flag);\n"
            "        }"
        ),
        replacement="        h.update(0u64.to_le_bytes());",
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="olean_cache::tests::cache_key_is_deterministic_and_sensitive_to_every_field",
    ),
    RustGuard(
        guard_id="olean_cache_key_sensitive_to_import_digest",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/olean_cache.rs",
        description="Bind .olean cache keys to transitive import artifact SHA-256 digests",
        anchor="                feed_len_str(&mut h, &sha.to_ascii_lowercase());",
        replacement='                feed_len_str(&mut h, "fixed-import-sha");',
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="olean_cache::tests::cache_key_is_deterministic_and_sensitive_to_every_field",
    ),
    RustGuard(
        guard_id="olean_cache_verify_part_sha256_mismatch",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/olean_cache.rs",
        description="Reject cached .olean parts whose bytes fail SHA-256 verification",
        anchor=(
            "        if !actual_sha.eq_ignore_ascii_case(&part.sha256) {\n"
            "            return Err(Failure::operational(\n"
            '                "olean-cache",\n'
            "                format!(\n"
            '                    "cached artifact SHA-256 mismatch for {} (expected {}, got {})",'
        ),
        replacement=(
            "        if false {\n"
            "            return Err(Failure::operational(\n"
            '                "olean-cache",\n'
            "                format!(\n"
            '                    "cached artifact SHA-256 mismatch for {} (expected {}, got {})",'
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="olean_cache::tests::disk_cache_roundtrip_tamper_and_no_rebuild_guards",
    ),
    RustGuard(
        guard_id="olean_cache_no_rebuild_bundled_fail_closed",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/olean_cache.rs",
        description="Fail closed on cache miss when --no-rebuild-bundled is set",
        anchor=(
            "        if self.no_rebuild_bundled {\n"
            "            let reason = if let Some(found_ver) = self.prebuilt_skipped_version {"
        ),
        replacement=(
            "        if false {\n"
            "            let reason = if let Some(found_ver) = self.prebuilt_skipped_version {"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="olean_cache::tests::disk_cache_roundtrip_tamper_and_no_rebuild_guards",
    ),
    RustGuard(
        guard_id="olean_cache_prebuilt_reject_symlink_parts",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/olean_cache.rs",
        description="Reject symlinks while resolving cached .olean parts via join_checked_non_symlink",
        anchor=(
            "        if meta.file_type().is_symlink() {\n"
            "            return Err(Failure::operational(\n"
            '                "olean-cache",\n'
            '                format!("refusing symlink in cache path {}", cur.display()),\n'
            "            ));\n"
            "        }"
        ),
        replacement=(
            "        if false {\n"
            "            return Err(Failure::operational(\n"
            '                "olean-cache",\n'
            '                format!("refusing symlink in cache path {}", cur.display()),\n'
            "            ));\n"
            "        }"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="olean_cache::tests::prebuilt_manifest_precedes_disk_cache_and_rejects_symlinks",
    ),
    # ------------------------------------------------------------------
    # cargo-anneal: setup.rs (2 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="setup_reject_archive_incomplete_marker",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/setup.rs",
        description="Reject toolchain archives containing a reserved top-level .incomplete marker",
        anchor=(
            "    if new_entries\n"
            "        .iter()\n"
            "        .any(|name| name == OsStr::new(INCOMPLETE_MARKER))\n"
            "    {"
        ),
        replacement=(
            "    let _ = &new_entries;\n"
            "    if false\n"
            "    {"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="setup::tests::rejects_archive_containing_reserved_incomplete_marker",
    ),
    RustGuard(
        guard_id="setup_reinstall_reject_symlink_install_root",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/setup.rs",
        description="Reject symlinked toolchain installation paths before replacing entries",
        anchor=(
            "        Ok(meta) if meta.file_type().is_symlink() => {\n"
            "            return Err(io::Error::new(\n"
            "                io::ErrorKind::AlreadyExists,\n"
            '                "installation path is a symlink",\n'
            "            ));\n"
            "        }"
        ),
        replacement=(
            "        Ok(meta) if false && meta.file_type().is_symlink() => {\n"
            "            return Err(io::Error::new(\n"
            "                io::ErrorKind::AlreadyExists,\n"
            '                "installation path is a symlink",\n'
            "            ));\n"
            "        }"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="setup::tests::reinstall_rejects_symlink_and_non_directory_install_paths",
    ),
    # ------------------------------------------------------------------
    # cargo-anneal: init.rs (2 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="init_ensure_non_symlink_dir_rejects_symlink",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/init.rs",
        description="Refuse symlink target directory components when scaffolding starter Anneal files",
        anchor=(
            "            if lmeta.file_type().is_symlink() {\n"
            '                return Err(format!("refusing symlink directory {}", prefix.display()));\n'
            "            }"
        ),
        replacement=(
            "            if false {\n"
            '                return Err(format!("refusing symlink directory {}", prefix.display()));\n'
            "            }"
        ),
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="init::tests::standalone_mode_scaffolds_runnable_example_and_refuses_symlinks",
    ),
    RustGuard(
        guard_id="init_write_create_new_refuses_overwrite",
        suite="cargo_anneal",
        target_file="trusted/cargo-anneal/src/init.rs",
        description="Refuse overwriting pre-existing starter Spec.lean or Proof.lean files",
        anchor=(
            "            Ok(_) => {\n"
            '                return Err(format!("refusing to overwrite existing file {}", dest.display()));\n'
            "            }"
        ),
        replacement="            Ok(_) => {}",
        package="cargo-anneal",
        test_args=("--lib",),
        test_name="init::tests::cargo_mode_requires_package_manifest_and_creates_proof_files_once",
    ),
    # ------------------------------------------------------------------
    # anneal-rustc-capture: capture.rs (7 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="rustc_capture_args_reject_response_file",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/capture.rs",
        description="Reject compiler @response-file arguments during capture",
        anchor=(
            "        if arg.starts_with('@') {\n"
            "            return Err(Failure::tool("
        ),
        replacement="        if false {\n            return Err(Failure::tool(",
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="capture::tests::compiler_args_gate_rejects_extern_search_paths_response_files_and_proc_macro",
    ),
    RustGuard(
        guard_id="rustc_capture_args_reject_extern_search_paths",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/capture.rs",
        description="Reject --extern and -L library search path flags during capture",
        anchor=(
            '        if arg == "--extern" || arg.starts_with("--extern=") '
            '|| arg == "-L" || arg.starts_with("-L")\n'
            "        {"
        ),
        replacement="        if false\n        {",
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="capture::tests::compiler_args_gate_rejects_extern_search_paths_response_files_and_proc_macro",
    ),
    RustGuard(
        guard_id="rustc_capture_options_require_overflow_checks_no",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/capture.rs",
        description="Require explicit -Coverflow-checks=no during MIR capture",
        anchor=(
            "    if opts.cg.overflow_checks != Some(false) {\n"
            "        return Err(format!(\n"
            '            "-Coverflow-checks=no is required during capture (got {:?})",'
        ),
        replacement=(
            "    if false {\n"
            "        return Err(format!(\n"
            '            "-Coverflow-checks=no is required during capture (got {:?})",'
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="capture::tests::compiler_options_gate_enforces_opt_level_debug_assertions_and_overflow_checks",
    ),
    RustGuard(
        guard_id="rustc_capture_options_require_mir_preserve_ub",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/capture.rs",
        description="Require -Zmir-preserve-ub so PlaceMention/SwitchInt UB survives capture",
        anchor=(
            "    if !opts.unstable_opts.mir_preserve_ub {\n"
            '        return Err("-Zmir-preserve-ub must be enabled during capture".into());'
        ),
        replacement=(
            "    if false {\n"
            '        return Err("-Zmir-preserve-ub must be enabled during capture".into());'
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="capture::tests::compiler_options_gate_requires_mir_preserve_ub_and_matching_crate_type_and_panic",
    ),
    RustGuard(
        guard_id="rustc_capture_sysroot_crate_dev_ino",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/capture.rs",
        description="Enforce target sysroot (st_dev, st_ino) membership on external crates",
        anchor=(
            "        if !allowed_sysroot_ids.contains(&dev_ino) {\n"
            "            return Err(Failure::unsupported(format!(\n"
            '                "external crate {} resolved outside target sysroot: {}",'
        ),
        replacement=(
            "        if false && !allowed_sysroot_ids.contains(&dev_ino) {\n"
            "            return Err(Failure::unsupported(format!(\n"
            '                "external crate {} resolved outside target sysroot: {}",'
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="capture::tests::sysroot_only_crate_admission_enforces_sysroot_dev_ino_and_no_proc_macro",
    ),
    RustGuard(
        guard_id="rustc_capture_session_sysroot_toctou",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/capture.rs",
        description="Detect symlink retargeting TOCTOU divergence on session sysroot",
        anchor=(
            "    if sysroot != verified_sysroot || session_sysroot_id != verified_sysroot_id {\n"
            "        return Err(Failure::tool(\n"
            '            "compiler session sysroot diverged from verified sysroot",'
        ),
        replacement=(
            "    if false && (sysroot != verified_sysroot || session_sysroot_id != verified_sysroot_id) {\n"
            "        return Err(Failure::tool(\n"
            '            "compiler session sysroot diverged from verified sysroot",'
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="capture::tests::session_sysroot_check_detects_symlink_retargeting_toctou",
    ),
    RustGuard(
        guard_id="rustc_capture_env_depinfo_require_declared",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/capture.rs",
        description="Reject undeclared compile-time environment reads in dep-info gate",
        anchor=(
            "        let Some(expected) = declared.get(name) else {\n"
            "            return Err(Failure::unsupported(format!(\n"
            '                "environment-dependent source inputs are unsupported: undeclared variable {name}"\n'
            "            )));\n"
            "        };"
        ),
        replacement=(
            "        let Some(expected) = declared.get(name) else {\n"
            "            let _ = value;\n"
            "            continue;\n"
            "        };"
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="capture::tests::env_depinfo_gate_requires_exact_declared_bindings",
    ),
    # ------------------------------------------------------------------
    # anneal-rustc-capture: driver.rs (1 guard)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="rustc_capture_driver_require_analysis_callback",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/driver.rs",
        description="Require clean analysis callback before reporting compiler driver success",
        anchor=(
            "        if !callbacks.analysis_reached {\n"
            '            early_dcx.early_fatal("compiler returned without reaching a clean analysis callback");\n'
            "        }"
        ),
        replacement=(
            "        if false && !callbacks.analysis_reached {\n"
            '            early_dcx.early_fatal("compiler returned without reaching a clean analysis callback");\n'
            "        }"
        ),
        package="anneal-rustc-capture",
        test_args=("--test", "compiler_session"),
        test_name="compiler_information_is_not_callback_evidence",
    ),
    # ------------------------------------------------------------------
    # anneal-rustc-capture: extract.rs (3 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="rustc_capture_extract_rodata_immutability",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/extract.rs",
        description="Reject mutable global allocations when reading constant scalars",
        anchor=(
            "    if alloc.mutability != Mutability::Not {\n"
            '        return Err("mutable global allocations are unsupported in constants".into());\n'
            "    }"
        ),
        replacement=(
            "    if false {\n"
            '        return Err("mutable global allocations are unsupported in constants".into());\n'
            "    }"
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="extract::tests::rodata_global_alloc_reader_enforces_immutability_init_bounds_endian_and_no_provenance",
    ),
    RustGuard(
        guard_id="rustc_capture_extract_rodata_no_provenance",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/extract.rs",
        description="Reject pointer provenance in global allocation scalar constants",
        anchor=(
            "    if !alloc.provenance().range_empty(range, cx) {\n"
            '        return Err("provenance-bearing global allocation constants are unsupported".into());\n'
            "    }"
        ),
        replacement=(
            "    if false {\n"
            '        return Err("provenance-bearing global allocation constants are unsupported".into());\n'
            "    }"
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="extract::tests::rodata_global_alloc_reader_enforces_immutability_init_bounds_endian_and_no_provenance",
    ),
    RustGuard(
        guard_id="rustc_capture_extract_call_source_use",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/extract.rs",
        description="Reject CallSource::Use terminators to prevent post-capture clone rewrite",
        anchor=(
            "        mir::CallSource::Use => Err(\n"
            '            "CallSource::Use call terminators are unsupported: post-capture \\\n'
            "             optimize_use_clone may rewrite Clone::clone to a bitwise copy \\\n"
            '             for Copy types, diverging from captured MIR"\n'
            "                .into(),\n"
            "        ),"
        ),
        replacement="        mir::CallSource::Use => Ok(()),",
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="extract::tests::call_source_use_fails_closed_while_other_call_sources_pass_guard",
    ),
    # ------------------------------------------------------------------
    # anneal-rustc-capture: identity.rs (5 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="rustc_capture_identity_reject_loader_env",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/identity.rs",
        description="Reject LD_*/DYLD_* dynamic linker override env vars by presence",
        anchor=(
            "        if FORBIDDEN_LOADER_ENV_VARS.contains(&key_str) {\n"
            "            return Err(Failure::tool(format!(\n"
            '                "forbidden dynamic linker environment variable is set: {key_str}"\n'
            "            )));\n"
            "        }"
        ),
        replacement=(
            "        if false && FORBIDDEN_LOADER_ENV_VARS.contains(&key_str) {\n"
            "            return Err(Failure::tool(format!(\n"
            '                "forbidden dynamic linker environment variable is set: {key_str}"\n'
            "            )));\n"
            "        }"
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="identity::tests::loader_env_guards_behave_as_specified",
    ),
    RustGuard(
        guard_id="rustc_capture_identity_host_triple_traversal",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/identity.rs",
        description="Reject path-traversal or malformed host triples in sysroot driver scan",
        anchor=(
            "    loaded_dev_ino: (u64, u64),\n"
            ") -> Result<String, Failure> {\n"
            "    if !is_valid_host_triple(host) {\n"
            "        return Err(Failure::tool(format!(\n"
            '            "invalid rustc host triple: {host:?}"\n'
            "        )));\n"
            "    }"
        ),
        replacement=(
            "    loaded_dev_ino: (u64, u64),\n"
            ") -> Result<String, Failure> {\n"
            "    if false {\n"
            "        return Err(Failure::tool(format!(\n"
            '            "invalid rustc host triple: {host:?}"\n'
            "        )));\n"
            "    }"
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="identity::tests::symlinked_sysroot_matches_by_dev_ino_and_rejects_decoy_and_host_traversal",
    ),
    RustGuard(
        guard_id="rustc_capture_identity_runtime_symlink_dev_ino",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/identity.rs",
        description="Require runtime DSO mapping (st_dev, st_ino) to match resolved split symlinks",
        anchor=(
            "            && !maps_pathname_basename(pathname).is_some_and(is_toolchain_dso_filename)\n"
            "            && self.symlink_dev_inos.contains(&dev_ino)"
        ),
        replacement=(
            "            && !maps_pathname_basename(pathname).is_some_and(is_toolchain_dso_filename)\n"
            "            && {\n"
            "                let _ = dev_ino;\n"
            "                true\n"
            "            }"
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="identity::tests::runtime_closure_authenticates_split_symlinks_and_transitive_runpath",
    ),
    RustGuard(
        guard_id="rustc_capture_identity_exec_residency",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/identity.rs",
        description="Reject rogue executable VMAs outside sysroot and verified runtime closure",
        anchor=(
            "        } else if !runtime_closure.is_allowed(dev_ino, pathname) {\n"
            "            return Err(Failure::tool(format!(\n"
            '                "loaded executable mapping {} does not belong to verified sysroot {} or standard system libraries",'
        ),
        replacement=(
            "        } else if false && !runtime_closure.is_allowed(dev_ino, pathname) {\n"
            "            return Err(Failure::tool(format!(\n"
            '                "loaded executable mapping {} does not belong to verified sysroot {} or standard system libraries",'
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="identity::tests::closed_world_maps_residency_verifies_dso_closure_and_static_driver",
    ),
    RustGuard(
        guard_id="rustc_capture_identity_toolchain_dso_in_sysroot",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/identity.rs",
        description="Reject spliced toolchain DSOs (e.g. libLLVM) mapped from outside sysroot",
        anchor=(
            "        let Some((name, path)) = sysroot_libs.get(&dev_ino) else {\n"
            "            return Err(Failure::tool(format!(\n"
            '                "loaded toolchain DSO {} does not match any library in sysroot {}",\n'
            "                String::from_utf8_lossy(pathname),\n"
            "                sysroot.display()\n"
            "            )));\n"
            "        };"
        ),
        replacement=(
            "        let Some((name, path)) = sysroot_libs.get(&dev_ino) else {\n"
            "            let _ = pathname;\n"
            "            continue;\n"
            "        };"
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="identity::tests::closed_world_maps_residency_verifies_dso_closure_and_static_driver",
    ),
    # ------------------------------------------------------------------
    # anneal-rustc-capture: ir.rs (5 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="rustc_capture_ir_retag_guard",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/ir.rs",
        description="Refuse erasing non-noop WithRetag::Yes on reference-bearing types",
        anchor=(
            "fn admit_retag(retag_noop: bool, with_retag: bool) -> Result<(), String> {\n"
            "    if with_retag && !retag_noop {"
        ),
        replacement=(
            "fn admit_retag(retag_noop: bool, with_retag: bool) -> Result<(), String> {\n"
            "    if false && with_retag && !retag_noop {"
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="ir::tests::retag_guard_refuses_erasing_an_effective_retag",
    ),
    RustGuard(
        guard_id="rustc_capture_ir_place_mention_sizedness",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/ir.rs",
        description="Refuse admitting PlaceMention on unsized locals as a nop",
        anchor=(
            "fn admit_place_mention(is_sized: bool) -> Result<(), String> {\n"
            "    if !is_sized {"
        ),
        replacement=(
            "fn admit_place_mention(is_sized: bool) -> Result<(), String> {\n"
            "    if false && !is_sized {"
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="ir::tests::place_mention_guard_checks_local_bounds_and_sizedness",
    ),
    RustGuard(
        guard_id="rustc_capture_ir_validate_char_unicode_scalar",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/ir.rs",
        description="Enforce Unicode scalar validity for char constant literals",
        anchor=(
            "        (Ty::Char, ConstLit::Scalar { bits }) => {\n"
            "            if is_unicode_scalar(bits) {"
        ),
        replacement=(
            "        (Ty::Char, ConstLit::Scalar { bits }) => {\n"
            "            if { let _ = bits; true } {"
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="ir::tests::validate_constant_checks_all_ty_and_lit_combinations",
    ),
    RustGuard(
        guard_id="rustc_capture_ir_storage_dead_return_place",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/ir.rs",
        description="Reject StorageDead on return place _0 before Lean emission",
        anchor=(
            "                        if *local == 0 {\n"
            '                            return Err("StorageDead on return place _0 is unsupported".into());'
        ),
        replacement=(
            "                        if false && *local == 0 {\n"
            '                            return Err("StorageDead on return place _0 is unsupported".into());'
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="extract::tests::body_constructor_rejects_storage_dead_return_place_and_invalid_constants",
    ),
    RustGuard(
        guard_id="rustc_capture_ir_unique_program_identities",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/ir.rs",
        description="Reject duplicate captured function identities inside Program::try_new",
        anchor=(
            "            if !identities.insert(body.identity.as_str()) {\n"
            "                return Err(format!(\n"
            '                    "ambiguous captured function identity: {}",'
        ),
        replacement=(
            "            let _ = identities.insert(body.identity.as_str());\n"
            "            if false {\n"
            "                return Err(format!(\n"
            '                    "ambiguous captured function identity: {}",'
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="extract::tests::body_and_program_constructors_enforce_static_admission_and_unique_identities",
    ),
    # ------------------------------------------------------------------
    # anneal-rustc-capture: lean.rs (2 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="rustc_capture_lean_place_mention_renders_nop",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/lean.rs",
        description="Lower validated PlaceMention explicitly to Trusted.MirAst.StatementKind.nop",
        anchor='        Statement::PlaceMention { .. } | Statement::Nop => "Trusted.MirAst.StatementKind.nop".into(),',
        replacement=(
            '        Statement::PlaceMention { .. } => "Trusted.MirAst.StatementKind.placeMention".into(),\n'
            '        Statement::Nop => "Trusted.MirAst.StatementKind.nop".into(),'
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="lean::tests::render_lowers_validated_place_mention_and_nop_to_statement_kind_nop",
    ),
    RustGuard(
        guard_id="rustc_capture_lean_numeric_identity_encoding",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/lean.rs",
        description="Encode body identities strictly as numeric Char.ofNat character lists",
        anchor=(
            "            let chars_list =\n"
            '                list_literal(chunk, |ch| format!("(_root_.Char.ofNat {})", u32::from(*ch)));'
        ),
        replacement='            let chars_list = list_literal(chunk, |ch| format!("\'{ch}\'"));',
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="lean::tests::identity_names_are_only_numeric_character_data",
    ),
    # ------------------------------------------------------------------
    # anneal-rustc-capture: lib.rs (2 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="rustc_capture_lib_env_nul_rejection",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/lib.rs",
        description="Reject NUL bytes in declared --env KEY=VALUE bindings",
        anchor=(
            "    if key.contains('\\0') || value.contains('\\0') {\n"
            '        return Err("environment binding must not contain NUL bytes".to_owned());'
        ),
        replacement=(
            "    if false {\n"
            '        return Err("environment binding must not contain NUL bytes".to_owned());'
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="tests::parse_env_binding_validates_syntax_and_nul_bytes",
    ),
    RustGuard(
        guard_id="rustc_capture_lib_env_duplicate_rejection",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/lib.rs",
        description="Reject duplicate --env binding keys deterministically",
        anchor=(
            "            if declared.insert(key.clone(), value.clone()).is_some() {\n"
            "                return Err(Failure::tool(format!(\n"
            '                    "duplicate --env binding for {key}"'
        ),
        replacement=(
            "            let _ = declared.insert(key.clone(), value.clone());\n"
            "            if false {\n"
            "                return Err(Failure::tool(format!(\n"
            '                    "duplicate --env binding for {key}"'
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="tests::resolved_env_sorts_deterministically_and_rejects_duplicates",
    ),
    # ------------------------------------------------------------------
    # anneal-rustc-capture: mono.rs (3 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="rustc_capture_mono_reject_trailing_tokens",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/mono.rs",
        description="Reject trailing unparsed tokens in monomorphization generic argument syntax",
        anchor=(
            "    if !parser.rest().is_empty() {\n"
            "        return Err(format!(\n"
            '            "unexpected trailing tokens in generic argument {input:?}: {:?}",'
        ),
        replacement=(
            "    if false {\n"
            "        return Err(format!(\n"
            '            "unexpected trailing tokens in generic argument {input:?}: {:?}",'
        ),
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="mono::tests::rejects_malformed_or_excess_generic_args",
    ),
    RustGuard(
        guard_id="rustc_capture_mono_enforce_predicate_bounds",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/mono.rs",
        description="Refuse concrete monomorphizations whose trait/well-formedness bounds fail",
        anchor=(
            "    if !pred_errors.is_empty() {\n"
            "        return Err(format!(\n"
            '            "{label} trait or well-formedness predicates unsatisfied for `{}`: {:?}",'
        ),
        replacement=(
            "    let _ = &pred_errors;\n"
            "    if false {\n"
            "        return Err(format!(\n"
            '            "{label} trait or well-formedness predicates unsatisfied for `{}`: {:?}",'
        ),
        package="anneal-rustc-capture",
        test_args=("--test", "typed_capture"),
        test_name="explicit_concrete_monomorphization_refuses_unsatisfied_bounds_and_invalid_requests",
    ),
    RustGuard(
        guard_id="rustc_capture_mono_enforce_region_outlives",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/mono.rs",
        description="Refuse concrete monomorphizations whose region/outlives bounds fail",
        anchor=(
            "    if !region_errors.is_empty() {\n"
            "        return Err(format!(\n"
            '            "{label} region or outlives predicates unsatisfied for `{}`: {:?}",'
        ),
        replacement=(
            "    let _ = &region_errors;\n"
            "    if false {\n"
            "        return Err(format!(\n"
            '            "{label} region or outlives predicates unsatisfied for `{}`: {:?}",'
        ),
        package="anneal-rustc-capture",
        test_args=("--test", "typed_capture"),
        test_name="explicit_monomorphization_enforces_crate_roots_region_bounds_and_self_const_fn",
    ),
    # ------------------------------------------------------------------
    # anneal-rustc-capture: publication.rs (2 guards)
    # ------------------------------------------------------------------
    RustGuard(
        guard_id="rustc_capture_publication_staging_mode_private",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/publication.rs",
        description="Keep capture staging directory private (0o700) against other users",
        anchor="            staging.permissions(fs::Permissions::from_mode(0o700));",
        replacement="            staging.permissions(fs::Permissions::from_mode(0o755));",
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="publication::tests::staging_excludes_other_users",
    ),
    RustGuard(
        guard_id="rustc_capture_publication_preserve_foreign_data",
        suite="rustc_capture",
        target_file="trusted/rustc-capture/src/publication.rs",
        description="Remove only empty reservations on drop to preserve caller data",
        anchor="            let _ = fs::remove_dir(&self.destination);",
        replacement="            let _ = fs::remove_dir_all(&self.destination);",
        package="anneal-rustc-capture",
        test_args=("--lib",),
        test_name="publication::tests::failed_publication_preserves_data_added_to_the_reservation",
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
    if package == "anneal-rustc-capture":
        return anneal_root / "trusted/rustc-capture"
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
    if suite == "all":
        guards = list(RUST_GUARDS)
    elif suite == "workspace":
        guards = [g for g in RUST_GUARDS if g.suite in WORKSPACE_SUITES]
    else:
        guards = [g for g in RUST_GUARDS if g.suite == suite]
    if name_filter:
        guards = [g for g in guards if name_filter in g.guard_id]
    return guards


def _resolve_rustc_capture_env(
    nightly_toolchain: str,
    *,
    use_explicit_cargo: bool,
    rustc_capture_sysroot: Path | None = None,
) -> tuple[Path | None, dict[str, str]]:
    """Resolve nightly sysroot, linker flags, and optional cargo executable."""
    nightly_cargo: Path | None = None
    if rustc_capture_sysroot is not None:
        sysroot = rustc_capture_sysroot
    else:
        rustup_bin = shutil.which("rustup")
        if not rustup_bin:
            raise RuntimeError(
                "rustup not found on PATH; cannot run rustc_capture guards"
            )
        proc = subprocess.run(
            [rustup_bin, "run", nightly_toolchain, "rustc", "--print", "sysroot"],
            capture_output=True,
            text=True,
        )
        if proc.returncode != 0:
            detail = (proc.stderr or proc.stdout).strip()
            raise RuntimeError(
                f"failed resolving nightly toolchain {nightly_toolchain!r}: {detail}"
            )
        sysroot = Path(proc.stdout.strip())
        if not use_explicit_cargo:
            which_cargo = subprocess.run(
                [rustup_bin, "which", "--toolchain", nightly_toolchain, "cargo"],
                capture_output=True,
                text=True,
            )
            if which_cargo.returncode != 0:
                detail = (which_cargo.stderr or which_cargo.stdout).strip()
                raise RuntimeError(
                    f"failed resolving cargo for {nightly_toolchain!r}: {detail}"
                )
            nightly_cargo = Path(which_cargo.stdout.strip())
            if not nightly_cargo.is_file():
                raise RuntimeError(
                    f"resolved nightly cargo does not exist: {nightly_cargo}"
                )

    lib_dir = sysroot / "lib"
    if not lib_dir.is_dir():
        raise RuntimeError(
            f"nightly rustc sysroot lacks lib directory: {lib_dir}"
        )

    existing_ld = os.environ.get("LD_LIBRARY_PATH", "")
    ld_path = f"{lib_dir}:{existing_ld}" if existing_ld else str(lib_dir)
    existing_rustflags = os.environ.get("RUSTFLAGS", "").strip()
    link_flags = f"-L {lib_dir} -C link-arg=-Wl,-rpath,{lib_dir}"
    rustflags = (
        f"{existing_rustflags} {link_flags}".strip()
        if existing_rustflags
        else link_flags
    )
    env_overrides: dict[str, str] = {
        "RUSTUP_TOOLCHAIN": nightly_toolchain,
        "RUSTFLAGS": rustflags,
        "LD_LIBRARY_PATH": ld_path,
    }
    rustc_bin = sysroot / "bin/rustc"
    if rustc_bin.is_file():
        env_overrides["RUSTC"] = str(rustc_bin)
    return nightly_cargo, env_overrides


def _build_cargo_test_args(
    test_package: str, guard: RustGuard, *tail: str
) -> list[str]:
    return ["test", "--locked", "-p", test_package, *guard.test_args, *tail]


def _target_dir_for_guard(base_target: Path, guard: RustGuard) -> Path:
    subdir = "rustc-capture" if guard.suite == "rustc_capture" else "workspace"
    return base_target / subdir


def _effective_cargo_and_env(
    guard: RustGuard,
    *,
    cargo_bin: Path,
    rustc_capture_cargo: Path | None,
    rustc_capture_env: dict[str, str] | None,
) -> tuple[Path, dict[str, str] | None]:
    if guard.suite == "rustc_capture":
        return (rustc_capture_cargo or cargo_bin, rustc_capture_env)
    return (cargo_bin, None)


def _run_cargo(
    cargo_bin: Path,
    args: list[str],
    *,
    cwd: Path,
    target_dir: Path,
    timeout_sec: int,
    extra_env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["CARGO_TARGET_DIR"] = str(target_dir)
    # Disable color noise for deterministic parsing.
    env["CARGO_TERM_COLOR"] = "never"
    if extra_env:
        if "RUSTC" not in extra_env:
            env.pop("RUSTC", None)
        env.update(extra_env)
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
    rustc_capture_cargo: Path | None,
    rustc_capture_env: dict[str, str] | None,
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

        effective_cargo, extra_env = _effective_cargo_and_env(
            guard,
            cargo_bin=cargo_bin,
            rustc_capture_cargo=rustc_capture_cargo,
            rustc_capture_env=rustc_capture_env,
        )
        guard_target = _target_dir_for_guard(worker_target, guard)
        pre_stat = src_path.stat()
        try:
            src_path.write_text(mutated_text, encoding="utf-8")
            _bump_mtime_if_needed(src_path, pre_stat.st_mtime_ns)

            # Gate 1 (Anti-fake-kill): compile target first with `--no-run`.
            # Any compile error must report `ERROR`, never `KILLED`.
            test_package, _ = _test_package_and_dir_for_guard(worker_anneal, guard)
            compile_args = _build_cargo_test_args(test_package, guard, "--no-run")
            try:
                comp = _run_cargo(
                    effective_cargo,
                    compile_args,
                    cwd=worker_anneal,
                    target_dir=guard_target,
                    timeout_sec=timeout_sec,
                    extra_env=extra_env,
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
            test_args = _build_cargo_test_args(
                test_package, guard, "--", "--exact", guard.test_name
            )
            try:
                test_res = _run_cargo(
                    effective_cargo,
                    test_args,
                    cwd=worker_anneal,
                    target_dir=guard_target,
                    timeout_sec=timeout_sec,
                    extra_env=extra_env,
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
    nightly_toolchain: str = DEFAULT_NIGHTLY_TOOLCHAIN,
    use_explicit_cargo: bool = False,
    rustc_capture_sysroot: Path | None = None,
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

    rustc_capture_cargo: Path | None = None
    rustc_capture_env: dict[str, str] | None = None
    if any(g.suite == "rustc_capture" for g in guards):
        rustc_capture_cargo, rustc_capture_env = _resolve_rustc_capture_env(
            nightly_toolchain,
            use_explicit_cargo=use_explicit_cargo,
            rustc_capture_sysroot=rustc_capture_sysroot,
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
        # 1. Baseline compile per distinct `(suite, test_package, test_args)`
        # target.
        seen_builds: set[tuple[str, str, tuple[str, ...]]] = set()
        for g in guards:
            test_pkg, _ = _test_package_and_dir_for_guard(base_anneal, g)
            key = (g.suite, test_pkg, g.test_args)
            if key in seen_builds:
                continue
            seen_builds.add(key)
            eff_cargo, extra_env = _effective_cargo_and_env(
                g,
                cargo_bin=cargo_bin,
                rustc_capture_cargo=rustc_capture_cargo,
                rustc_capture_env=rustc_capture_env,
            )
            guard_target = _target_dir_for_guard(base_target, g)
            guard_target.mkdir(parents=True, exist_ok=True)
            comp = _run_cargo(
                eff_cargo,
                _build_cargo_test_args(test_pkg, g, "--no-run"),
                cwd=base_anneal,
                target_dir=guard_target,
                timeout_sec=timeout_sec,
                extra_env=extra_env,
            )
            if comp.returncode != 0:
                raise RuntimeError(
                    f"baseline build failed for {test_pkg} {' '.join(g.test_args)}:\n"
                    f"{comp.stdout}\n{comp.stderr}"
                )

        # 2. Verify each distinct baseline targeted test passes (>= 1 test).
        seen_tests: set[tuple[str, str, tuple[str, ...], str]] = set()
        for g in guards:
            test_pkg, _ = _test_package_and_dir_for_guard(base_anneal, g)
            tkey = (g.suite, test_pkg, g.test_args, g.test_name)
            if tkey in seen_tests:
                continue
            seen_tests.add(tkey)
            eff_cargo, extra_env = _effective_cargo_and_env(
                g,
                cargo_bin=cargo_bin,
                rustc_capture_cargo=rustc_capture_cargo,
                rustc_capture_env=rustc_capture_env,
            )
            guard_target = _target_dir_for_guard(base_target, g)
            base_res = _run_cargo(
                eff_cargo,
                _build_cargo_test_args(test_pkg, g, "--", "--exact", g.test_name),
                cwd=base_anneal,
                target_dir=guard_target,
                timeout_sec=timeout_sec,
                extra_env=extra_env,
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
        integ_targets = {
            (
                g.suite,
                g.package,
                _test_package_and_dir_for_guard(base_anneal, g)[0],
                g.test_args[1],
            )
            for g in guards
            if len(g.test_args) == 2 and g.test_args[0] == "--test"
        }
        for idx in range(1, worker_count):
            w_root = root_path / f"worker-{idx}"
            w_anneal = w_root / "anneal"
            w_target = w_root / "target"
            w_root.mkdir()
            shutil.copytree(base_anneal, w_anneal, symlinks=True)
            shutil.copytree(base_target, w_target, symlinks=True)
            # Clear local package fingerprints/build dirs and integration test
            # executables so `env!("CARGO_BIN_EXE_*")` in `--test` binaries
            # rebinds to this worker's own `w_target` rather than `worker-0`.
            for suite_name, src_pkg, test_pkg, test_stem_raw in integ_targets:
                subdir = "rustc-capture" if suite_name == "rustc_capture" else "workspace"
                sub_debug = w_target / subdir / "debug"
                for pkg_name in (src_pkg, test_pkg):
                    for parent_name in (".fingerprint", "build"):
                        parent_dir = sub_debug / parent_name
                        if not parent_dir.is_dir():
                            continue
                        for pattern in (pkg_name, f"{pkg_name}-*"):
                            for entry in parent_dir.glob(pattern):
                                if entry.is_dir():
                                    shutil.rmtree(entry, ignore_errors=True)
                                else:
                                    entry.unlink(missing_ok=True)
                deps_root = sub_debug / "deps"
                test_stem = test_stem_raw.replace("-", "_")
                if deps_root.is_dir():
                    for entry in deps_root.glob(f"{test_stem}-*"):
                        if entry.is_dir():
                            shutil.rmtree(entry, ignore_errors=True)
                        else:
                            entry.unlink(missing_ok=True)
            worker_pool.put((w_anneal, w_target))

        # 4. Run single-guard mutations concurrently across worker workspaces.
        by_id: dict[str, GuardResult] = {}
        with ThreadPoolExecutor(max_workers=worker_count) as pool:
            futs = {
                pool.submit(
                    _check_one_guard,
                    g,
                    cargo_bin=cargo_bin,
                    rustc_capture_cargo=rustc_capture_cargo,
                    rustc_capture_env=rustc_capture_env,
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
            f"[{entry['status']:8s}] ({entry['suite']:13s}) "
            f"{entry['guard_id']:48s} {entry['duration_sec']:5.2f}s  "
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
            "Run single-guard mutation checks against trusted/audit/src/, "
            "trusted/cargo-anneal/src/, and trusted/rustc-capture/src/."
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
        "--nightly-toolchain",
        default=DEFAULT_NIGHTLY_TOOLCHAIN,
        help=(
            "Nightly toolchain for `rustc_capture` guards "
            f"(default: {DEFAULT_NIGHTLY_TOOLCHAIN})."
        ),
    )
    parser.add_argument(
        "--suite",
        choices=SUITE_CHOICES,
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
            print(f"{g.suite:14s} {g.guard_id:48s} {g.target_file}")
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
            nightly_toolchain=args.nightly_toolchain,
            use_explicit_cargo=args.cargo is not None,
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
