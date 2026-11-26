#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""CI driver for Stage-1 MIR multi-leg differential oracle checks.

Runs `anneal-diff run --json` against the Stage-1 Profile v1 corpus, executes
an optional explicit `--mir-eval-manifest` Leg-3 evaluator when provided, and
emits `anneal-semantic-detail/v1` plus numeric `anneal-perf-record/v1` metric
snippets.

Stage 0 Alpha — Not Yet Audited: empirical differential testing raises
confidence and uncovers divergences rather than proving universal soundness.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import glob
import json
import math
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tomllib
from typing import Any


DETAIL_SCHEMA = "anneal-semantic-detail/v1"
ALPHA_NOTICE = "Stage 0 Alpha — Not Yet Audited (this is alpha software!)"
REQUIRED_METRICS_KEYS = frozenset(
    {
        "compared_count",
        "pass_agreed_count",
        "ub_agreed_count",
        "conservative_unsupported_count",
        "kernel_checked_pass_count",
        "kernel_checked_ub_count",
        "unsound_missed_fault_count",
        "value_mismatch_count",
        "unexpected_conservative_count",
        "leg_divergence_count",
    }
)


_CARGO_CHILD_PATH_ENV_VARS = (
    "CARGO_HOME",
    "CARGO_TARGET_DIR",
    "XDG_CACHE_HOME",
)

_CARGO_CHILD_CMD_ENV_VARS = (
    "CARGO",
    "RUSTC",
    "RUSTDOC",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
)

_DIFF_CHILD_PATH_ENV_VARS = (
    "ANNEAL_CAPTURE",
    "ANNEAL_MVP_CAPTURE",
    "ANNEAL_CLI",
    "ANNEAL_MVP_CLI",
    "ANNEAL_AUDITOR",
    "ANNEAL_LEAN",
    "ANNEAL_MVP_LEAN",
    "ANNEAL_SYSROOT",
    "ANNEAL_TEST_RUST_SYSROOT",
    "ANNEAL_MVP_SYSROOT",
    "ANNEAL_TEST_INSTALL_ROOT",
    "ANNEAL_MIRI_SYSROOT",
    "ANNEAL_DIFF_CACHE_DIR",
    *_CARGO_CHILD_PATH_ENV_VARS,
)

_SEARCH_PATH_ENV_VARS = (
    "PATH",
    "LD_LIBRARY_PATH",
)


def _anchor_search_path_list(raw: str, base_dir: Path) -> str:
    """Anchor relative entries inside `os.pathsep`-delimited search lists."""
    return os.pathsep.join(
        _anchor_env_path(entry or ".", base_dir)
        for entry in raw.split(os.pathsep)
    )


def _anchor_cargo_child_env(
    raw_env: dict[str, str],
    caller_cwd: Path,
    *,
    include_diff_vars: bool = False,
) -> dict[str, str]:
    """Strip credentials and anchor relative path/tool env vars."""
    child_env = _strip_child_credentials(raw_env)
    path_vars = (
        _DIFF_CHILD_PATH_ENV_VARS
        if include_diff_vars
        else _CARGO_CHILD_PATH_ENV_VARS
    )
    for env_key in path_vars:
        raw_val = child_env.get(env_key)
        if raw_val:
            child_env[env_key] = _anchor_env_path(raw_val, caller_cwd)
    for list_key in _SEARCH_PATH_ENV_VARS:
        raw_list = child_env.get(list_key)
        if raw_list:
            child_env[list_key] = _anchor_search_path_list(
                raw_list, caller_cwd
            )
    for cmd_key in _CARGO_CHILD_CMD_ENV_VARS:
        raw_cmd = child_env.get(cmd_key)
        if raw_cmd:
            child_env[cmd_key] = _resolve_command_token(raw_cmd, caller_cwd)
    return child_env

_STRIPPED_CHILD_ENV_VARS = (
    "ACTIONS_CACHE_URL",
    "ACTIONS_ID_TOKEN_REQUEST_TOKEN",
    "ACTIONS_ID_TOKEN_REQUEST_URL",
    "ACTIONS_RESULTS_URL",
    "ACTIONS_RUNTIME_TOKEN",
    "ACTIONS_RUNTIME_URL",
    "GH_TOKEN",
    "GITHUB_TOKEN",
)


def _strip_child_credentials(env: dict[str, str]) -> dict[str, str]:
    """Remove GitHub Actions and API credential variables from child env."""
    for env_key in _STRIPPED_CHILD_ENV_VARS:
        env.pop(env_key, None)
    return env


def ensure_not_symlink(path: Path, label: str = "path") -> None:
    """Reject symlink inputs/outputs fail-closed."""
    if path.is_symlink():
        raise ValueError(f"{label} must not be a symlink: {path}")


def _resolve_cli_path(
    path: Path, label: str = "path", *, base_dir: Path | None = None
) -> Path:
    """Anchor `path` to `base_dir` (or `Path.cwd()`) and reject symlinks."""
    anchor = Path.cwd() if base_dir is None else base_dir
    anchored = path if path.is_absolute() else (anchor / path)
    ensure_not_symlink(anchored, label)
    lexical_abs = Path(os.path.abspath(anchored))
    ensure_not_symlink(lexical_abs, label)
    if anchored.name in ("", ".", ".."):
        resolved = anchored.resolve(strict=False)
    else:
        resolved = anchored.parent.resolve(strict=False) / anchored.name
    ensure_not_symlink(resolved, label)
    return resolved


def _resolve_optional_cli_path(
    path: Path | None, label: str, *, base_dir: Path | None = None
) -> Path | None:
    if path is None:
        return None
    return _resolve_cli_path(path, label, base_dir=base_dir)


def _anchor_env_path(raw: str, base_dir: Path) -> str:
    """Anchor a relative environment path without following leaf symlinks."""
    p = Path(raw)
    if p.is_absolute():
        return raw
    anchored = base_dir / p
    if anchored.name in ("", ".", ".."):
        return os.path.abspath(anchored)
    return str(anchored.parent.resolve(strict=False) / anchored.name)


def _resolve_command_token(raw_cmd: str, base_dir: Path) -> str:
    """Anchor relative command paths containing separators; keep bare names."""
    if os.sep in raw_cmd or (os.altsep and os.altsep in raw_cmd):
        return _anchor_env_path(raw_cmd, base_dir)
    return raw_cmd


def _git_metadata(
    repo_root: Path,
    *,
    allow_unknown_git: bool = False,
    commit_sha_override: str | None = None,
    commit_unix_ts_override: int | None = None,
    branch_override: str | None = None,
) -> tuple[str, str, int]:
    """Return `(branch, commit_sha, commit_unix_ts)`, failing closed."""
    if (commit_sha_override is None) != (commit_unix_ts_override is None):
        raise ValueError(
            "commit_sha_override and commit_unix_ts_override must be provided together"
        )
    if (
        commit_sha_override is not None
        and commit_unix_ts_override is not None
        and branch_override
    ):
        return branch_override, commit_sha_override.lower(), commit_unix_ts_override

    child_env = _strip_child_credentials(os.environ.copy())
    sha_ok = False
    br_ok = False
    ts_ok = False
    sha = ""
    branch = ""
    ts_val = 0
    try:
        sha_out = subprocess.run(
            ["git", "-C", str(repo_root), "rev-parse", "HEAD"],
            env=child_env,
            capture_output=True,
            text=True,
            check=False,
        )
        br_out = subprocess.run(
            ["git", "-C", str(repo_root), "rev-parse", "--abbrev-ref", "HEAD"],
            env=child_env,
            capture_output=True,
            text=True,
            check=False,
        )
        ts_out = subprocess.run(
            ["git", "-C", str(repo_root), "show", "-s", "--format=%ct", "HEAD"],
            env=child_env,
            capture_output=True,
            text=True,
            check=False,
        )
        raw_sha = sha_out.stdout.strip()
        sha_ok = (
            sha_out.returncode == 0
            and len(raw_sha) == 40
            and all(c in "0123456789abcdefABCDEF" for c in raw_sha)
        )
        if sha_ok:
            sha = raw_sha.lower()
        raw_br = br_out.stdout.strip()
        br_ok = br_out.returncode == 0 and bool(raw_br)
        if br_ok:
            branch = raw_br
        raw_ts = ts_out.stdout.strip()
        ts_ok = ts_out.returncode == 0 and raw_ts.isdigit()
        if ts_ok:
            ts_val = int(raw_ts)
    except OSError as exc:
        if (
            not allow_unknown_git
            and (
                commit_sha_override is None
                or commit_unix_ts_override is None
                or not branch_override
            )
        ):
            raise RuntimeError(
                f"git metadata query failed in {repo_root}: {exc}"
            ) from exc

    final_sha = (
        commit_sha_override.lower()
        if commit_sha_override is not None
        else (sha if sha_ok else ("0" * 40 if allow_unknown_git else ""))
    )
    final_branch = (
        branch_override
        if branch_override
        else (branch if br_ok else ("unknown" if allow_unknown_git else ""))
    )
    if commit_unix_ts_override is not None:
        final_ts: int | None = commit_unix_ts_override
    elif ts_ok:
        final_ts = ts_val
    elif allow_unknown_git:
        final_ts = 0
    else:
        final_ts = None

    if final_sha and final_branch and final_ts is not None:
        return final_branch, final_sha, final_ts
    raise RuntimeError(
        f"missing valid git HEAD metadata in {repo_root} (pass --allow-unknown-git or explicit revision flags)"
    )


def _tool_version(
    cmd: list[str],
    *,
    anchor: Path | None = None,
    extra_lib_dir: Path | None = None,
) -> str:
    probe_env = _anchor_cargo_child_env(
        os.environ.copy(),
        Path.cwd() if anchor is None else anchor,
        include_diff_vars=True,
    )
    if extra_lib_dir is not None and extra_lib_dir.is_dir():
        prev_ld = probe_env.get("LD_LIBRARY_PATH", "")
        probe_env["LD_LIBRARY_PATH"] = (
            f"{extra_lib_dir}{os.pathsep}{prev_ld}"
            if prev_ld
            else str(extra_lib_dir)
        )
    try:
        res = subprocess.run(
            cmd,
            env=probe_env,
            capture_output=True,
            text=True,
            check=False,
        )
        if res.returncode == 0 and res.stdout.strip():
            return res.stdout.strip().splitlines()[0]
    except OSError:
        pass
    return "unknown"


def _find_cached_lean(toolchain_parent: Path) -> Path | None:
    try:
        entries = sorted(toolchain_parent.iterdir())
    except OSError:
        return None
    for entry in entries:
        cand = entry / "lean" / "bin" / "lean"
        if cand.is_file():
            return cand
    return None


def _resolve_suite_lean_cmd(anneal_root: Path, anchor: Path) -> list[str]:
    for key in ("ANNEAL_LEAN", "ANNEAL_MVP_LEAN"):
        raw_lean = os.environ.get(key)
        if raw_lean:
            cand = _anchor_env_path(raw_lean, anchor)
            if (
                os.sep in raw_lean
                or (os.altsep and os.altsep in raw_lean)
                or Path(cand).exists()
            ):
                return [cand]
            return [raw_lean]
    raw_inst = os.environ.get("ANNEAL_TEST_INSTALL_ROOT")
    if raw_inst:
        cand = Path(_anchor_env_path(raw_inst, anchor)) / "lean" / "bin" / "lean"
        if cand.is_file():
            return [str(cand)]
    raw_xdg = os.environ.get("XDG_CACHE_HOME")
    if raw_xdg:
        found = _find_cached_lean(
            Path(_anchor_env_path(raw_xdg, anchor)) / "anneal" / "toolchain"
        )
        if found is not None:
            return [str(found)]
    raw_home = os.environ.get("HOME")
    if raw_home:
        home_path = Path(_anchor_env_path(raw_home, anchor))
        for rel in (
            ".cache/anneal/toolchain",
            "Library/Caches/anneal/toolchain",
            "anneal/toolchain",
        ):
            found = _find_cached_lean(home_path / rel)
            if found is not None:
                return [str(found)]
        tc_file = anneal_root / "trusted" / "lean" / "lean-toolchain"
        if tc_file.is_file() and not tc_file.is_symlink():
            tc_spec = tc_file.read_text(encoding="utf-8").strip()
            if tc_spec:
                tc_dir = tc_spec.replace("/", "--").replace(":", "---")
                elan_base = (
                    Path(_anchor_env_path(os.environ["ELAN_HOME"], anchor))
                    if os.environ.get("ELAN_HOME")
                    else (home_path / ".elan")
                )
                elan_lean = elan_base / "toolchains" / tc_dir / "bin" / "lean"
                if elan_lean.is_file():
                    return [str(elan_lean)]
    return ["lean"]


def _resolve_suite_rustc_cmd(
    anchor: Path,
) -> tuple[list[str], Path | None]:
    sysroot_candidates: list[Path] = []
    for key in (
        "ANNEAL_SYSROOT",
        "ANNEAL_TEST_RUST_SYSROOT",
        "ANNEAL_MVP_SYSROOT",
    ):
        raw = os.environ.get(key)
        if raw:
            sysroot_candidates.append(Path(_anchor_env_path(raw, anchor)))
    raw_inst = os.environ.get("ANNEAL_TEST_INSTALL_ROOT")
    if raw_inst:
        sysroot_candidates.append(
            Path(_anchor_env_path(raw_inst, anchor)) / "rust"
        )
    for sys_dir in sysroot_candidates:
        rustc_bin = sys_dir / "bin" / "rustc"
        if rustc_bin.is_file():
            return [str(rustc_bin)], sys_dir / "lib"

    raw_rustc = os.environ.get("RUSTC")
    if raw_rustc:
        return [_resolve_command_token(raw_rustc, anchor)], None

    anchored_path = _anchor_search_path_list(
        os.environ.get("PATH", ""), anchor
    )
    if shutil.which("rustup", path=anchored_path or None) is not None:
        return ["rustup", "run", "nightly-2026-05-31", "rustc"], None
    return ["rustc"], None


def _collect_environment(
    anneal_root: Path, *, caller_cwd: Path | None = None
) -> dict[str, Any]:
    anchor = Path.cwd() if caller_cwd is None else caller_cwd
    rustc_cmd, rustc_lib = _resolve_suite_rustc_cmd(anchor)
    lean_cmd = _resolve_suite_lean_cmd(anneal_root, anchor)
    return {
        "os": platform.system().lower(),
        "arch": platform.machine(),
        "rustc_version": _tool_version(
            [*rustc_cmd, "--version"], anchor=anchor, extra_lib_dir=rustc_lib
        ),
        "lean_version": _tool_version(
            [*lean_cmd, "--version"], anchor=anchor
        ),
        "anneal_root": anneal_root.name,
    }


def _default_anneal_root() -> Path:
    return Path(__file__).resolve().parent.parent


def _allowed_artifact_manifests(manifest_canon: Path) -> set[Path]:
    """Resolve canonical manifests permitted to emit a built binary target.

    Plain `[package]` manifests (and non-virtual workspace manifests without
    `workspace.default-members`) only match `manifest_canon` itself; virtual
    workspaces and package workspaces with explicit `workspace.default-members`
    match resolved selected member `Cargo.toml` files excluding
    `workspace.exclude`.
    """
    try:
        parsed = tomllib.loads(manifest_canon.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError):
        return {manifest_canon}
    if not isinstance(parsed, dict):
        return {manifest_canon}
    workspace = parsed.get("workspace")
    if not isinstance(workspace, dict):
        return {manifest_canon}
    if "default-members" in workspace:
        raw_select = workspace.get("default-members")
        if not isinstance(raw_select, list):
            return set()
    elif "package" in parsed:
        return {manifest_canon}
    else:
        raw_select = workspace.get("members", [])
        if not isinstance(raw_select, list):
            return set()

    allowed: set[Path] = set()
    ws_dir = manifest_canon.parent
    escaped_ws = glob.escape(str(ws_dir))
    excluded_dirs: set[Path] = set()
    raw_exclude = workspace.get("exclude", [])
    if isinstance(raw_exclude, list):
        for pat in raw_exclude:
            if not isinstance(pat, str) or not pat:
                continue
            for match in glob.glob(
                os.path.join(escaped_ws, pat), recursive=True
            ):
                try:
                    excluded_dirs.add(Path(match).resolve(strict=True))
                except OSError:
                    continue

    for pat in raw_select:
        if not isinstance(pat, str) or not pat:
            continue
        for match in glob.glob(
            os.path.join(escaped_ws, pat), recursive=True
        ):
            cand_dir = Path(match)
            if cand_dir.is_symlink():
                continue
            try:
                resolved_dir = cand_dir.resolve(strict=True)
                if not resolved_dir.is_dir():
                    continue
                if resolved_dir != ws_dir and ws_dir not in resolved_dir.parents:
                    continue
                if any(
                    resolved_dir == ex or ex in resolved_dir.parents
                    for ex in excluded_dirs
                ):
                    continue
                cand_manifest = resolved_dir / "Cargo.toml"
                if cand_manifest.is_symlink() or not cand_manifest.is_file():
                    continue
                allowed.add(cand_manifest.resolve(strict=True))
            except OSError:
                continue
    return allowed


def _extract_built_executable(
    stdout: str, bin_name: str, manifest_canon: Path
) -> Path | None:
    """Extract the binary path from `cargo build --message-format=json`."""
    allowed_manifests = _allowed_artifact_manifests(manifest_canon)
    found: Path | None = None
    for raw_line in stdout.splitlines():
        line = raw_line.strip()
        if not line.startswith("{"):
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(msg, dict) or msg.get("reason") != "compiler-artifact":
            continue
        msg_manifest = msg.get("manifest_path")
        if not isinstance(msg_manifest, str) or not msg_manifest:
            continue
        try:
            if Path(msg_manifest).resolve(strict=True) not in allowed_manifests:
                continue
        except OSError:
            continue
        target = msg.get("target")
        if not isinstance(target, dict) or target.get("name") != bin_name:
            continue
        kinds = target.get("kind")
        if isinstance(kinds, list) and "bin" not in kinds:
            continue
        profile = msg.get("profile")
        if isinstance(profile, dict) and profile.get("test") is True:
            continue
        exe = msg.get("executable")
        if isinstance(exe, str) and exe:
            cand = Path(exe)
            if found is not None and cand != found:
                return None
            found = cand
    return found


def maybe_run_mir_eval_manifest(
    manifest: Path | None,
    *,
    skip_tests: bool = False,
) -> tuple[dict[str, Any], Path | None]:
    """Run and build an explicit `anneal-mir-eval` Cargo manifest when given."""
    if manifest is None:
        return (
            {
                "executed": False,
                "passed": None,
                "reason": "no --mir-eval-manifest supplied",
            },
            None,
        )

    caller_cwd = Path.cwd()
    manifest_abs = _resolve_cli_path(
        manifest, "mir_eval_manifest", base_dir=caller_cwd
    )
    if not manifest_abs.is_file():
        return (
            {
                "executed": False,
                "passed": False,
                "manifest_path": str(manifest_abs),
                "error": f"missing mir-eval manifest: {manifest_abs}",
            },
            None,
        )
    manifest_canon = manifest_abs.resolve(strict=True)

    cargo = _resolve_command_token(os.environ.get("CARGO", "cargo"), caller_cwd)
    env = _anchor_cargo_child_env(os.environ.copy(), caller_cwd)
    work_dir = manifest_canon.parent
    if not skip_tests:
        test_res = subprocess.run(
            [cargo, "test", "--manifest-path", str(manifest_canon), "--locked"],
            cwd=work_dir,
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )
        if test_res.returncode != 0:
            return (
                {
                    "executed": True,
                    "passed": False,
                    "manifest_path": str(manifest_abs),
                    "error": (test_res.stderr or test_res.stdout)[-1200:],
                },
                None,
            )

    build_res = subprocess.run(
        [
            cargo,
            "build",
            "--manifest-path",
            str(manifest_canon),
            "--locked",
            "--bin",
            "anneal-mir-eval",
            "--message-format=json",
        ],
        cwd=work_dir,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    if build_res.returncode != 0:
        return (
            {
                "executed": True,
                "passed": False,
                "manifest_path": str(manifest_abs),
                "error": (build_res.stderr or build_res.stdout)[-1200:],
            },
            None,
        )

    extracted_bin = _extract_built_executable(
        build_res.stdout, "anneal-mir-eval", manifest_canon
    )
    if extracted_bin is None:
        return (
            {
                "executed": True,
                "passed": False,
                "manifest_path": str(manifest_abs),
                "error": (
                    "cargo build JSON output lacked compiler-artifact "
                    "executable for anneal-mir-eval"
                ),
            },
            None,
        )
    bin_path = (
        extracted_bin
        if extracted_bin.is_absolute()
        else work_dir / extracted_bin
    )
    if not bin_path.is_file():
        return (
            {
                "executed": True,
                "passed": False,
                "manifest_path": str(manifest_abs),
                "error": f"expected built binary at {bin_path}",
            },
            None,
        )
    ensure_not_symlink(bin_path, "anneal-mir-eval binary")
    return (
        {
            "executed": not skip_tests,
            "passed": True if not skip_tests else None,
            "manifest_path": str(manifest_abs),
        },
        bin_path,
    )


def build_perf_metrics_snippet(diff_report: dict[str, Any]) -> dict[str, float | int]:
    """Project `anneal-differential-run/v1` into `perf-record` metrics."""
    metrics = diff_report["metrics"]
    missing = REQUIRED_METRICS_KEYS - set(metrics.keys())
    if missing:
        raise ValueError(f"missing metrics keys in differential report: {sorted(missing)}")

    out: dict[str, float | int] = {
        "differential_oracle.litmus.compared_count": int(metrics["compared_count"]),
        "differential_oracle.litmus.pass_agreed_count": int(
            metrics["pass_agreed_count"]
        ),
        "differential_oracle.litmus.ub_agreed_count": int(metrics["ub_agreed_count"]),
        "differential_oracle.litmus.conservative_unsupported_count": int(
            metrics["conservative_unsupported_count"]
        ),
        "differential_oracle.litmus.kernel_checked_pass_count": int(
            metrics["kernel_checked_pass_count"]
        ),
        "differential_oracle.litmus.kernel_checked_ub_count": int(
            metrics["kernel_checked_ub_count"]
        ),
        "differential_oracle.litmus.unsound_missed_fault_count": int(
            metrics["unsound_missed_fault_count"]
        ),
        "differential_oracle.litmus.value_mismatch_count": int(
            metrics["value_mismatch_count"]
        ),
        "differential_oracle.litmus.unexpected_conservative_count": int(
            metrics["unexpected_conservative_count"]
        ),
        "differential_oracle.litmus.leg_divergence_count": int(
            metrics["leg_divergence_count"]
        ),
        "differential_oracle.red_flags.passed_count": int(
            diff_report.get("red_flags_passed", 0)
        ),
    }
    mutants = diff_report.get("mutant_check")
    if isinstance(mutants, dict) and "killed_pct" in mutants:
        out["differential_oracle.mutants.killed_pct"] = float(mutants["killed_pct"])
    return out


def _load_perf_tracking():
    raw_script = Path(__file__)
    ensure_not_symlink(raw_script, "script")
    raw_ci_dir = raw_script.parent
    ensure_not_symlink(raw_ci_dir, "ci directory")
    ci_dir = raw_ci_dir.resolve(strict=True)
    perf_path = ci_dir / "perf_tracking.py"
    ensure_not_symlink(perf_path, "perf_tracking.py")
    if str(ci_dir) not in sys.path:
        sys.path.insert(0, str(ci_dir))
    import perf_tracking

    return perf_tracking


def build_perf_record_from_snippet(
    perf_snippet: dict[str, float | int],
    *,
    branch: str,
    commit_sha: str,
    commit_unix_ts: int,
    environment_profile: dict[str, Any],
) -> dict[str, Any]:
    """Assemble and validate a full `anneal-perf-record/v1` record."""
    if not isinstance(perf_snippet, dict) or not perf_snippet:
        raise ValueError("perf_snippet must be a non-empty dict")
    pt = _load_perf_tracking()
    for metric_id, value in perf_snippet.items():
        if not pt.METRIC_ID_RE.match(metric_id):
            raise ValueError(f"invalid metric ID in snippet: {metric_id!r}")
        desc = pt.describe_metric(metric_id)
        if desc["category"] != "differential_oracle":
            raise ValueError(
                f"unexpected category {desc['category']!r} for {metric_id!r}"
            )
        if (
            isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(value)
            or value < 0
        ):
            raise ValueError(f"invalid numeric metric value {metric_id}={value!r}")

    if not pt.SHA40_RE.match(commit_sha) or not branch:
        raise ValueError(
            f"cannot build anneal-perf-record/v1 without valid 40-hex commit_sha and non-empty branch: sha={commit_sha!r}, branch={branch!r}"
        )
    ts_iso = datetime.fromtimestamp(max(0, commit_unix_ts), tz=timezone.utc).strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )
    os_name = str(environment_profile.get("os") or platform.system().lower() or "linux")
    arch = str(environment_profile.get("arch") or platform.machine() or "x86_64")
    record = {
        "schema": pt.RECORD_SCHEMA,
        "commit": {
            "sha": commit_sha,
            "short_sha": commit_sha[:12],
            "timestamp": ts_iso,
            "unix_ts": max(0, int(commit_unix_ts)),
            "subject": "Stage-1 differential oracle telemetry",
            "branch": branch,
        },
        "environment": {
            "profile": f"{os_name}-{arch}",
            "os": os_name,
            "arch": arch,
            "cpu_model": "ci-runner",
            "vcpu_count": max(1, os.cpu_count() or 1),
            "ram_total_kib": 0,
            "lean_version": str(
                environment_profile.get("lean_version") or "unknown"
            ),
            "rustc_version": str(
                environment_profile.get("rustc_version") or "unknown"
            ),
        },
        "sampling": {
            "verify_repeats": 1,
            "aggregation": "single",
        },
        "metrics": perf_snippet,
    }
    return pt.validate_record(record)


def validate_perf_metrics_snippet(
    perf_snippet: dict[str, float | int],
    *,
    branch: str,
    commit_sha: str,
    commit_unix_ts: int,
    environment_profile: dict[str, Any],
) -> None:
    """Validate snippet metric IDs, categories, and `perf-record` schema."""
    build_perf_record_from_snippet(
        perf_snippet,
        branch=branch,
        commit_sha=commit_sha,
        commit_unix_ts=commit_unix_ts,
        environment_profile=environment_profile,
    )


def build_semantic_detail_report(
    *,
    diff_report: dict[str, Any],
    mir_eval_status: dict[str, Any],
    repo: str,
    branch: str,
    commit_sha: str,
    commit_unix_ts: int,
    environment_profile: dict[str, Any],
) -> dict[str, Any]:
    """Assemble the canonical `anneal-semantic-detail/v1` JSON document."""
    failing_cases = [
        {
            "id": c["id"],
            "category": c["category"],
            "expected": c["expected"],
            "verdict": c["verdict"],
        }
        for c in diff_report.get("cases", [])
        if not _verdict_is_ok(c.get("verdict"))
    ]
    perf_snippet = build_perf_metrics_snippet(diff_report)
    validate_perf_metrics_snippet(
        perf_snippet,
        branch=branch,
        commit_sha=commit_sha,
        commit_unix_ts=commit_unix_ts,
        environment_profile=environment_profile,
    )
    capture_source = str(diff_report.get("capture_bin_source") or "unknown")
    capture_sha256 = str(diff_report.get("capture_bin_sha256") or "")
    prebuilt_overlay = str(diff_report.get("prebuilt_overlay") or "unknown")
    evidence_blocks: dict[str, Any] = {
        "differential_oracle": {
            **diff_report["metrics"],
            "red_flags_passed": diff_report.get("red_flags_passed", 0),
            "red_flag_error": diff_report.get("red_flag_error"),
            "legs": diff_report.get("legs", []),
            "capture_bin_source": capture_source,
            "capture_bin_sha256": capture_sha256,
            "prebuilt_overlay": prebuilt_overlay,
        },
        "mir_eval_cargo_test": mir_eval_status,
        "perf_metrics": perf_snippet,
    }
    if diff_report.get("mutant_check") is not None:
        evidence_blocks["oracle_mutants"] = diff_report["mutant_check"]

    return {
        "schema": DETAIL_SCHEMA,
        "alpha_notice": ALPHA_NOTICE,
        "repo": repo,
        "branch": branch,
        "commit_sha": commit_sha,
        "commit_unix_ts": commit_unix_ts,
        "mir_dialect": diff_report.get("mir_dialect", "profile_v1"),
        "environment_profile": environment_profile,
        "trust_tier": "candidate:mir_semantics",
        "evidence_blocks": evidence_blocks,
        "differential_runs": [
            {
                "manifest_path": diff_report.get("manifest_path", ""),
                "legs": diff_report.get("legs", []),
                "capture_bin_source": capture_source,
                "capture_bin_sha256": capture_sha256,
                "prebuilt_overlay": prebuilt_overlay,
                "metrics": diff_report["metrics"],
                "cases": diff_report.get("cases", []),
            }
        ],
        "known_bugs": failing_cases,
        "corpus_blockers": [],
    }


def _verdict_is_ok(verdict: Any) -> bool:
    if not isinstance(verdict, dict):
        return False
    return verdict.get("kind") in (
        "agree_value",
        "agree_undefined_behavior",
        "sound_conservative_abstraction",
    )


def report_passes(detail: dict[str, Any], *, require_mutants: bool = True) -> bool:
    """Validate cases, zero divergences, red flags, mutants, and mir-eval."""
    runs = detail.get("differential_runs", [])
    if not isinstance(runs, list) or not runs:
        return False
    cases = runs[0].get("cases", [])
    if not isinstance(cases, list) or not cases:
        return False
    if any(not _verdict_is_ok(c.get("verdict")) for c in cases):
        return False

    blocks = detail.get("evidence_blocks", {})
    diff_ev = blocks.get("differential_oracle", {})
    if diff_ev.get("red_flag_error") is not None:
        return False
    if int(diff_ev.get("red_flags_passed", 0)) <= 0:
        return False
    if int(diff_ev.get("compared_count", 0)) != len(cases):
        return False
    if int(diff_ev.get("kernel_checked_pass_count", 0)) <= 0:
        return False
    if int(diff_ev.get("kernel_checked_ub_count", 0)) <= 0:
        return False
    if int(diff_ev.get("unsound_missed_fault_count", 1)) > 0:
        return False
    if int(diff_ev.get("value_mismatch_count", 1)) > 0:
        return False
    if int(diff_ev.get("unexpected_conservative_count", 1)) > 0:
        return False
    if int(diff_ev.get("leg_divergence_count", 1)) > 0:
        return False
    if detail.get("known_bugs"):
        return False

    mutants = blocks.get("oracle_mutants")
    if require_mutants and not isinstance(mutants, dict):
        return False
    if isinstance(mutants, dict):
        total = int(mutants.get("total_mutants", 0))
        killed = int(mutants.get("killed_mutants", 0))
        if total == 0 or killed != total:
            return False
        probes = mutants.get("synthetic_lean_probes", [])
        if not isinstance(probes, list) or not probes or any(
            not p.get("passed") for p in probes
        ):
            return False

    mir_eval = blocks.get("mir_eval_cargo_test", {})
    if mir_eval.get("passed") is False or (
        mir_eval.get("executed") and not mir_eval.get("passed")
    ):
        return False
    return True


def run_anneal_diff(
    *,
    anneal_root: Path,
    manifest: Path | None,
    capture_bin: Path | None,
    mir_eval_bin: Path | None,
    cache_root: Path | None,
    self_check_oracle: bool,
    anneal_diff_bin: Path | None = None,
) -> tuple[int, dict[str, Any]]:
    """Run `anneal-diff run --json` and parse its JSON payload."""
    caller_cwd = Path.cwd()
    anneal_root_canon = _resolve_cli_path(
        anneal_root, "anneal_root", base_dir=caller_cwd
    ).resolve(strict=True)
    if anneal_diff_bin is not None:
        anneal_diff_abs = _resolve_cli_path(
            anneal_diff_bin, "anneal-diff binary", base_dir=caller_cwd
        )
        cmd = [str(anneal_diff_abs), "run", "--json"]
    else:
        cargo = _resolve_command_token(
            os.environ.get("CARGO", "cargo"), caller_cwd
        )
        cmd = [
            cargo,
            "run",
            "--locked",
            "-q",
            "-p",
            "anneal-differential-tests",
            "--bin",
            "anneal-diff",
            "--",
            "run",
            "--json",
        ]
    if manifest is not None:
        manifest_abs = _resolve_cli_path(
            manifest, "manifest", base_dir=caller_cwd
        )
        cmd.extend(["--manifest", str(manifest_abs)])
    if capture_bin is not None:
        capture_abs = _resolve_cli_path(
            capture_bin, "capture binary", base_dir=caller_cwd
        )
        cmd.extend(["--capture-bin", str(capture_abs)])
    if mir_eval_bin is not None:
        mir_eval_abs = _resolve_cli_path(
            mir_eval_bin, "mir-eval binary", base_dir=caller_cwd
        )
        cmd.extend(["--mir-eval-bin", str(mir_eval_abs)])
    if cache_root is not None:
        cache_abs = _resolve_cli_path(
            cache_root, "cache root", base_dir=caller_cwd
        )
        cmd.extend(["--cache-root", str(cache_abs)])
    if self_check_oracle:
        cmd.append("--self-check-oracle")

    child_env = _anchor_cargo_child_env(
        os.environ.copy(), caller_cwd, include_diff_vars=True
    )

    proc = subprocess.run(
        cmd,
        cwd=anneal_root_canon,
        env=child_env,
        capture_output=True,
        text=True,
        check=False,
    )
    stdout = proc.stdout.strip()
    if not stdout:
        raise RuntimeError(
            f"anneal-diff produced no JSON stdout (rc={proc.returncode}): {proc.stderr}"
        )
    parsed = json.loads(stdout)
    return proc.returncode, parsed


def main(argv: list[str] | None = None) -> int:
    caller_cwd = Path.cwd()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--anneal-root",
        type=Path,
        default=_default_anneal_root(),
        help="Path to the anneal/ workspace root.",
    )
    parser.add_argument("--manifest", type=Path, help="Override differential manifest.")
    parser.add_argument(
        "--capture-bin",
        type=Path,
        help="Explicit anneal-rustc-capture binary path.",
    )
    mir_eval_group = parser.add_mutually_exclusive_group()
    mir_eval_group.add_argument(
        "--mir-eval-manifest",
        type=Path,
        help="Optional explicit anneal-mir-eval Cargo.toml manifest to test and build.",
    )
    mir_eval_group.add_argument(
        "--mir-eval-bin",
        type=Path,
        help="Optional prebuilt anneal-mir-eval binary path.",
    )
    parser.add_argument(
        "--anneal-diff-bin",
        type=Path,
        help="Optional prebuilt anneal-diff binary path.",
    )
    parser.add_argument(
        "--cache-root",
        type=Path,
        help="Optional cache root for Miri sysroot and Lean DAG artifacts.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Optional output path for anneal-semantic-detail/v1 JSON.",
    )
    parser.add_argument(
        "--perf-metrics-out",
        type=Path,
        help="Optional output path for differential metric snippet JSON.",
    )
    parser.add_argument(
        "--perf-record-out",
        type=Path,
        help="Optional output path for full validated `anneal-perf-record/v1` JSON.",
    )
    parser.add_argument(
        "--expect-capture-source",
        help="Optional expected `capture_bin_source` provenance to enforce fail-closed.",
    )
    parser.add_argument(
        "--no-self-check-oracle",
        action="store_true",
        help="Disable injected oracle mutant checks.",
    )
    parser.add_argument(
        "--skip-mir-eval-tests",
        action="store_true",
        help="Skip running --mir-eval-manifest unit/CLI tests even if supplied.",
    )
    parser.add_argument(
        "--allow-unknown-git",
        action="store_true",
        help="Allow fallback git metadata when running outside a git checkout.",
    )
    parser.add_argument("--repo", default="google/zerocopy")
    parser.add_argument("--branch")
    parser.add_argument(
        "--commit-sha",
        help="Explicit 40-hex commit SHA override for telemetry metadata.",
    )
    parser.add_argument(
        "--commit-unix-ts",
        type=int,
        help="Explicit commit UNIX timestamp override (>= 0) for telemetry metadata.",
    )
    args = parser.parse_args(argv)

    if (args.commit_sha is None) != (args.commit_unix_ts is None):
        parser.error(
            "--commit-sha and --commit-unix-ts must be provided together"
        )
    if args.commit_sha is not None and (
        len(args.commit_sha) != 40
        or any(c not in "0123456789abcdefABCDEF" for c in args.commit_sha)
    ):
        parser.error("--commit-sha must be a 40-character hexadecimal digest")
    if args.commit_unix_ts is not None and args.commit_unix_ts < 0:
        parser.error("--commit-unix-ts must be a non-negative integer")

    anneal_root = _resolve_cli_path(
        args.anneal_root, "anneal_root", base_dir=caller_cwd
    ).resolve(strict=True)
    manifest_path = _resolve_optional_cli_path(
        args.manifest, "manifest", base_dir=caller_cwd
    )
    capture_bin_path = _resolve_optional_cli_path(
        args.capture_bin, "capture_bin", base_dir=caller_cwd
    )
    mir_eval_manifest_path = _resolve_optional_cli_path(
        args.mir_eval_manifest, "mir_eval_manifest", base_dir=caller_cwd
    )
    mir_eval_bin_path = _resolve_optional_cli_path(
        args.mir_eval_bin, "mir_eval_bin", base_dir=caller_cwd
    )
    anneal_diff_bin_path = _resolve_optional_cli_path(
        args.anneal_diff_bin, "anneal_diff_bin", base_dir=caller_cwd
    )
    cache_root_path = _resolve_optional_cli_path(
        args.cache_root, "cache_root", base_dir=caller_cwd
    )
    output_path = _resolve_optional_cli_path(
        args.output, "output", base_dir=caller_cwd
    )
    perf_metrics_out_path = _resolve_optional_cli_path(
        args.perf_metrics_out, "perf_metrics_out", base_dir=caller_cwd
    )
    perf_record_out_path = _resolve_optional_cli_path(
        args.perf_record_out, "perf_record_out", base_dir=caller_cwd
    )

    mir_eval_status, built_mir_eval_bin = maybe_run_mir_eval_manifest(
        mir_eval_manifest_path, skip_tests=args.skip_mir_eval_tests
    )
    if (
        mir_eval_manifest_path is not None
        and mir_eval_status.get("passed") is False
    ):
        print(
            f"mir-eval manifest check failed: {mir_eval_status.get('error', '')}",
            file=sys.stderr,
        )
        return 1
    effective_mir_eval_bin = (
        built_mir_eval_bin
        if mir_eval_manifest_path is not None
        else mir_eval_bin_path
    )

    self_check_oracle = not args.no_self_check_oracle
    diff_rc, diff_report = run_anneal_diff(
        anneal_root=anneal_root,
        manifest=manifest_path,
        capture_bin=capture_bin_path,
        mir_eval_bin=effective_mir_eval_bin,
        cache_root=cache_root_path,
        self_check_oracle=self_check_oracle,
        anneal_diff_bin=anneal_diff_bin_path,
    )

    branch, commit_sha, commit_unix_ts = _git_metadata(
        anneal_root,
        allow_unknown_git=args.allow_unknown_git,
        commit_sha_override=args.commit_sha,
        commit_unix_ts_override=args.commit_unix_ts,
        branch_override=args.branch,
    )
    env_profile = _collect_environment(anneal_root, caller_cwd=caller_cwd)
    detail = build_semantic_detail_report(
        diff_report=diff_report,
        mir_eval_status=mir_eval_status,
        repo=args.repo,
        branch=branch,
        commit_sha=commit_sha,
        commit_unix_ts=commit_unix_ts,
        environment_profile=env_profile,
    )
    perf_snippet = build_perf_metrics_snippet(diff_report)
    perf_record = build_perf_record_from_snippet(
        perf_snippet,
        branch=branch,
        commit_sha=commit_sha,
        commit_unix_ts=commit_unix_ts,
        environment_profile=env_profile,
    )

    if args.expect_capture_source:
        actual_src = diff_report.get("capture_bin_source")
        actual_sha = str(diff_report.get("capture_bin_sha256") or "")
        valid_hex_sha = len(actual_sha) == 64 and all(
            ch in "0123456789abcdef" for ch in actual_sha
        )
        if actual_src != args.expect_capture_source or not valid_hex_sha:
            print(
                f"capture provenance mismatch: expected source={args.expect_capture_source!r}, "
                f"got source={actual_src!r}, sha256={actual_sha!r}",
                file=sys.stderr,
            )
            return 1

    if output_path is not None:
        ensure_not_symlink(output_path, "output")
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(
            json.dumps(detail, indent=2) + "\n", encoding="utf-8"
        )
    if perf_metrics_out_path is not None:
        ensure_not_symlink(perf_metrics_out_path, "perf_metrics_out")
        perf_metrics_out_path.parent.mkdir(parents=True, exist_ok=True)
        perf_metrics_out_path.write_text(
            json.dumps(perf_snippet, indent=2) + "\n", encoding="utf-8"
        )
    if perf_record_out_path is not None:
        ensure_not_symlink(perf_record_out_path, "perf_record_out")
        perf_record_out_path.parent.mkdir(parents=True, exist_ok=True)
        perf_record_out_path.write_text(
            json.dumps(perf_record, indent=2) + "\n", encoding="utf-8"
        )

    print(json.dumps(detail, indent=2))
    if diff_rc != 0 or not report_passes(detail, require_mutants=self_check_oracle):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
