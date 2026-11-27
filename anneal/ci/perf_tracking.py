#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Collect, validate, check, and analyze Anneal performance telemetry."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import fnmatch
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from typing import Any

_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

import anneal_ci_lib  # noqa: E402
import prebuild_bundled_oleans  # noqa: E402
import verify_zerocopy  # noqa: E402

RECORD_SCHEMA = "anneal-perf-record/v1"
BUDGETS_SCHEMA = "anneal-perf-budgets/v1"

ALLOWED_TOP_LEVEL_KEYS = frozenset(
    {"schema", "commit", "environment", "sampling", "metrics"}
)
REQUIRED_COMMIT_KEYS = frozenset(
    {"sha", "short_sha", "timestamp", "unix_ts", "subject", "branch"}
)
REQUIRED_ENV_KEYS = frozenset(
    {
        "profile",
        "os",
        "arch",
        "cpu_model",
        "vcpu_count",
        "ram_total_kib",
        "lean_version",
        "rustc_version",
    }
)
REQUIRED_SAMPLING_KEYS = frozenset({"verify_repeats", "aggregation"})
ALLOWED_SAMPLING_KEYS = REQUIRED_SAMPLING_KEYS | frozenset({"rss_method"})

SHA40_RE = re.compile(r"^[0-9a-f]{40}$")
METRIC_ID_RE = re.compile(r"^[a-z0-9_]+(\.[a-z0-9_-]+){2,}$")
TIME_RSS_RE = re.compile(r"__ANNEAL_TIME_MAXRSS_KIB__=(\d+)")

COLLECTABLE_CATEGORIES = (
    "verify",
    "theory_elab",
    "memory_rss",
    "artifact_size",
    "zerocopy_proofs",
)
RENDER_ONLY_CATEGORIES = (
    # Schema- and dashboard-supported via `perf_tracking.validate_record`,
    # `analyze`, and `render_perf_dashboard.py` when callers invoke
    # `ci/check_mir_differential.py --perf-record-out` with Git or explicit
    # commit metadata; neither collected by `collect_record` / `anneal-perf.yml`
    # nor uploaded from `.git`-less `ci-core` `anneal-ws-test` runs yet.
    "differential_oracle",
)
CATEGORIES = (*COLLECTABLE_CATEGORIES, *RENDER_ONLY_CATEGORIES)
ALLOWED_CATEGORIES = frozenset(CATEGORIES)
ALLOWED_COLLECTABLE_CATEGORIES = frozenset(COLLECTABLE_CATEGORIES)
DEFAULT_TIME_BIN = Path("/usr/bin/time")

DEFAULT_ROLLING_POLICY: dict[str, Any] = {
    "window": 25,
    "min_history": 5,
    "confirmed_z": 3.5,
    "spike_z": 4.0,
    "min_rel_delta": 0.08,
    "spike_min_rel_delta": 0.10,
    "severe_z": 6.0,
    "severe_rel_delta": 0.20,
    "mad_floor_rel": 0.015,
    "deterministic_rel_delta": 0.05,
    "deterministic_min_bytes": 4096,
}

DEFAULT_BUDGETS_PATH = _CI_DIR / "perf_budgets.json"

LEAN_BASE_COMPILE_FLAGS = [
    "-j1",
    "-M2048",
    "-t0",
    "-DElab.async=false",
    "-Ddebug.skipKernelTC=false",
]

THEORY_COMPILE_FLAGS = [
    *LEAN_BASE_COMPILE_FLAGS,
    "-DwarningAsError=true",
]


class ValidationError(ValueError):
    """Raised when telemetry or budget inputs violate schema invariants."""


@dataclass(frozen=True)
class SubprocessMeasurement:
    """Result and isolated resource accounting for one subprocess run."""

    returncode: int
    stdout: str
    stderr: str
    elapsed_ms: float
    maxrss_kib: int
    rss_method: str


def ensure_not_symlink(path: Path, label: str = "path") -> None:
    """Reject symlink inputs/outputs fail-closed."""
    anneal_ci_lib.ensure_not_symlink(path, label, exc_type=ValidationError)


def _is_non_bool_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _is_finite_nonneg_number(value: Any) -> bool:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return False
    return math.isfinite(value) and value >= 0


def validate_record(record: Any) -> dict[str, Any]:
    """Validate one `anneal-perf-record/v1` object fail-closed."""
    if not isinstance(record, dict):
        raise ValidationError("record must be a JSON object")

    keys = set(record.keys())
    unknown = keys - ALLOWED_TOP_LEVEL_KEYS
    if unknown:
        raise ValidationError(f"unknown top-level keys: {sorted(unknown)}")
    missing = ALLOWED_TOP_LEVEL_KEYS - keys
    if missing:
        raise ValidationError(f"missing top-level keys: {sorted(missing)}")

    if record["schema"] != RECORD_SCHEMA:
        raise ValidationError(
            f"unsupported schema {record['schema']!r} (expected {RECORD_SCHEMA!r})"
        )

    commit = record["commit"]
    if not isinstance(commit, dict):
        raise ValidationError("commit must be an object")
    c_keys = set(commit.keys())
    if c_keys != REQUIRED_COMMIT_KEYS:
        raise ValidationError(
            f"commit keys mismatch: {sorted(c_keys)} vs {sorted(REQUIRED_COMMIT_KEYS)}"
        )
    if not isinstance(commit["sha"], str) or not SHA40_RE.match(commit["sha"]):
        raise ValidationError(f"invalid 40-hex commit.sha: {commit['sha']!r}")
    for str_k in ("short_sha", "timestamp", "subject", "branch"):
        if not isinstance(commit[str_k], str) or not commit[str_k]:
            if str_k == "subject" and isinstance(commit[str_k], str):
                continue
            raise ValidationError(f"commit.{str_k} must be a non-empty string")
    if not _is_non_bool_int(commit["unix_ts"]) or commit["unix_ts"] < 0:
        raise ValidationError(f"invalid commit.unix_ts: {commit['unix_ts']!r}")

    env = record["environment"]
    if not isinstance(env, dict):
        raise ValidationError("environment must be an object")
    e_keys = set(env.keys())
    if e_keys != REQUIRED_ENV_KEYS:
        raise ValidationError(
            f"environment keys mismatch: {sorted(e_keys)} vs {sorted(REQUIRED_ENV_KEYS)}"
        )
    for str_k in (
        "profile",
        "os",
        "arch",
        "cpu_model",
        "lean_version",
        "rustc_version",
    ):
        if not isinstance(env[str_k], str) or not env[str_k]:
            raise ValidationError(f"environment.{str_k} must be a non-empty string")
    if not _is_non_bool_int(env["vcpu_count"]) or env["vcpu_count"] < 1:
        raise ValidationError(f"invalid environment.vcpu_count: {env['vcpu_count']!r}")
    if not _is_non_bool_int(env["ram_total_kib"]) or env["ram_total_kib"] < 0:
        raise ValidationError(
            f"invalid environment.ram_total_kib: {env['ram_total_kib']!r}"
        )

    sampling = record["sampling"]
    if not isinstance(sampling, dict):
        raise ValidationError("sampling must be an object")
    s_keys = set(sampling.keys())
    if not REQUIRED_SAMPLING_KEYS.issubset(s_keys) or (s_keys - ALLOWED_SAMPLING_KEYS):
        raise ValidationError(f"invalid sampling keys: {sorted(s_keys)}")
    if not _is_non_bool_int(sampling["verify_repeats"]) or sampling["verify_repeats"] < 1:
        raise ValidationError(
            f"invalid sampling.verify_repeats: {sampling['verify_repeats']!r}"
        )
    if not isinstance(sampling["aggregation"], str) or not sampling["aggregation"]:
        raise ValidationError("sampling.aggregation must be a non-empty string")
    if "rss_method" in sampling and sampling["rss_method"] not in (
        "usr_bin_time",
        "fallback_wait4",
    ):
        raise ValidationError(f"invalid sampling.rss_method: {sampling['rss_method']!r}")

    metrics = record["metrics"]
    if not isinstance(metrics, dict) or not metrics:
        raise ValidationError("metrics must be a non-empty object")
    for metric_id, val in metrics.items():
        if not isinstance(metric_id, str) or not METRIC_ID_RE.match(metric_id):
            raise ValidationError(f"invalid metric ID: {metric_id!r}")
        category = metric_id.split(".", 1)[0]
        if category not in ALLOWED_CATEGORIES:
            raise ValidationError(
                f"unknown metric category {category!r} in {metric_id!r}"
            )
        if not _is_finite_nonneg_number(val):
            raise ValidationError(
                f"metric {metric_id!r} must be finite non-negative number, got {val!r}"
            )
    return record


def load_record(path: Path) -> dict[str, Any]:
    """Read and validate one JSON telemetry record."""
    ensure_not_symlink(path, "record file")
    try:
        raw = path.read_text(encoding="utf-8")
        data = json.loads(raw)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValidationError(f"cannot parse record {path}: {exc}") from exc
    return validate_record(data)


def load_records_jsonl(path: Path) -> list[dict[str, Any]]:
    """Read and validate all non-empty lines of a JSONL telemetry log."""
    ensure_not_symlink(path, "records JSONL")
    if not path.exists():
        return []
    records: list[dict[str, Any]] = []
    for lineno, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        stripped = line.strip()
        if not stripped:
            continue
        try:
            obj = json.loads(stripped)
            records.append(validate_record(obj))
        except (json.JSONDecodeError, ValidationError) as exc:
            raise ValidationError(f"{path}:{lineno}: {exc}") from exc
    return records


def load_budgets(path: Path) -> dict[str, Any]:
    """Read and validate `anneal-perf-budgets/v1` JSON."""
    ensure_not_symlink(path, "budgets file")
    if not path.is_file():
        raise ValidationError(f"missing budgets file: {path}")
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or data.get("schema") != BUDGETS_SCHEMA:
        raise ValidationError(f"unsupported budgets schema in {path}")
    rolling = dict(DEFAULT_ROLLING_POLICY)
    raw_rolling = data.get("rolling", {})
    if not isinstance(raw_rolling, dict):
        raise ValidationError("budgets.rolling must be an object")
    rolling.update(raw_rolling)
    budgets = data.get("budgets", [])
    if not isinstance(budgets, list):
        raise ValidationError("budgets.budgets must be a list")
    for idx, rule in enumerate(budgets):
        if not isinstance(rule, dict):
            raise ValidationError(f"budgets[{idx}] must be an object")
        if not rule.get("metric") and not rule.get("pattern"):
            raise ValidationError(f"budgets[{idx}] needs metric or pattern")
        for bound in ("max_value", "min_value"):
            if bound in rule and not _is_finite_nonneg_number(rule[bound]):
                raise ValidationError(f"budgets[{idx}].{bound} invalid: {rule[bound]!r}")
    return {"schema": BUDGETS_SCHEMA, "rolling": rolling, "budgets": budgets}


def resolve_budgets_cfg(explicit_path: Path | None) -> dict[str, Any] | None:
    """Load explicit `--budgets` fail-closed, or default budgets if present."""
    if explicit_path is not None:
        return load_budgets(explicit_path)
    if DEFAULT_BUDGETS_PATH.exists() or DEFAULT_BUDGETS_PATH.is_symlink():
        return load_budgets(DEFAULT_BUDGETS_PATH)
    return None


def describe_metric(metric_id: str) -> dict[str, Any]:
    """Infer canonical `MetricDescriptor` metadata from a metric ID."""
    if not METRIC_ID_RE.match(metric_id):
        raise ValidationError(f"invalid metric ID: {metric_id!r}")
    parts = metric_id.split(".")
    category = parts[0]
    if category not in ALLOWED_CATEGORIES:
        raise ValidationError(f"unknown category in metric ID: {metric_id!r}")

    if category == "verify":
        subject = parts[1]
        measure = parts[2]
        if measure.endswith("_total_ms"):
            phase = "total"
        elif measure.endswith("_capture_ms"):
            phase = "capture"
        elif measure.endswith("_proof_audit_ms"):
            phase = "proof_audit"
        else:
            phase = measure
        mode = measure.removesuffix(f"_{phase}_ms").replace("_", " ")
        return {
            "id": metric_id,
            "label": f"{subject} verify ({mode}, {phase.replace('_', ' ')})",
            "category": "verify",
            "group": f"verify.{subject}.{phase}",
            "unit": "ms",
            "direction": "lower_is_better",
            "deterministic": False,
        }

    if category == "theory_elab":
        if parts[1] == "summary":
            return {
                "id": metric_id,
                "label": f"theory summary ({parts[2].replace('_', ' ')})",
                "category": "theory_elab",
                "group": "theory_elab.summary",
                "unit": "ms",
                "direction": "lower_is_better",
                "deterministic": False,
            }
        mod_name = parts[1].replace("_", ".")
        return {
            "id": metric_id,
            "label": f"{mod_name} (cold lean -j1)",
            "category": "theory_elab",
            "group": "theory_elab.module.cold_j1",
            "unit": "ms",
            "direction": "lower_is_better",
            "deterministic": False,
        }

    if category == "memory_rss":
        target = parts[1]
        if target.startswith("theory_"):
            mod_name = target[len("theory_") :].replace("_", ".")
            label = f"{mod_name} peak RSS"
            group = "memory_rss.theory_elab"
        elif target == "theory_elab":
            label = "theory_elab max module RSS"
            group = "memory_rss.theory_elab"
        elif target.startswith("zerocopy_"):
            unit_name = target[len("zerocopy_") :]
            label = f"zerocopy {unit_name} peak RSS"
            group = "memory_rss.zerocopy_proofs"
        else:
            label = f"{target.replace('_', ' ')} ({parts[2].replace('_', ' ')})"
            group = f"memory_rss.{target}"
        return {
            "id": metric_id,
            "label": label,
            "category": "memory_rss",
            "group": group,
            "unit": "KiB",
            "direction": "lower_is_better",
            "deterministic": False,
        }

    if category == "artifact_size":
        scope = parts[1]
        if scope == "module" and len(parts) >= 4:
            mod_name = parts[2].replace("_", ".")
            part_name = parts[3].removesuffix("_bytes").replace("_", ".")
            return {
                "id": metric_id,
                "label": f"{mod_name} .{part_name} size",
                "category": "artifact_size",
                "group": f"artifact_size.module.{parts[2]}",
                "unit": "B",
                "direction": "lower_is_better",
                "deterministic": True,
            }
        if scope == "bundled_olean":
            part_name = parts[2].removesuffix("_bytes")
            return {
                "id": metric_id,
                "label": f"bundled .olean* ({part_name})",
                "category": "artifact_size",
                "group": "artifact_size.bundled_olean",
                "unit": "B",
                "direction": "lower_is_better",
                "deterministic": True,
            }
        return {
            "id": metric_id,
            "label": f"{scope} {parts[2].removesuffix('_bytes')}",
            "category": "artifact_size",
            "group": f"artifact_size.{scope}",
            "unit": "B",
            "direction": "lower_is_better",
            "deterministic": True,
        }

    if category == "differential_oracle":
        section = parts[1]
        measure = parts[2]
        if section == "mutants":
            return {
                "id": metric_id,
                "label": f"differential oracle ({section} {measure.removesuffix('_pct').replace('_', ' ')})",
                "category": "differential_oracle",
                "group": "differential_oracle.mutants",
                "unit": "%",
                "direction": "higher_is_better",
                "deterministic": True,
            }
        lower_measures = {
            "unsound_missed_fault_count",
            "value_mismatch_count",
            "unexpected_conservative_count",
            "leg_divergence_count",
            "unsound_accept_count",
            "authority_disagreement_count",
            "conservative_over_approx_count",
            "spurious_lean_ub_count",
            "admitted_authority_ub_count",
        }
        direction = (
            "lower_is_better" if measure in lower_measures else "higher_is_better"
        )
        return {
            "id": metric_id,
            "label": f"differential oracle ({section} {measure.replace('_', ' ')})",
            "category": "differential_oracle",
            "group": f"differential_oracle.{section}",
            "unit": "count",
            "direction": direction,
            "deterministic": True,
        }

    # `zerocopy_proofs`
    unit_name = parts[1]
    measure = parts[2]
    if unit_name == "suite" and measure == "verified_units_count":
        return {
            "id": metric_id,
            "label": "zerocopy verified proof units",
            "category": "zerocopy_proofs",
            "group": "zerocopy_proofs.suite.count",
            "unit": "count",
            "direction": "higher_is_better",
            "deterministic": True,
        }
    if unit_name == "suite":
        return {
            "id": metric_id,
            "label": "zerocopy suite total time",
            "category": "zerocopy_proofs",
            "group": "zerocopy_proofs.suite.total",
            "unit": "ms",
            "direction": "lower_is_better",
            "deterministic": False,
        }
    phase = measure.removesuffix("_ms")
    return {
        "id": metric_id,
        "label": f"zerocopy {unit_name} ({phase.replace('_', ' ')})",
        "category": "zerocopy_proofs",
        "group": f"zerocopy_proofs.{phase}",
        "unit": "ms",
        "direction": "lower_is_better",
        "deterministic": False,
    }


def _run_fork_wait4(
    cmd: list[str],
    *,
    cwd: Path | None,
    env: dict[str, str],
    timeout: float,
) -> SubprocessMeasurement:
    """Fallback isolated child runner when `/usr/bin/time` is unavailable."""
    with tempfile.TemporaryDirectory(prefix="anneal-wait4-") as tmp_dir:
        tmp = Path(tmp_dir)
        out_path = tmp / "stdout.txt"
        err_path = tmp / "stderr.txt"
        started = time.monotonic()
        with out_path.open("w+b") as out_f, err_path.open("w+b") as err_f:
            pid = os.fork()
            if pid == 0:
                try:
                    if cwd is not None:
                        os.chdir(str(cwd))
                    os.dup2(out_f.fileno(), 1)
                    os.dup2(err_f.fileno(), 2)
                    os.execvpe(cmd[0], cmd, env)
                except BaseException as exc:
                    os.write(2, f"exec failed: {exc}\n".encode("utf-8"))
                    os._exit(127)
            deadline = started + timeout
            status = 0
            rusage = None
            while True:
                waited_pid, status, rusage = os.wait4(pid, os.WNOHANG)
                if waited_pid == pid:
                    break
                if time.monotonic() >= deadline:
                    os.kill(pid, 9)
                    _, status, rusage = os.wait4(pid, 0)
                    raise subprocess.TimeoutExpired(cmd, timeout)
                time.sleep(0.01)
        elapsed_ms = (time.monotonic() - started) * 1000.0
        returncode = os.waitstatus_to_exitcode(status)
        assert rusage is not None
        raw_rss = int(rusage.ru_maxrss)
        maxrss_kib = raw_rss // 1024 if sys.platform == "darwin" else raw_rss
        return SubprocessMeasurement(
            returncode=returncode,
            stdout=out_path.read_text(encoding="utf-8", errors="replace"),
            stderr=err_path.read_text(encoding="utf-8", errors="replace"),
            elapsed_ms=elapsed_ms,
            maxrss_kib=max(0, maxrss_kib),
            rss_method="fallback_wait4",
        )


def run_measured_subprocess(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    timeout: float = 600.0,
    time_bin: Path | None = DEFAULT_TIME_BIN,
) -> SubprocessMeasurement:
    """Run `cmd` with fresh-`exec` `/usr/bin/time` RSS isolation on Linux.

    Using `/usr/bin/time` avoids `posix_spawn(CLONE_VM)` `exec_mm_put_old`
    contaminating small child `ru_maxrss` with the Python parent's RSS.
    """
    effective_env = os.environ.copy() if env is None else dict(env)
    use_time = (
        time_bin is not None
        and sys.platform.startswith("linux")
        and time_bin.is_file()
        and os.access(time_bin, os.X_OK)
    )
    if not use_time:
        return _run_fork_wait4(cmd, cwd=cwd, env=effective_env, timeout=timeout)

    with tempfile.TemporaryDirectory(prefix="anneal-time-") as tmp_dir:
        rss_path = Path(tmp_dir) / "maxrss.txt"
        wrapped = [
            str(time_bin),
            "-f",
            "__ANNEAL_TIME_MAXRSS_KIB__=%M",
            "-o",
            str(rss_path),
            "--",
            *cmd,
        ]
        started = time.monotonic()
        proc = subprocess.run(
            wrapped,
            cwd=cwd,
            env=effective_env,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
        elapsed_ms = (time.monotonic() - started) * 1000.0
        rss_text = (
            rss_path.read_text(encoding="utf-8", errors="replace")
            if rss_path.is_file()
            else ""
        )
        match = TIME_RSS_RE.search(rss_text)
        if not match:
            raise RuntimeError(
                f"missing /usr/bin/time maxrss output for {cmd!r}: {rss_text!r}"
            )
        return SubprocessMeasurement(
            returncode=proc.returncode,
            stdout=proc.stdout,
            stderr=proc.stderr,
            elapsed_ms=elapsed_ms,
            maxrss_kib=int(match.group(1)),
            rss_method="usr_bin_time",
        )


def _atomic_write_text(path: Path, text: str) -> None:
    anneal_ci_lib.atomic_write_text(path, text, exc_type=ValidationError)


def _read_linux_cpu_model() -> str:
    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.is_file():
        for line in cpuinfo.read_text(encoding="utf-8", errors="replace").splitlines():
            if line.lower().startswith("model name"):
                _, _, value = line.partition(":")
                cleaned = " ".join(value.split())
                if cleaned:
                    return cleaned
    return platform.processor() or platform.machine() or "unknown"


def _read_linux_ram_kib() -> int:
    meminfo = Path("/proc/meminfo")
    if meminfo.is_file():
        for line in meminfo.read_text(encoding="utf-8", errors="replace").splitlines():
            if line.startswith("MemTotal:"):
                parts = line.split()
                if len(parts) >= 2 and parts[1].isdigit():
                    return int(parts[1])
    return 0


def _read_git_commit_metadata(repo_root: Path, branch_override: str | None) -> dict[str, Any]:
    fmt = "%H%x00%ct%x00%cI%x00%s"
    out = subprocess.check_output(
        ["git", "-C", str(repo_root), "show", "-s", f"--format={fmt}", "HEAD"],
        text=True,
    )
    sha, unix_str, iso_ts, subject = out.rstrip("\n").split("\x00", 3)
    if branch_override:
        branch = branch_override
    else:
        branch_out = subprocess.check_output(
            ["git", "-C", str(repo_root), "rev-parse", "--abbrev-ref", "HEAD"],
            text=True,
        ).strip()
        branch = branch_out or "HEAD"
    # Normalize ISO timestamp to UTC Z when offset is +00:00 or preserve ISO.
    if iso_ts.endswith("+00:00"):
        iso_ts = iso_ts[:-6] + "Z"
    return {
        "sha": sha,
        "short_sha": sha[:12],
        "timestamp": iso_ts,
        "unix_ts": int(unix_str),
        "subject": subject,
        "branch": branch,
    }


def _read_tool_version(cmd: list[str], fallback: str) -> str:
    try:
        out = subprocess.check_output(cmd, text=True, stderr=subprocess.STDOUT).strip()
        first = out.splitlines()[0].strip() if out else ""
        return first or fallback
    except Exception:
        return fallback


def _discover_tools(
    anneal_root: Path,
    *,
    cli: Path | None,
    capture: Path | None,
    sysroot: Path | None,
    lean: Path | None,
    auditor: Path | None,
    install_root: Path | None,
    target_dir: Path | None,
) -> dict[str, Path | None]:
    return anneal_ci_lib.discover_tools(
        anneal_root,
        cli=cli,
        capture=capture,
        sysroot=sysroot,
        lean=lean,
        auditor=auditor,
        install_root=install_root,
        target_dir=target_dir,
    )


def _find_scalar_fixture(anneal_root: Path) -> Path:
    for rel in (
        "trusted/cargo-anneal/tests/fixtures/scalar",
        "trusted/cargo-anneal/assets/scalar",
    ):
        cand = anneal_root / rel
        if (cand / "request.json").is_file():
            return cand
    raise RuntimeError(f"scalar fixture not found under {anneal_root}")


def _stage_scalar_fixture(fixture_dir: Path, dst: Path) -> None:
    dst.mkdir(parents=True, exist_ok=True)
    for name in ("lib.rs", "Spec.lean", "Proof.lean", "request.json"):
        src = fixture_dir / name
        if src.is_file():
            shutil.copyfile(src, dst / name)


def _run_cargo_anneal_verify(
    *,
    cli: Path,
    request_path: Path,
    cwd: Path,
    capture: Path | None,
    sysroot: Path | None,
    lean: Path | None,
    xdg_cache_home: Path,
    extra_flags: list[str],
    artifacts_dir: Path | None,
    timeout: float,
    time_bin: Path | None,
) -> tuple[dict[str, Any], SubprocessMeasurement]:
    cmd = anneal_ci_lib.build_cargo_anneal_verify_cmd(
        cli=cli,
        request_path=request_path,
        capture=capture,
        sysroot=sysroot,
        lean=lean,
        artifacts_dir=artifacts_dir,
        extra_flags=extra_flags,
    )
    env = anneal_ci_lib.strip_actions_env(os.environ, include_oidc=True)
    env["XDG_CACHE_HOME"] = str(xdg_cache_home)
    meas = run_measured_subprocess(
        cmd, cwd=cwd, env=env, timeout=timeout, time_bin=time_bin
    )
    if meas.returncode != 0:
        raise RuntimeError(
            f"cargo-anneal verify failed (rc={meas.returncode}) for {cmd!r}:\n"
            f"stdout:\n{meas.stdout}\nstderr:\n{meas.stderr}"
        )
    receipt = json.loads(meas.stdout)
    if receipt.get("status") != "selected_unit_verified":
        raise RuntimeError(
            f"unexpected verification status {receipt.get('status')!r}: {receipt}"
        )
    return receipt, meas


def _hardlink_or_copy2(src: str, dst: str) -> str:
    """Create zero-byte hardlink when on same filesystem, else copy2."""
    try:
        os.link(src, dst)
        return dst
    except OSError:
        return shutil.copy2(src, dst)


def _mirror_lean_prefix_without_prebuilt(
    lean_bin: Path, staging_root: Path
) -> Path:
    """Mirror `lean_bin`'s prefix without sibling `share/anneal/prebuilt`."""
    src_prefix = lean_bin.resolve(strict=True).parent.parent
    dst_prefix = staging_root / "lean"
    shutil.copytree(
        src_prefix,
        dst_prefix,
        symlinks=True,
        copy_function=_hardlink_or_copy2,
    )
    return dst_prefix / "bin/lean"


def collect_verify_scalar(
    *,
    anneal_root: Path,
    tools: dict[str, Path | None],
    verify_repeats: int,
    cold_no_cache_repeats: int,
    timeout: float,
    time_bin: Path | None,
) -> tuple[dict[str, float | int], set[str]]:
    """Collect `verify.scalar.*` and `memory_rss.verify_scalar.*` metrics."""
    cli = tools["cli"]
    if cli is None:
        raise RuntimeError("missing cargo-anneal binary for `verify` collection")
    fixture_dir = _find_scalar_fixture(anneal_root)
    metrics: dict[str, float | int] = {}
    rss_methods: set[str] = set()

    lean_bin = tools["lean"]
    has_prebuilt = False
    if lean_bin is not None:
        lean_prefix_cand = lean_bin.resolve(strict=True).parent.parent
        prebuilt_manifest = lean_prefix_cand.parent / "share/anneal/prebuilt/manifest.json"
        has_prebuilt = prebuilt_manifest.is_file()

    with tempfile.TemporaryDirectory(prefix="anneal-perf-verify-") as tmp_str:
        tmp = Path(tmp_str)
        warm_xdg = tmp / "warm-xdg"
        warm_xdg.mkdir(parents=True)

        if has_prebuilt and lean_bin is not None:
            warm_lean = _mirror_lean_prefix_without_prebuilt(
                lean_bin, tmp / "no-prebuilt"
            )
        else:
            warm_lean = lean_bin

        # Prime warm_xdg once outside measured repeats using a Lean prefix
        # without sibling `share/anneal/prebuilt` so warm_disk populates and
        # exercises `$XDG_CACHE_HOME/anneal/olean-cache` cleanly.
        prime_dir = tmp / "prime-work"
        _stage_scalar_fixture(fixture_dir, prime_dir)
        _run_cargo_anneal_verify(
            cli=cli,
            request_path=prime_dir / "request.json",
            cwd=prime_dir,
            capture=tools["capture"],
            sysroot=tools["sysroot"],
            lean=warm_lean,
            xdg_cache_home=warm_xdg,
            extra_flags=[],
            artifacts_dir=None,
            timeout=timeout,
            time_bin=time_bin,
        )

        modes: list[tuple[str, int, list[str], Path | None, Path | None]] = [
            ("cold_no_cache", cold_no_cache_repeats, ["--no-cache"], None, lean_bin),
        ]
        if has_prebuilt:
            modes.append(
                ("cold_prebuilt", verify_repeats, ["--no-rebuild-bundled"], None, lean_bin)
            )
        modes.append(
            ("warm_disk", verify_repeats, ["--no-rebuild-bundled"], warm_xdg, warm_lean)
        )
        for mode_name, repeats, flags, fixed_xdg, mode_lean in modes:
            totals: list[float] = []
            captures: list[float] = []
            proof_audits: list[float] = []
            rss_vals: list[int] = []
            for rep in range(repeats):
                work_dir = tmp / f"{mode_name}-{rep}"
                _stage_scalar_fixture(fixture_dir, work_dir)
                if fixed_xdg is None:
                    xdg = tmp / f"xdg-{mode_name}-{rep}"
                    xdg.mkdir(parents=True)
                else:
                    xdg = fixed_xdg
                receipt, meas = _run_cargo_anneal_verify(
                    cli=cli,
                    request_path=work_dir / "request.json",
                    cwd=work_dir,
                    capture=tools["capture"],
                    sysroot=tools["sysroot"],
                    lean=mode_lean,
                    xdg_cache_home=xdg,
                    extra_flags=flags,
                    artifacts_dir=None,
                    timeout=timeout,
                    time_bin=time_bin,
                )
                rss_methods.add(meas.rss_method)
                t = receipt.get("timing_ms", {})
                totals.append(float(t.get("total", meas.elapsed_ms)))
                captures.append(float(t.get("capture", 0.0)))
                proof_audits.append(float(t.get("proof_and_audit", 0.0)))
                rss_vals.append(int(meas.maxrss_kib))

            metrics[f"verify.scalar.{mode_name}_total_ms"] = round(
                float(statistics.median(totals)), 3
            )
            metrics[f"verify.scalar.{mode_name}_capture_ms"] = round(
                float(statistics.median(captures)), 3
            )
            metrics[f"verify.scalar.{mode_name}_proof_audit_ms"] = round(
                float(statistics.median(proof_audits)), 3
            )
            metrics[f"memory_rss.verify_scalar.{mode_name}_maxrss_kib"] = int(
                statistics.median(rss_vals)
            )
    return metrics, rss_methods


def _lean_subprocess_env(lean_path: str | None = None) -> dict[str, str]:
    env: dict[str, str] = {}
    for k in (
        "HOME",
        "TMPDIR",
        "LANG",
        "LC_ALL",
        "LEAN_SYSROOT",
        "LD_LIBRARY_PATH",
        "DYLD_LIBRARY_PATH",
    ):
        if k in os.environ:
            env[k] = os.environ[k]
    env["PATH"] = os.environ.get("PATH", "/usr/bin:/bin")
    if lean_path is not None:
        env["LEAN_PATH"] = lean_path
    return env


def collect_theory_and_oleans(
    *,
    anneal_root: Path,
    lean_bin: Path,
    selected_modules: list[str] | None,
    timeout: float,
    time_bin: Path | None,
) -> tuple[dict[str, float | int], set[str]]:
    """Collect cold per-module `lean -j1` timings, RSS, and `.olean*` sizes."""
    lean_exec = lean_bin.resolve(strict=True)
    prefix_out = subprocess.check_output(
        [str(lean_exec), "--print-prefix"], text=True
    ).strip()
    lean_prefix = Path(prefix_out).resolve(strict=True)

    foundation_lock = json.loads(
        (anneal_root / "trusted/lean/foundation-lock.json").read_text(encoding="utf-8")
    )
    prebuild_bundled_oleans.parse_and_verify_library_lock(
        anneal_root / "trusted/audit/library-lock.json",
        lean_prefix,
        jobs=4,
    )
    foundation_graph: dict[str, list[dict[str, Any]]] = dict(foundation_lock["graph"])
    sysroot_graph: dict[str, list[dict[str, Any]]] = dict(foundation_graph)

    foundation_mods = set(foundation_lock["modules"].keys())
    _, path_shas = prebuild_bundled_oleans.compute_sysroot_manifest(
        lean_prefix / "lib/lean",
        jobs=4,
    )

    bundled_sources: dict[str, Path] = {}
    bundled_sources.update(prebuild_bundled_oleans.load_trusted_module_sources(anneal_root))
    bundled_sources.update(prebuild_bundled_oleans.load_theory_module_sources(anneal_root))

    inspector_src = anneal_root / "trusted/audit/TrustedBoundary.lean"
    if not inspector_src.is_file():
        raise RuntimeError(f"missing inspector source: {inspector_src}")

    if selected_modules:
        unknown = [
            m
            for m in selected_modules
            if m != "TrustedBoundary" and m not in bundled_sources
        ]
        if unknown:
            raise RuntimeError(f"unknown --modules selection: {unknown}")
        record_set = set(selected_modules)
    else:
        record_set = set(bundled_sources.keys()) | {"TrustedBoundary"}

    metrics: dict[str, float | int] = {}
    rss_methods: set[str] = set()
    mod_durations: dict[str, float] = {}
    mod_deps: dict[str, list[str]] = {}
    mod_rss: dict[str, int] = {}
    sum_public = 0
    sum_server = 0
    sum_private = 0

    with tempfile.TemporaryDirectory(prefix="anneal-perf-lean-") as tmp_str:
        tmp = Path(tmp_str)
        out_dir = tmp / "out"
        control_dir = tmp / "control"
        setup_dir = tmp / "setups"
        out_dir.mkdir(parents=True)
        control_dir.mkdir(parents=True)
        setup_dir.mkdir(parents=True)

        staged_inspector = control_dir / "TrustedBoundary.lean"
        staged_inspector.write_bytes(inspector_src.read_bytes())
        entry_file = control_dir / "TrustedBoundaryEntry.lean"
        entry_file.write_text("import TrustedBoundary\n", encoding="utf-8")

        inspector_out = out_dir / "TrustedBoundary.olean"
        ins_meas = run_measured_subprocess(
            [
                str(lean_exec),
                *LEAN_BASE_COMPILE_FLAGS,
                "-R",
                str(control_dir),
                "-o",
                str(inspector_out),
                str(staged_inspector),
            ],
            cwd=tmp,
            env=_lean_subprocess_env(str(lean_prefix / "lib/lean")),
            timeout=timeout,
            time_bin=time_bin,
        )
        if ins_meas.returncode != 0:
            raise RuntimeError(
                f"failed compiling TrustedBoundary.lean (rc={ins_meas.returncode}):\n"
                f"stdout:\n{ins_meas.stdout}\nstderr:\n{ins_meas.stderr}"
            )
        rss_methods.add(ins_meas.rss_method)

        if "TrustedBoundary" in record_set:
            mod_durations["TrustedBoundary"] = round(ins_meas.elapsed_ms, 3)
            mod_deps["TrustedBoundary"] = []
            mod_rss["TrustedBoundary"] = ins_meas.maxrss_kib
            metrics["theory_elab.trustedboundary.cold_j1_ms"] = round(
                ins_meas.elapsed_ms, 3
            )
            metrics["memory_rss.theory_trustedboundary.cold_j1_maxrss_kib"] = (
                ins_meas.maxrss_kib
            )
            for ext, suffix_key in (
                ("olean", "olean_bytes"),
                ("olean.server", "olean_server_bytes"),
                ("olean.private", "olean_private_bytes"),
            ):
                p = out_dir / f"TrustedBoundary.{ext}"
                if p.is_file():
                    sz = p.stat().st_size
                    metrics[f"artifact_size.module.trustedboundary.{suffix_key}"] = sz
                    if ext == "olean":
                        sum_public += sz
                    elif ext == "olean.server":
                        sum_server += sz
                    else:
                        sum_private += sz

        # Discover exact module DAG if any bundled Trusted.*/Anneal.* modules
        # are selected.
        needed_bundled = {m for m in record_set if m != "TrustedBoundary"}
        if needed_bundled:
            shutil.copyfile(inspector_out, control_dir / "TrustedBoundary.olean")
            headers_req = tmp / "headers.req.json"
            headers_res = tmp / "headers.res.json"
            headers_req.write_text(
                json.dumps(
                    {
                        "mode": "headers",
                        "sysroot": str(lean_prefix),
                        "foundation": sorted(foundation_mods),
                        "sources": [
                            [m, str(bundled_sources[m])]
                            for m in sorted(bundled_sources)
                        ],
                    }
                ),
                encoding="utf-8",
            )
            headers_proc = subprocess.run(
                [
                    str(lean_exec),
                    "-j1",
                    "-M2048",
                    "--run",
                    str(entry_file),
                    str(headers_req),
                    str(headers_res),
                ],
                cwd=tmp,
                env=_lean_subprocess_env(
                    os.pathsep.join([str(control_dir), str(lean_prefix / "lib/lean")])
                ),
                capture_output=True,
                text=True,
                timeout=timeout,
                check=False,
            )
            if headers_proc.returncode != 0:
                raise RuntimeError(
                    f"TrustedBoundary headers failed (rc={headers_proc.returncode}):\n"
                    f"stdout:\n{headers_proc.stdout}\nstderr:\n{headers_proc.stderr}"
                )
            parsed_headers = json.loads(headers_res.read_text(encoding="utf-8"))
            if not parsed_headers.get("ok"):
                raise RuntimeError(
                    f"TrustedBoundary headers error: {parsed_headers}"
                )

            bundled_edges: dict[str, list[dict[str, Any]]] = {}
            resolve_roots: set[str] = set()
            for item in parsed_headers["result"]["headers"]:
                mod = item["module"]
                bundled_edges[mod] = item["imports"]
                for edge in item["imports"]:
                    dep = edge["module"]
                    if dep in bundled_sources or dep in sysroot_graph:
                        continue
                    if not prebuild_bundled_oleans.is_allowed_pinned_library_module(dep):
                        raise RuntimeError(
                            f"bundled module {mod} imports disallowed external module {dep}"
                        )
                    resolve_roots.add(dep)

            if resolve_roots:
                resolve_req = tmp / "resolve.req.json"
                resolve_res = tmp / "resolve.res.json"
                resolve_req.write_text(
                    json.dumps(
                        {
                            "mode": "resolve-imports",
                            "sysroot": str(lean_prefix),
                            "modules": sorted(resolve_roots),
                        }
                    ),
                    encoding="utf-8",
                )
                resolve_proc = subprocess.run(
                    [
                        str(lean_exec),
                        "-j1",
                        "-M2048",
                        "--run",
                        str(entry_file),
                        str(resolve_req),
                        str(resolve_res),
                    ],
                    cwd=tmp,
                    env=_lean_subprocess_env(
                        os.pathsep.join([str(control_dir), str(lean_prefix / "lib/lean")])
                    ),
                    capture_output=True,
                    text=True,
                    timeout=timeout,
                    check=False,
                )
                if resolve_proc.returncode != 0:
                    raise RuntimeError(
                        f"TrustedBoundary resolve-imports failed (rc={resolve_proc.returncode}):\n"
                        f"stdout:\n{resolve_proc.stdout}\nstderr:\n{resolve_proc.stderr}"
                    )
                parsed_resolve = json.loads(resolve_res.read_text(encoding="utf-8"))
                if not parsed_resolve.get("ok"):
                    raise RuntimeError(
                        f"TrustedBoundary resolve-imports error: {parsed_resolve}"
                    )
                resolved_graph = parsed_resolve["result"]["graph"]
                prebuild_bundled_oleans.validate_resolved_library_graph(
                    resolved_graph, resolve_roots, foundation_graph
                )
                sysroot_graph.update(resolved_graph)

            for mod, edges in bundled_edges.items():
                for edge in edges:
                    dep = edge["module"]
                    if dep not in bundled_sources and dep not in sysroot_graph:
                        raise RuntimeError(
                            f"bundled module {mod} imports unresolved external module {dep}"
                        )

            sysroot_mods = foundation_mods | set(sysroot_graph.keys())
            sysroot_arts, _ = prebuild_bundled_oleans.collect_sysroot_artifacts(
                lean_prefix / "lib/lean",
                sysroot_mods,
                path_shas,
            )

            # Compute transitive bundled closure needed for `needed_bundled`.
            compile_set: set[str] = set()
            stack = list(needed_bundled)
            while stack:
                mod = stack.pop()
                if mod in compile_set:
                    continue
                compile_set.add(mod)
                for edge in bundled_edges[mod]:
                    dep = edge["module"]
                    if dep in bundled_sources and dep not in compile_set:
                        stack.append(dep)

            full_graph = dict(sysroot_graph)
            full_graph.update(bundled_edges)
            full_arts = dict(sysroot_arts)

            pending = set(compile_set)
            while pending:
                ready = sorted(
                    m
                    for m in pending
                    if all(
                        e["module"] not in pending for e in bundled_edges[m]
                    )
                )
                if not ready:
                    raise RuntimeError(
                        f"dependency cycle across bundled modules: {sorted(pending)}"
                    )
                for mod in ready:
                    pending.remove(mod)
                    edges = bundled_edges[mod]
                    closure = prebuild_bundled_oleans.transitive_closure(
                        full_graph, edges
                    )
                    import_arts = {dep: full_arts[dep] for dep in closure}
                    src_path = bundled_sources[mod]
                    src_bytes = src_path.read_bytes()
                    is_mod = prebuild_bundled_oleans.source_starts_with_module_keyword(
                        src_bytes
                    )
                    setup_path = setup_dir / f"{mod}.setup.json"
                    setup_path.write_text(
                        json.dumps(
                            {
                                "name": mod,
                                "isModule": is_mod,
                                "imports": edges,
                                "importArts": import_arts,
                                "dynlibs": [],
                                "plugins": [],
                                "options": {},
                            }
                        ),
                        encoding="utf-8",
                    )
                    out_olean = out_dir / "lib" / f"{mod.replace('.', '/')}.olean"
                    out_olean.parent.mkdir(parents=True, exist_ok=True)
                    is_theory = mod == "Anneal" or mod.startswith("Anneal.")
                    compile_flags = (
                        THEORY_COMPILE_FLAGS if is_theory else LEAN_BASE_COMPILE_FLAGS
                    )
                    meas = run_measured_subprocess(
                        [
                            str(lean_exec),
                            *compile_flags,
                            "--setup",
                            str(setup_path),
                            "-o",
                            str(out_olean),
                            str(src_path),
                        ],
                        cwd=tmp,
                        env=_lean_subprocess_env(),
                        timeout=timeout,
                        time_bin=time_bin,
                    )
                    if meas.returncode != 0:
                        raise RuntimeError(
                            f"failed compiling {mod} (rc={meas.returncode}):\n"
                            f"stdout:\n{meas.stdout}\nstderr:\n{meas.stderr}"
                        )
                    rss_methods.add(meas.rss_method)

                    rel_stem = f"lib/{mod.replace('.', '/')}"
                    oleans: list[str] = []
                    part_sizes: dict[str, int] = {}
                    for ext in prebuild_bundled_oleans.OLEAN_PARTS:
                        part_file = out_dir / f"{rel_stem}.{ext}"
                        if part_file.is_file():
                            oleans.append(str(part_file))
                            part_sizes[ext] = part_file.stat().st_size
                    if not oleans:
                        raise RuntimeError(f"missing .olean output for {mod}")
                    full_arts[mod] = [oleans, []]

                    if mod in record_set:
                        slug = mod.replace(".", "_").lower()
                        dur = round(meas.elapsed_ms, 3)
                        mod_durations[mod] = dur
                        mod_rss[mod] = meas.maxrss_kib
                        mod_deps[mod] = [
                            e["module"]
                            for e in edges
                            if e["module"] in record_set
                        ]
                        metrics[f"theory_elab.{slug}.cold_j1_ms"] = dur
                        metrics[f"memory_rss.theory_{slug}.cold_j1_maxrss_kib"] = (
                            meas.maxrss_kib
                        )
                        for ext, suffix_key in (
                            ("olean", "olean_bytes"),
                            ("olean.server", "olean_server_bytes"),
                            ("olean.private", "olean_private_bytes"),
                        ):
                            if ext in part_sizes:
                                sz = part_sizes[ext]
                                metrics[
                                    f"artifact_size.module.{slug}.{suffix_key}"
                                ] = sz
                                if ext == "olean":
                                    sum_public += sz
                                elif ext == "olean.server":
                                    sum_server += sz
                                else:
                                    sum_private += sz

    if mod_durations:
        finish: dict[str, float] = {}
        for mod in mod_durations:
            # Topological order guaranteed by `ready` loop; recurse defensively.
            def _finish(name: str) -> float:
                if name in finish:
                    return finish[name]
                dep_max = max((_finish(d) for d in mod_deps.get(name, ())), default=0.0)
                val = mod_durations[name] + dep_max
                finish[name] = val
                return val

            _finish(mod)
        metrics["theory_elab.summary.critical_path_ms"] = round(
            max(finish.values()), 3
        )
        metrics["theory_elab.summary.total_cpu_ms"] = round(
            sum(mod_durations.values()), 3
        )
        metrics["theory_elab.summary.slowest_module_ms"] = round(
            max(mod_durations.values()), 3
        )
        metrics["memory_rss.theory_elab.max_module_maxrss_kib"] = max(mod_rss.values())
        metrics["artifact_size.bundled_olean.public_bytes"] = sum_public
        metrics["artifact_size.bundled_olean.server_bytes"] = sum_server
        metrics["artifact_size.bundled_olean.private_bytes"] = sum_private
        metrics["artifact_size.bundled_olean.total_bytes"] = (
            sum_public + sum_server + sum_private
        )

    return metrics, rss_methods


def collect_binary_and_archive_sizes(
    *,
    tools: dict[str, Path | None],
    omnibus_archive: Path | None,
) -> dict[str, int]:
    """Collect exact `st_size` byte footprints for binaries and archives."""
    metrics: dict[str, int] = {}
    for tool_key, metric_id in (
        ("cli", "artifact_size.bin.cargo_anneal_bytes"),
        ("capture", "artifact_size.bin.anneal_rustc_capture_bytes"),
        ("auditor", "artifact_size.bin.anneal_audit_bytes"),
    ):
        path = tools.get(tool_key)
        if path is not None and path.is_file():
            metrics[metric_id] = path.stat().st_size
    if omnibus_archive is not None:
        resolved = omnibus_archive.resolve(strict=True)
        if resolved.is_file():
            metrics["artifact_size.archive.omnibus_tar_zst_bytes"] = (
                resolved.stat().st_size
            )
    return metrics


def collect_zerocopy_proofs(
    *,
    repo_root: Path,
    tools: dict[str, Path | None],
    timeout: float,
    time_bin: Path | None,
) -> tuple[dict[str, float | int], set[str]]:
    """Verify `zerocopy/proofs/*` against unmodified `zerocopy/src/`."""
    for req in ("cli", "capture", "sysroot", "lean"):
        if tools.get(req) is None:
            raise RuntimeError(
                f"missing `{req}` tool for `zerocopy_proofs` collection"
            )
    units = verify_zerocopy.discover_units(
        repo_root / "zerocopy/proofs",
        repo_root / "zerocopy/src",
        repo_root=repo_root,
    )
    metrics: dict[str, float | int] = {}
    rss_methods: set[str] = set()
    suite_started = time.monotonic()
    verified_count = 0

    with tempfile.TemporaryDirectory(prefix="anneal-perf-zc-") as tmp_str:
        tmp = Path(tmp_str)
        xdg = tmp / "xdg"
        xdg.mkdir(parents=True)
        env = os.environ.copy()
        env["XDG_CACHE_HOME"] = str(xdg)
        for unit_dir, request in units:
            meas, receipt = anneal_ci_lib.run_cargo_anneal_verify(
                cli=tools["cli"],
                request_path=unit_dir / "request.json",
                cwd=unit_dir,
                capture=tools["capture"],
                sysroot=tools["sysroot"],
                lean=tools["lean"],
                artifacts_dir=tmp / unit_dir.name,
                env=env,
                timeout=timeout,
                runner=lambda cmd, cwd, env, timeout: run_measured_subprocess(
                    cmd, cwd=cwd, env=env, timeout=timeout, time_bin=time_bin
                ),
                label=unit_dir.name,
            )
            rss_methods.add(meas.rss_method)
            receipt = verify_zerocopy.validate_unit_receipt(
                unit_dir,
                meas.returncode,
                receipt,
                request,
                capture=tools["capture"],
                sysroot=tools["sysroot"],
                timeout=timeout,
            )
            verified_count += 1
            t = receipt.get("timing_ms", {})
            unit_slug = re.sub(r"[^a-z0-9_-]+", "_", unit_dir.name.lower()).strip("_") or "unit"
            metrics[f"zerocopy_proofs.{unit_slug}.total_ms"] = round(
                float(t.get("total", meas.elapsed_ms)), 3
            )
            metrics[f"zerocopy_proofs.{unit_slug}.capture_ms"] = round(
                float(t.get("capture", 0.0)), 3
            )
            metrics[f"zerocopy_proofs.{unit_slug}.proof_audit_ms"] = round(
                float(t.get("proof_and_audit", 0.0)), 3
            )
            metrics[f"memory_rss.zerocopy_{unit_slug}.maxrss_kib"] = meas.maxrss_kib

    metrics["zerocopy_proofs.suite.total_ms"] = round(
        (time.monotonic() - suite_started) * 1000.0, 3
    )
    metrics["zerocopy_proofs.suite.verified_units_count"] = verified_count
    return metrics, rss_methods


def collect_record(
    *,
    anneal_root: Path,
    repo_root: Path,
    profile: str,
    categories: set[str],
    modules: list[str] | None,
    verify_repeats: int,
    cold_no_cache_repeats: int,
    tools: dict[str, Path | None],
    omnibus_archive: Path | None,
    branch_override: str | None,
    timeout: float,
    time_bin: Path | None,
) -> dict[str, Any]:
    """Collect one complete validated `anneal-perf-record/v1` object."""
    _validate_collect_categories(categories)
    metrics: dict[str, float | int] = {}
    rss_methods: set[str] = set()

    if "verify" in categories:
        v_metrics, v_rss = collect_verify_scalar(
            anneal_root=anneal_root,
            tools=tools,
            verify_repeats=verify_repeats,
            cold_no_cache_repeats=cold_no_cache_repeats,
            timeout=timeout,
            time_bin=time_bin,
        )
        metrics.update(v_metrics)
        rss_methods.update(v_rss)

    if "theory_elab" in categories or (
        "artifact_size" in categories and tools.get("lean") is not None
    ):
        if tools.get("lean") is None:
            raise RuntimeError("missing `--lean` executable for theory_elab")
        t_metrics, t_rss = collect_theory_and_oleans(
            anneal_root=anneal_root,
            lean_bin=tools["lean"],
            selected_modules=modules,
            timeout=timeout,
            time_bin=time_bin,
        )
        for k, v in t_metrics.items():
            cat = k.split(".", 1)[0]
            if cat in categories:
                metrics[k] = v
        if "theory_elab" in categories or "memory_rss" in categories:
            rss_methods.update(t_rss)

    if "artifact_size" in categories:
        metrics.update(
            collect_binary_and_archive_sizes(
                tools=tools, omnibus_archive=omnibus_archive
            )
        )

    if "zerocopy_proofs" in categories:
        z_metrics, z_rss = collect_zerocopy_proofs(
            repo_root=repo_root,
            tools=tools,
            timeout=timeout,
            time_bin=time_bin,
        )
        for k, v in z_metrics.items():
            cat = k.split(".", 1)[0]
            if cat in categories:
                metrics[k] = v
        rss_methods.update(z_rss)

    if not metrics:
        raise RuntimeError("collected zero metrics")

    lean_ver = "unknown"
    if tools.get("lean") is not None:
        raw_lean = _read_tool_version([str(tools["lean"]), "--version"], "unknown")
        m = re.search(r"version\s+([0-9]+\.[0-9]+\.[0-9]+[^\s,]*)", raw_lean)
        lean_ver = m.group(1) if m else raw_lean

    rustc_ver = "unknown"
    if tools.get("sysroot") is not None:
        rustc_bin = tools["sysroot"] / "bin/rustc"
        if rustc_bin.is_file():
            rustc_ver = _read_tool_version([str(rustc_bin), "--version"], "unknown")
    if rustc_ver == "unknown":
        rustc_ver = _read_tool_version(
            ["rustup", "run", "nightly-2026-05-31", "rustc", "--version"], "unknown"
        )

    rss_method = "fallback_wait4" if "fallback_wait4" in rss_methods else "usr_bin_time"
    record = {
        "schema": RECORD_SCHEMA,
        "commit": _read_git_commit_metadata(repo_root, branch_override),
        "environment": {
            "profile": profile,
            "os": platform.system() or "Linux",
            "arch": platform.machine() or "x86_64",
            "cpu_model": _read_linux_cpu_model(),
            "vcpu_count": max(1, os.cpu_count() or 1),
            "ram_total_kib": _read_linux_ram_kib(),
            "lean_version": lean_ver,
            "rustc_version": rustc_ver,
        },
        "sampling": {
            "verify_repeats": verify_repeats,
            "aggregation": "median",
            "rss_method": rss_method,
        },
        "metrics": dict(sorted(metrics.items())),
    }
    return validate_record(record)


def _rule_matches_metric(rule: dict[str, Any], metric_id: str) -> bool:
    if "metric" in rule:
        return metric_id == rule["metric"]
    return fnmatch.fnmatchcase(metric_id, rule["pattern"])


def budget_bounds_for_metric(
    budgets_cfg: dict[str, Any], metric_id: str
) -> tuple[float | None, float | None]:
    """Return tightest `(budget_min, budget_max)` matching `metric_id`."""
    min_val: float | None = None
    max_val: float | None = None
    for rule in budgets_cfg.get("budgets", ()):
        if not _rule_matches_metric(rule, metric_id):
            continue
        if "max_value" in rule:
            v = float(rule["max_value"])
            max_val = v if max_val is None else min(max_val, v)
        if "min_value" in rule:
            v = float(rule["min_value"])
            min_val = v if min_val is None else max(min_val, v)
    return min_val, max_val


def evaluate_budgets(
    record: dict[str, Any], budgets_cfg: dict[str, Any]
) -> list[dict[str, Any]]:
    """Evaluate Tier A `max_value` and `min_value` rules against one record."""
    validate_record(record)
    violations: list[dict[str, Any]] = []
    for metric_id, raw_val in sorted(record["metrics"].items()):
        val = float(raw_val)
        min_val, max_val = budget_bounds_for_metric(budgets_cfg, metric_id)
        if max_val is not None and val > max_val:
            violations.append(
                {
                    "metric": metric_id,
                    "kind": "max_value",
                    "value": val,
                    "limit": max_val,
                }
            )
        if min_val is not None and val < min_val:
            violations.append(
                {
                    "metric": metric_id,
                    "kind": "min_value",
                    "value": val,
                    "limit": min_val,
                }
            )
    return violations


def append_record(records_path: Path, record: dict[str, Any]) -> list[dict[str, Any]]:
    """Idempotently upsert `(commit.sha, environment.profile)` in `records.jsonl`."""
    validate_record(record)
    ensure_not_symlink(records_path, "records file")
    existing = load_records_jsonl(records_path)
    key = (record["commit"]["sha"], record["environment"]["profile"])

    updated: list[dict[str, Any]] = []
    replaced = False
    for item in existing:
        item_key = (item["commit"]["sha"], item["environment"]["profile"])
        if item_key == key:
            if not replaced:
                updated.append(record)
                replaced = True
        else:
            updated.append(item)
    if not replaced:
        updated.append(record)

    updated.sort(key=lambda r: (r["commit"]["unix_ts"], r["commit"]["sha"]))
    lines = "".join(
        json.dumps(r, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n"
        for r in updated
    )
    _atomic_write_text(records_path, lines)
    return updated


def compute_geomean_ratio(
    baseline: dict[str, float | int],
    current: dict[str, float | int],
    metric_ids: list[str] | None = None,
) -> float | None:
    """Compute inversion-symmetric `exp(mean(ln(current[m] / baseline[m])))`."""
    keys = sorted(metric_ids) if metric_ids is not None else sorted(
        set(baseline.keys()) & set(current.keys())
    )
    log_ratios: list[float] = []
    for k in keys:
        if k not in baseline or k not in current:
            continue
        a = float(baseline[k])
        b = float(current[k])
        if a > 0.0 and b > 0.0 and math.isfinite(a) and math.isfinite(b):
            log_ratios.append(math.log(b / a))
    if not log_ratios:
        return None
    return round(math.exp(sum(log_ratios) / len(log_ratios)), 6)


def analyze_history(
    records: list[dict[str, Any]],
    budgets_cfg: dict[str, Any] | None = None,
    *,
    profile: str | None = None,
) -> dict[str, Any]:
    """Run Tier A + Tier B rolling `Median/MAD` analysis on `records`."""
    if not records:
        return {
            "profile": profile or "",
            "commits": [],
            "anomalies": [],
            "latest_anomalies": [],
            "category_geomean_vs_prev": {},
            "category_geomean_vs_baseline": {},
            "latest_budget_violations": [],
        }

    rolling = dict(DEFAULT_ROLLING_POLICY)
    if budgets_cfg is not None:
        rolling.update(budgets_cfg.get("rolling", {}))

    target_profile = profile or records[-1]["environment"]["profile"]
    filtered = [
        r for r in records if r["environment"]["profile"] == target_profile
    ]
    if not filtered:
        return {
            "profile": target_profile,
            "commits": [],
            "anomalies": [],
            "latest_anomalies": [],
            "category_geomean_vs_prev": {},
            "category_geomean_vs_baseline": {},
            "latest_budget_violations": [],
        }

    window = int(rolling["window"])
    min_history = int(rolling["min_history"])
    confirmed_z = float(rolling["confirmed_z"])
    spike_z = float(rolling["spike_z"])
    min_rel_delta = float(rolling["min_rel_delta"])
    spike_min_rel_delta = float(rolling.get("spike_min_rel_delta", 0.10))
    severe_z = float(rolling["severe_z"])
    severe_rel_delta = float(rolling["severe_rel_delta"])
    mad_floor_rel = float(rolling["mad_floor_rel"])
    det_rel_delta = float(rolling["deterministic_rel_delta"])
    det_min_bytes = int(rolling["deterministic_min_bytes"])

    commits_meta: list[dict[str, Any]] = []
    for idx, rec in enumerate(filtered):
        cpu_model = rec["environment"]["cpu_model"]
        prev_cpu = filtered[idx - 1]["environment"]["cpu_model"] if idx > 0 else cpu_model
        commits_meta.append(
            {
                "sha": rec["commit"]["sha"],
                "short": rec["commit"]["short_sha"],
                "ts": rec["commit"]["unix_ts"],
                "timestamp": rec["commit"]["timestamp"],
                "subject": rec["commit"]["subject"],
                "cpu_model": cpu_model,
                "hw_changed": idx > 0 and cpu_model != prev_cpu,
            }
        )

    all_metric_ids = sorted(
        {m for rec in filtered for m in rec["metrics"].keys()}
    )
    descriptors = {m: describe_metric(m) for m in all_metric_ids}
    anomalies: list[dict[str, Any]] = []

    for idx, meta in enumerate(commits_meta):
        if meta["hw_changed"]:
            prev_cpu = commits_meta[idx - 1]["cpu_model"]
            anomalies.append(
                {
                    "commit_index": idx,
                    "sha": meta["sha"],
                    "short_sha": meta["short"],
                    "metric": "environment.cpu_model",
                    "kind": "hardware_shift",
                    "severity": "info",
                    "detail": f"{prev_cpu} -> {meta['cpu_model']}",
                }
            )

    for metric_id in all_metric_ids:
        desc = descriptors[metric_id]
        if desc["direction"] != "lower_is_better":
            continue
        series = [rec["metrics"].get(metric_id) for rec in filtered]

        if desc["deterministic"]:
            prev_val: float | None = None
            for idx, raw_val in enumerate(series):
                if raw_val is None:
                    continue
                val = float(raw_val)
                if prev_val is not None:
                    abs_delta = val - prev_val
                    rel_delta = abs_delta / max(prev_val, 1.0)
                    min_abs = det_min_bytes if desc["unit"] == "B" else 0
                    if rel_delta > det_rel_delta and abs_delta >= min_abs:
                        anomalies.append(
                            {
                                "commit_index": idx,
                                "sha": commits_meta[idx]["sha"],
                                "short_sha": commits_meta[idx]["short"],
                                "metric": metric_id,
                                "kind": "deterministic_growth",
                                "severity": "warning",
                                "value": val,
                                "baseline": prev_val,
                                "rel_delta": round(rel_delta, 4),
                            }
                        )
                prev_val = val
            continue

        segment_start = 0
        prev_z: float | None = None
        for idx, raw_val in enumerate(series):
            hw_changed = commits_meta[idx]["hw_changed"]
            if hw_changed:
                # Reset rolling baseline window across CPU SKU transitions so
                # subsequent commits are evaluated only against same-SKU runs.
                segment_start = idx
                prev_z = None
            if raw_val is None:
                prev_z = None
                continue
            val = float(raw_val)
            history = [
                float(x)
                for x in series[max(segment_start, idx - window) : idx]
                if x is not None
            ]
            if len(history) < min_history:
                prev_z = None
                continue
            med = float(statistics.median(history))
            mad = float(statistics.median(abs(y - med) for y in history))
            if med == 0.0:
                if val == 0.0:
                    prev_z = 0.0
                    continue
                sigma = max(1.4826 * mad, 1.0)
                z = (val - med) / sigma
                rel_delta = 1.0
            else:
                sigma = max(1.4826 * mad, mad_floor_rel * med, 1.0e-9)
                z = (val - med) / sigma
                rel_delta = (val - med) / med

            if not hw_changed and (
                (
                    prev_z is not None
                    and z > confirmed_z
                    and prev_z > confirmed_z
                    and rel_delta > min_rel_delta
                )
                or (z > severe_z and rel_delta > severe_rel_delta)
            ):
                anomalies.append(
                    {
                        "commit_index": idx,
                        "sha": commits_meta[idx]["sha"],
                        "short_sha": commits_meta[idx]["short"],
                        "metric": metric_id,
                        "kind": "confirmed_regression",
                        "severity": "error",
                        "value": val,
                        "baseline": round(med, 3),
                        "sigma": round(sigma, 3),
                        "z_score": round(z, 3),
                        "rel_delta": round(rel_delta, 4),
                    }
                )
            elif not hw_changed and z > spike_z and rel_delta > spike_min_rel_delta:
                anomalies.append(
                    {
                        "commit_index": idx,
                        "sha": commits_meta[idx]["sha"],
                        "short_sha": commits_meta[idx]["short"],
                        "metric": metric_id,
                        "kind": "candidate_spike",
                        "severity": "info",
                        "value": val,
                        "baseline": round(med, 3),
                        "sigma": round(sigma, 3),
                        "z_score": round(z, 3),
                        "rel_delta": round(rel_delta, 4),
                    }
                )
            prev_z = z

    latest_rec = filtered[-1]
    latest_budgets = (
        evaluate_budgets(latest_rec, budgets_cfg) if budgets_cfg is not None else []
    )
    for b in latest_budgets:
        anomalies.append(
            {
                "commit_index": len(filtered) - 1,
                "sha": latest_rec["commit"]["sha"],
                "short_sha": latest_rec["commit"]["short_sha"],
                "metric": b["metric"],
                "kind": "budget_breach",
                "severity": "error",
                "value": b["value"],
                "limit": b["limit"],
                "bound": b["kind"],
            }
        )

    latest_idx = len(filtered) - 1
    latest_anomalies = [a for a in anomalies if a["commit_index"] == latest_idx]

    # Category GeoMean summaries against previous commit and rolling baseline.
    prev_metrics = filtered[-2]["metrics"] if len(filtered) >= 2 else {}
    last_hw_idx = max(
        (i for i, meta in enumerate(commits_meta) if meta["hw_changed"]),
        default=0,
    )
    rolling_baselines: dict[str, float] = {}
    for metric_id in latest_rec["metrics"]:
        hist = [
            float(r["metrics"][metric_id])
            for r in filtered[max(last_hw_idx, latest_idx - window) : latest_idx]
            if metric_id in r["metrics"]
        ]
        if hist:
            rolling_baselines[metric_id] = float(statistics.median(hist))

    cat_prev: dict[str, float] = {}
    cat_base: dict[str, float] = {}
    for cat in CATEGORIES:
        cat_ids = [
            m
            for m in latest_rec["metrics"]
            if descriptors[m]["category"] == cat
            and descriptors[m]["direction"] == "lower_is_better"
        ]
        if prev_metrics:
            r_prev = compute_geomean_ratio(prev_metrics, latest_rec["metrics"], cat_ids)
            if r_prev is not None:
                cat_prev[cat] = r_prev
        if rolling_baselines:
            r_base = compute_geomean_ratio(
                rolling_baselines, latest_rec["metrics"], cat_ids
            )
            if r_base is not None:
                cat_base[cat] = r_base

    return {
        "profile": target_profile,
        "commits": commits_meta,
        "anomalies": anomalies,
        "latest_anomalies": latest_anomalies,
        "category_geomean_vs_prev": cat_prev,
        "category_geomean_vs_baseline": cat_base,
        "latest_budget_violations": latest_budgets,
    }


def render_summary_markdown(
    records: list[dict[str, Any]],
    budgets_cfg: dict[str, Any] | None = None,
    *,
    profile: str | None = None,
) -> str:
    """Render concise Markdown summary for `$GITHUB_STEP_SUMMARY`."""
    if not records:
        return "## Anneal Performance Summary\n\nNo telemetry records found.\n"
    analysis = analyze_history(records, budgets_cfg, profile=profile)
    target_profile = analysis["profile"]
    filtered = [r for r in records if r["environment"]["profile"] == target_profile]
    latest = filtered[-1]
    c = latest["commit"]
    lines = [
        "## Anneal Performance Tracking Summary",
        "",
        f"- **Commit:** `{c['short_sha']}` — {c['subject']}",
        f"- **Profile:** `{target_profile}` (`{latest['environment']['cpu_model']}`)",
        f"- **History Depth:** `{len(filtered)}` commit(s)",
        "",
    ]

    geomeans = analysis["category_geomean_vs_baseline"]
    if geomeans:
        lines.extend(
            [
                "### Category Geometric Mean vs. Rolling Baseline",
                "",
                "| Category | Ratio | Delta |",
                "| :--- | ---: | ---: |",
            ]
        )
        for cat in CATEGORIES:
            if cat in geomeans:
                ratio = geomeans[cat]
                pct = (ratio - 1.0) * 100.0
                lines.append(f"| `{cat}` | `{ratio:.4f}x` | `{pct:+.2f}%` |")
        lines.append("")

    key_metrics = [
        "verify.scalar.cold_no_cache_total_ms",
        "verify.scalar.cold_prebuilt_total_ms",
        "verify.scalar.warm_disk_total_ms",
        "theory_elab.summary.critical_path_ms",
        "theory_elab.summary.slowest_module_ms",
        "memory_rss.theory_elab.max_module_maxrss_kib",
        "artifact_size.bundled_olean.total_bytes",
        "artifact_size.bin.cargo_anneal_bytes",
        "zerocopy_proofs.suite.total_ms",
        "zerocopy_proofs.suite.verified_units_count",
    ]
    present_keys = [k for k in key_metrics if k in latest["metrics"]]
    if present_keys:
        lines.extend(
            [
                "### Key Measurements",
                "",
                "| Metric | Value | Unit |",
                "| :--- | ---: | :--- |",
            ]
        )
        for k in present_keys:
            desc = describe_metric(k)
            val = latest["metrics"][k]
            fmt_val = f"{val:,.1f}" if isinstance(val, float) else f"{val:,}"
            lines.append(f"| `{k}` | `{fmt_val}` | `{desc['unit']}` |")
        lines.append("")

    latest_anomalies = analysis["latest_anomalies"]
    if latest_anomalies:
        lines.extend(["### Latest Commit Alerts", ""])
        for anom in latest_anomalies:
            lines.append(
                f"- **{anom['kind']}** (`{anom['severity']}`) on `{anom['metric']}`: "
                f"value={anom.get('value', anom.get('detail'))}"
            )
        lines.append("")
    else:
        lines.append("No regressions or budget breaches detected on latest commit.\n")

    return "\n".join(lines) + "\n"


def _validate_collect_categories(categories: set[str]) -> None:
    if not categories:
        raise ValidationError("empty category selection")
    unknown = categories - ALLOWED_CATEGORIES
    if unknown:
        raise ValidationError(f"unknown categories: {sorted(unknown)}")
    non_collectable = categories - ALLOWED_COLLECTABLE_CATEGORIES
    if non_collectable:
        raise ValidationError(
            "non-collectable categories for `collect`: "
            f"{sorted(non_collectable)} (`differential_oracle` metrics are "
            "emitted by `ci/check_mir_differential.py`, not "
            "`perf_tracking.py collect`)"
        )


def _parse_categories(raw: str | None) -> set[str]:
    if not raw:
        return set(COLLECTABLE_CATEGORIES)
    chosen = {part.strip() for part in raw.split(",") if part.strip()}
    _validate_collect_categories(chosen)
    return chosen


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    p_collect = sub.add_parser("collect", help="Collect Anneal performance telemetry")
    p_collect.add_argument(
        "--anneal-root",
        type=Path,
        default=anneal_ci_lib.default_anneal_root(__file__),
    )
    p_collect.add_argument("--repo-root", type=Path)
    p_collect.add_argument("--output", type=Path)
    p_collect.add_argument(
        "--profile",
        default=f"{platform.system().lower()}-{platform.machine().lower()}",
    )
    p_collect.add_argument("--categories", help="Comma-separated category subset")
    p_collect.add_argument("--modules", help="Comma-separated Lean module subset")
    p_collect.add_argument("--verify-repeats", type=int, default=3)
    p_collect.add_argument("--cold-no-cache-repeats", type=int, default=1)
    p_collect.add_argument("--cli", type=Path)
    p_collect.add_argument("--capture", type=Path)
    p_collect.add_argument("--sysroot", type=Path)
    p_collect.add_argument("--lean", type=Path)
    p_collect.add_argument("--auditor", type=Path)
    p_collect.add_argument("--install-root", type=Path)
    p_collect.add_argument("--target-dir", type=Path)
    p_collect.add_argument("--omnibus-archive", type=Path)
    p_collect.add_argument("--branch")
    p_collect.add_argument("--timeout", type=float, default=600.0)
    p_collect.add_argument("--time-bin", type=Path, default=DEFAULT_TIME_BIN)

    p_val = sub.add_parser("validate", help="Validate record JSON or JSONL")
    p_val.add_argument("input", type=Path)
    p_val.add_argument("--jsonl", action="store_true")

    p_bud = sub.add_parser("check-budgets", help="Evaluate Tier A budget ceilings")
    p_bud.add_argument("record", type=Path)
    p_bud.add_argument(
        "--budgets",
        type=Path,
        default=DEFAULT_BUDGETS_PATH,
    )
    p_bud.add_argument("--json-out", type=Path)

    p_app = sub.add_parser("append", help="Idempotently append record to JSONL")
    p_app.add_argument("records_jsonl", type=Path)
    p_app.add_argument("record", type=Path)

    p_ana = sub.add_parser("analyze", help="Run Tier A/B regression analysis")
    p_ana.add_argument("records_jsonl", type=Path)
    p_ana.add_argument("--budgets", type=Path, default=None)
    p_ana.add_argument("--profile")
    p_ana.add_argument("--json-out", type=Path)
    p_ana.add_argument("--fail-on-regression", action="store_true")

    p_sum = sub.add_parser("summary-markdown", help="Emit Markdown summary")
    p_sum.add_argument("records_jsonl", type=Path)
    p_sum.add_argument("--budgets", type=Path, default=None)
    p_sum.add_argument("--profile")
    p_sum.add_argument("--output", type=Path)

    args = parser.parse_args(argv)

    if args.command == "collect":
        categories = _parse_categories(args.categories)
        anneal_root = args.anneal_root.resolve(strict=True)
        repo_root = (args.repo_root or anneal_root.parent).resolve(strict=True)
        modules = (
            [m.strip() for m in args.modules.split(",") if m.strip()]
            if args.modules
            else None
        )
        tools = _discover_tools(
            anneal_root,
            cli=args.cli,
            capture=args.capture,
            sysroot=args.sysroot,
            lean=args.lean,
            auditor=args.auditor,
            install_root=args.install_root,
            target_dir=args.target_dir,
        )
        record = collect_record(
            anneal_root=anneal_root,
            repo_root=repo_root,
            profile=args.profile,
            categories=categories,
            modules=modules,
            verify_repeats=max(1, args.verify_repeats),
            cold_no_cache_repeats=max(1, args.cold_no_cache_repeats),
            tools=tools,
            omnibus_archive=args.omnibus_archive,
            branch_override=args.branch,
            timeout=args.timeout,
            time_bin=args.time_bin,
        )
        payload = json.dumps(record, indent=2, sort_keys=True) + "\n"
        if args.output:
            _atomic_write_text(args.output, payload)
        else:
            sys.stdout.write(payload)
        return 0

    if args.command == "validate":
        if args.jsonl:
            recs = load_records_jsonl(args.input)
            print(f"Validated {len(recs)} record(s) in {args.input}")
        else:
            load_record(args.input)
            print(f"Validated record {args.input}")
        return 0

    if args.command == "check-budgets":
        rec = load_record(args.record)
        cfg = load_budgets(args.budgets)
        violations = evaluate_budgets(rec, cfg)
        if args.json_out:
            _atomic_write_text(
                args.json_out,
                json.dumps({"violations": violations}, indent=2) + "\n",
            )
        if violations:
            for v in violations:
                print(
                    f"BUDGET VIOLATION {v['metric']}: value={v['value']} "
                    f"({v['kind']}={v['limit']})",
                    file=sys.stderr,
                )
            return 1
        print(f"All {len(rec['metrics'])} metrics within Tier A budgets.")
        return 0

    if args.command == "append":
        rec = load_record(args.record)
        updated = append_record(args.records_jsonl, rec)
        print(f"Stored {len(updated)} total record(s) in {args.records_jsonl}")
        return 0

    if args.command == "analyze":
        recs = load_records_jsonl(args.records_jsonl)
        cfg = resolve_budgets_cfg(args.budgets)
        report = analyze_history(recs, cfg, profile=args.profile)
        payload = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.json_out:
            _atomic_write_text(args.json_out, payload)
        else:
            sys.stdout.write(payload)
        if args.fail_on_regression:
            blocking = [
                a
                for a in report["latest_anomalies"]
                if a["kind"] in ("confirmed_regression", "budget_breach")
            ]
            if blocking:
                return 1
        return 0

    if args.command == "summary-markdown":
        recs = load_records_jsonl(args.records_jsonl)
        cfg = resolve_budgets_cfg(args.budgets)
        md = render_summary_markdown(recs, cfg, profile=args.profile)
        if args.output:
            _atomic_write_text(args.output, md)
        else:
            sys.stdout.write(md)
        return 0

    return 2


if __name__ == "__main__":
    raise SystemExit(main())
