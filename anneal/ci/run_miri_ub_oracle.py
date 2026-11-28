#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Fail-closed 2-tier Miri UB soundness oracle harness for Anneal.

Tier A fetches a SHA-256-pinned upstream `rust-lang/miri` archive matched to
Anneal's pinned `rustc` toolchain commit, safely extracts `tests/fail*/*.rs`,
verifies the canonical corpus manifest digest, and runs `anneal-rustc-capture`
(`--scope crate`) + `anneal-mir-eval` over every expanded unit. It fails closed
if ANY UB test is accepted (`unsound_accept > 0`), if any tool error occurs
(`tool_error > 0`), or if caught UB coverage regresses below the pinned ratchet
(`caught_ub < min_caught_ub`).

Tier B runs curated in-repo minimal UB regression fixtures and valid control
fixtures under `anneal/tests/corpora/miri_ub/`, asserting 100% UB detection on
required `caught_ub` fixtures, zero unsound accepts on fail-closed UB fixtures,
and 100% acceptance on valid controls so the harness cannot pass trivially.

Scope note: this oracle executes the zero-TCB Rust mirror (`anneal-mir-eval`),
not Lean `Trusted.MirSemantics`; a green run checks `anneal-rustc-capture` plus
`anneal-mir-eval` and does not itself verify Lean-vs-mirror correspondence.
"""

from __future__ import annotations

import argparse
import ctypes
import json
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys
import threading
import time
import urllib.parse
import urllib.request

sys.dont_write_bytecode = True
_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

# The implementation lives in `miri_ub_oracle_lib/`. Every name it defines
# is re-exported here, so callers and tests that use this module keep
# working. A test that patches a name must patch it in the module whose
# code reads it.
from miri_ub_oracle_lib.common import (  # noqa: E402, F401
    ALLOWED_API_HOSTS, ALLOWED_ARCHIVE_HOSTS, ALLOWED_ARCHIVE_URL_PREFIX, ALLOWED_PROFILES,
    ALLOWED_TIER_B_KINDS, ANNEAL_DIR, BUCKETS, CAPTURE_MAX_DISK_BYTES, CAPTURE_MAX_DISK_MB,
    CAPTURE_MAX_EXPORT_BYTES, CAPTURE_MAX_INODES, CAPTURE_MAX_NOFILE, CAPTURE_MAX_PROCS,
    CAPTURE_MAX_TASKS, CHILD_READ_CHUNK_BYTES, CI_DIR, DEFAULT_MAX_MEMORY_MB,
    DEFAULT_MAX_TOTAL_MEMORY_MB, DEFAULT_MAX_WORKERS, DEFAULT_PIN_PATH, DEFAULT_TIER_B_DIR,
    DOWNLOAD_CHUNK_BYTES, EVAL_MAX_NOFILE, HEX40_RE, HEX64_RE, MAX_ARCHIVE_BYTES,
    MAX_CHILD_OUTPUT_BYTES, MAX_CORPUS_DIR_DEPTH, MAX_CORPUS_DIR_ENTRIES,
    MAX_DECOMPRESSED_TAR_BYTES, MAX_PIN_BYTES, MAX_SINGLE_FILE_BYTES, MAX_SUBPROCESS_FSIZE_BYTES,
    MAX_TAR_MEMBERS, MAX_TIER_B_DIR_ENTRIES, MAX_TOTAL_EXTRACTED_BYTES, MIRI_HEADER_RE, OracleError,
    PIN_SCHEMA_VERSION, REPORT_SCHEMA_VERSION, REPO_ROOT, STRIPPED_CI_ENV_PREFIXES,
    STRIPPED_CI_ENV_VARS, TIER_B_SCHEMA_VERSION, _read_regular_file_bytes, _validate_hex,
    _validate_positive_int,
)
from miri_ub_oracle_lib.linux_abi import (  # noqa: E402, F401
    CONFINEMENT_MODES, _AARCH64_SECCOMP_SPEC, _BPF_JMP_JEQ_K, _BPF_JMP_JSET_K, _BPF_LD_W_ABS,
    _BPF_RET_K, _CLONE_FORBIDDEN_NS_FLAGS, _CLONE_NEWNET, _CLONE_NEWNS, _CLONE_NEWPID,
    _CLONE_NEWUSER, _CONFINED_EXEC_FLAG, _FCNTL_F_SETFL, _FCNTL_O_ASYNC, _FCNTL_SAFE_CMDS,
    _IOCTL_CAPTURE_ALLOWED, _IOCTL_FIOCLEX, _LANDLOCK_ACCESS_FS_ABI1_ALL,
    _LANDLOCK_ACCESS_FS_EXECUTE, _LANDLOCK_ACCESS_FS_IOCTL_DEV, _LANDLOCK_ACCESS_FS_MAKE_DIR,
    _LANDLOCK_ACCESS_FS_MAKE_REG, _LANDLOCK_ACCESS_FS_READ_DIR, _LANDLOCK_ACCESS_FS_READ_FILE,
    _LANDLOCK_ACCESS_FS_REFER, _LANDLOCK_ACCESS_FS_REMOVE_DIR, _LANDLOCK_ACCESS_FS_REMOVE_FILE,
    _LANDLOCK_ACCESS_FS_TRUNCATE, _LANDLOCK_ACCESS_FS_WRITE_FILE, _LANDLOCK_CREATE_RULESET_VERSION,
    _LANDLOCK_DIR_RO, _LANDLOCK_DIR_RO_EXEC, _LANDLOCK_DIR_RW_BASE, _LANDLOCK_FILE_RO,
    _LANDLOCK_FILE_RO_EXEC, _LANDLOCK_FILE_RW_BASE, _LANDLOCK_RULE_PATH_BENEATH,
    _LANDLOCK_SYSTEM_RO_EXEC_DIRS, _LANDLOCK_SYSTEM_RO_PATHS, _MNT_DETACH, _MS_BIND, _MS_NOATIME,
    _MS_NODEV, _MS_NODIRATIME, _MS_NOEXEC, _MS_NOSUID, _MS_PRIVATE, _MS_RDONLY, _MS_REC,
    _MS_RELATIME, _MS_REMOUNT, _OPEN_WRITE_FLAGS, _PRCTL_CAPTURE_ALLOWED, _PR_GET_DUMPABLE,
    _PR_SET_DUMPABLE, _PR_SET_NO_NEW_PRIVS, _PR_SET_SECCOMP, _SECCOMP_ARCH_TABLE,
    _SECCOMP_MODE_FILTER, _SECCOMP_RET_ALLOW, _SECCOMP_RET_ERRNO, _SECCOMP_RET_KILL_PROCESS,
    _ST_TO_MS_FLAGS, _SYS_LANDLOCK_ADD_RULE, _SYS_LANDLOCK_CREATE_RULESET,
    _SYS_LANDLOCK_RESTRICT_SELF, _X32_SYSCALL_BIT, _X86_64_SECCOMP_SPEC,
)
from miri_ub_oracle_lib.pins import (  # noqa: E402, F401
    _PinnedHttpsRedirectHandler, _fetch_pinned_github_json, _resolve_github_subtree_sha,
    _validate_https_host, load_pin, load_tier_b_manifest,
)
from miri_ub_oracle_lib.archive import (  # noqa: E402, F401
    _BoundedReadStream, _compute_git_tree_sha1, _expected_archive_tree_shas,
    _validate_tar_member_path, copy_and_verify_archive_sha256, download_verified_archive,
    safe_extract_miri_corpus, verify_rustc_miri_linkage,
)
from miri_ub_oracle_lib.corpus import (  # noqa: E402, F401
    _CAPTURE_FIXED_RUSTC_FLAGS, _stream_regular_file_sha256, _target_bitwidth, _walk_corpus_tree,
    compute_corpus_manifest_sha256, harness_skip_reason, parse_compile_flags, parse_miri_headers,
    verify_corpus_manifest,
)
from miri_ub_oracle_lib.seccomp import (  # noqa: E402, F401
    _SockFprog, _build_confinement_seccomp_bpf, _install_confinement_seccomp,
)
from miri_ub_oracle_lib.capture import (  # noqa: E402, F401
    _assert_capture_non_root_uid, _drop_all_capabilities, _enter_capture_namespaces,
    _export_capture_file, _harden_parent_process,
)
from miri_ub_oracle_lib.landlock import (  # noqa: E402, F401
    _collect_landlock_read_paths, _elf_pt_interp, _install_eval_landlock, _install_landlock,
    _is_script_or_python, _probe_landlock_abi, _require_confinement_support, _shebang_interpreter,
)
from miri_ub_oracle_lib.confined_exec import (  # noqa: E402, F401
    _apply_rlimit, _run_confined_exec, _wrap_with_confinement,
)
from miri_ub_oracle_lib.bounded import (  # noqa: E402, F401
    _CancelToken, _count_pgid_processes, _kill_process_group, _sanitize_detail,
    classify_eval_result, run_bounded, sanitized_child_env,
)
from miri_ub_oracle_lib.evaluate import (  # noqa: E402, F401
    _profile_eval_args, _sanitize_crate_name, evaluate_mir_json_unit, evaluate_rust_unit,
)
from miri_ub_oracle_lib.gates import (  # noqa: E402, F401
    _count_buckets, evaluate_tier_a_gate, evaluate_tier_b_gate,
)
from miri_ub_oracle_lib.tiers import (  # noqa: E402, F401
    _resolve_worker_memory_budget, run_tier_a, run_tier_b,
)


def resolve_sysroot(explicit: Path | None, channel: str) -> Path:
    """Resolve the pinned Rust sysroot fail-closed."""
    if explicit is not None:
        if not explicit.is_dir():
            raise OracleError(f"--sysroot directory does not exist: {explicit}")
        return explicit.resolve()
    env_sysroot = os.environ.get("ANNEAL_SYSROOT")
    if env_sysroot:
        p = Path(env_sysroot)
        if not p.is_dir():
            raise OracleError(f"ANNEAL_SYSROOT does not exist: {p}")
        return p.resolve()
    install_root = os.environ.get("ANNEAL_TEST_INSTALL_ROOT")
    if install_root:
        p = Path(install_root) / "rust"
        if not p.is_dir():
            raise OracleError(
                f"ANNEAL_TEST_INSTALL_ROOT rust sysroot does not exist: {p}"
            )
        return p.resolve()
    try:
        out = subprocess.check_output(
            ["rustup", "run", channel, "rustc", "--print", "sysroot"],
            env=sanitized_child_env(),
            text=True,
            timeout=15,
        ).strip()
    except (OSError, subprocess.SubprocessError) as exc:
        raise OracleError(
            f"failed to resolve sysroot for '{channel}' (pass --sysroot): {exc}"
        ) from exc
    p = Path(out)
    if not p.is_dir():
        raise OracleError(f"resolved sysroot does not exist: {p}")
    return p.resolve()


def render_summary_markdown(
    report: dict[str, object], *, elapsed_secs: float | None = None
) -> str:
    """Render a compact Markdown step summary for CI."""
    tier = str(report["tier"]).upper().replace("_", " ")
    status = "PASS" if report["passed"] else "FAIL"
    counts = report["counts"]
    lines = [
        f"## Anneal Miri UB Oracle ({tier}): {status}",
        "",
        f"- **Profile:** `{report['profile']}`",
    ]
    if elapsed_secs is not None:
        lines.append(f"- **Elapsed:** `{elapsed_secs}s`")
    if report["tier"] == "tier_a":
        pin = report["pin"]
        lines.extend([
            f"- **Upstream pin:** `{pin['upstream_repo']}@{pin['miri_commit'][:12]}` "
            f"(rustc `{pin['rustc_commit'][:12]}`)",
            f"- **Corpus files / units:** `{report['total_files']}` / `{report['total_units']}`",
            f"- **Ratchet:** `caught_ub={counts['caught_ub']}` >= "
            f"`min_caught_ub={pin['min_caught_ub']}`, "
            f"`unsound_accept={counts['unsound_accept']}` (must be `0`), "
            f"`tool_error={counts['tool_error']}` (must be `0`)",
        ])
    else:
        lines.extend([
            f"- **Fixtures:** `{report['total_fixtures']}`",
            f"- **Counts:** `caught_ub={counts['caught_ub']}`, "
            f"`accepted_valid={counts['accepted_valid']}`, "
            f"`capture_refused={counts['capture_refused']}`, "
            f"`unsound_accept={counts['unsound_accept']}`, "
            f"`tool_error={counts['tool_error']}`",
        ])

    lines.extend(["", "| Bucket | Count |", "| --- | ---: |"])
    for key, val in counts.items():  # type: ignore[union-attr]
        lines.append(f"| `{key}` | `{val}` |")

    failures = report.get("failures") or []
    if failures:
        lines.extend(["", "### Failures", ""])
        for msg in failures:  # type: ignore[union-attr]
            lines.append(f"- {msg}")
    lines.append("")
    return "\n".join(lines)


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run Anneal 2-tier Miri UB soundness oracle checks."
    )
    tier_group = parser.add_mutually_exclusive_group(required=True)
    tier_group.add_argument(
        "--tier-a",
        action="store_true",
        help="Run Tier A against the SHA-256-pinned upstream rust-lang/miri suite.",
    )
    tier_group.add_argument(
        "--tier-b",
        action="store_true",
        help="Run Tier B against curated in-repo minimal UB + valid control fixtures.",
    )
    parser.add_argument(
        "--pin",
        type=Path,
        default=DEFAULT_PIN_PATH,
        help="Path to miri_oracle_pin.json.",
    )
    parser.add_argument(
        "--tier-b-dir",
        type=Path,
        default=DEFAULT_TIER_B_DIR,
        help="Path to Tier B corpus directory containing manifest.json.",
    )
    parser.add_argument(
        "--capture-bin",
        type=Path,
        required=True,
        help="Path to anneal-rustc-capture binary.",
    )
    parser.add_argument(
        "--eval-bin",
        type=Path,
        required=True,
        help="Path to anneal-mir-eval binary.",
    )
    parser.add_argument(
        "--sysroot",
        type=Path,
        default=None,
        help="Path to pinned nightly Rust sysroot.",
    )
    parser.add_argument(
        "--archive",
        type=Path,
        default=None,
        help="Local pre-downloaded Miri .tar.gz archive (still SHA-256 verified).",
    )
    parser.add_argument(
        "--corpus-dir",
        type=Path,
        default=None,
        help="Local pre-extracted tests/ directory (still manifest-SHA-256 verified).",
    )
    parser.add_argument(
        "--no-network",
        action="store_true",
        help="Disallow network fetches (require --archive or --corpus-dir in Tier A).",
    )
    parser.add_argument(
        "--verify-upstream-linkage",
        action="store_true",
        help=(
            "Query api.github.com to verify rust-lang/rust@rustc_commit's "
            "src/tools/miri and tests/fail Git tree SHAs match the "
            "pinned miri_commit (automatic on online Tier A fetches)."
        ),
    )
    parser.add_argument(
        "--profile",
        choices=ALLOWED_PROFILES,
        default=None,
        help=(
            "Evaluator profile mode: 'auto' selects Profile v1 or v2 from each "
            "program's mir_profile_version (default); 'v1' forces --strict-v1; "
            "'v2' forces --profile-v2."
        ),
    )
    parser.add_argument(
        "--target",
        default="x86_64-unknown-linux-gnu",
        help="Target triple for Tier B capture.",
    )
    parser.add_argument(
        "--fuel",
        type=int,
        default=None,
        help="Override evaluator step fuel.",
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=None,
        help=(
            "Parallel worker threads (default: derived from "
            "min(8, cpu_count, max_total_memory_mb // (procs_per_worker * max_memory_mb)); "
            "fails closed if workers * procs_per_worker * max_memory_mb > max_total_memory_mb)."
        ),
    )
    parser.add_argument(
        "--timeout-secs",
        type=int,
        default=60,
        help="Per-subprocess wall-clock timeout in seconds.",
    )
    parser.add_argument(
        "--max-memory-mb",
        type=int,
        default=DEFAULT_MAX_MEMORY_MB,
        help=(
            "Linux RLIMIT_AS memory cap in MiB per confined process "
            f"(default: {DEFAULT_MAX_MEMORY_MB}; must be > 0; fails closed if "
            "seccomp/rlimit confinement is unavailable)."
        ),
    )
    parser.add_argument(
        "--max-total-memory-mb",
        type=int,
        default=DEFAULT_MAX_TOTAL_MEMORY_MB,
        help=(
            "Aggregate Linux RLIMIT_AS memory budget in MiB across all concurrent "
            f"workers and capture descendants (default: {DEFAULT_MAX_TOTAL_MEMORY_MB}; "
            "enforces workers * procs_per_worker * max_memory_mb <= max_total_memory_mb, "
            "with strict single-task read-only seccomp confinement on evaluators and "
            "PGID process-count enforcement capping capture at CAPTURE_MAX_TASKS)."
        ),
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Write deterministic JSON report to this path.",
    )
    parser.add_argument(
        "--summary-markdown",
        type=Path,
        default=None,
        help="Write Markdown summary (e.g. $GITHUB_STEP_SUMMARY) to this path.",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    raw_argv = sys.argv[1:] if argv is None else argv
    if raw_argv and raw_argv[0] == _CONFINED_EXEC_FLAG:
        return _run_confined_exec(raw_argv[1:])

    parser = build_arg_parser()
    args = parser.parse_args(argv)
    t0 = time.monotonic()

    prev_sigterm = None
    installed_sigterm = False
    if (
        hasattr(signal, "SIGTERM")
        and threading.current_thread() is threading.main_thread()
    ):
        def _handle_sigterm(_signum: int, _frame: object) -> None:
            raise SystemExit(128 + int(signal.SIGTERM))

        prev_sigterm = signal.signal(signal.SIGTERM, _handle_sigterm)
        installed_sigterm = True

    try:
        if sys.platform == "linux":
            _harden_parent_process()
        if not args.capture_bin.is_file():
            raise OracleError(f"capture binary not found: {args.capture_bin}")
        if not args.eval_bin.is_file():
            raise OracleError(f"eval binary not found: {args.eval_bin}")

        pin_channel = "nightly-2026-05-31"
        pin_snapshot: dict[str, object] | None = None
        if args.tier_a:
            pin_snapshot = load_pin(args.pin)
            pin_channel = str(
                pin_snapshot.get("rustc_toolchain_channel") or pin_channel
            )
        elif args.pin.exists() or (
            not args.tier_b_dir.is_symlink()
            and args.tier_b_dir.resolve() == DEFAULT_TIER_B_DIR.resolve()
        ):
            pin_snapshot = load_pin(args.pin)
            pin_channel = str(
                pin_snapshot.get("rustc_toolchain_channel") or pin_channel
            )
        sysroot = resolve_sysroot(args.sysroot, pin_channel)

        if args.tier_a:
            if args.archive is not None and args.corpus_dir is not None:
                raise OracleError("pass at most one of --archive or --corpus-dir")
            report = run_tier_a(
                pin_path=args.pin,
                capture_bin=args.capture_bin.resolve(),
                eval_bin=args.eval_bin.resolve(),
                sysroot=sysroot,
                archive_path=args.archive,
                corpus_dir=args.corpus_dir,
                no_network=args.no_network,
                profile_override=args.profile,
                workers=args.workers,
                timeout_secs=args.timeout_secs,
                max_memory_mb=args.max_memory_mb,
                max_total_memory_mb=args.max_total_memory_mb,
                fuel_override=args.fuel,
                pin=pin_snapshot,
                verify_upstream_linkage=args.verify_upstream_linkage,
            )
        else:
            report = run_tier_b(
                tier_b_dir=args.tier_b_dir,
                capture_bin=args.capture_bin.resolve(),
                eval_bin=args.eval_bin.resolve(),
                sysroot=sysroot,
                target=args.target,
                fuel=args.fuel if args.fuel is not None else 2_000_000,
                profile=args.profile or "auto",
                workers=args.workers,
                timeout_secs=args.timeout_secs,
                max_memory_mb=args.max_memory_mb,
                max_total_memory_mb=args.max_total_memory_mb,
                pin=pin_snapshot,
            )
    except OracleError as exc:
        err_report = {
            "schema_version": REPORT_SCHEMA_VERSION,
            "tier": "tier_a" if args.tier_a else "tier_b",
            "passed": False,
            "failures": [str(exc)],
        }
        print(json.dumps(err_report, indent=2, sort_keys=True), file=sys.stderr)
        return 2
    finally:
        if installed_sigterm:
            signal.signal(signal.SIGTERM, prev_sigterm)

    serialized = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized, encoding="utf-8")
    elapsed_secs = round(time.monotonic() - t0, 3)
    if args.summary_markdown is not None:
        args.summary_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.summary_markdown.write_text(
            render_summary_markdown(report, elapsed_secs=elapsed_secs),
            encoding="utf-8",
        )

    compact = {k: v for k, v in report.items() if k != "units"}
    print(json.dumps(compact, indent=2, sort_keys=True))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
