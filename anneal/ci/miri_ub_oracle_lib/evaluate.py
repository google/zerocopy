# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Evaluation of single Rust and MIR JSON units."""

from __future__ import annotations

import json
from pathlib import Path
import re
import shutil
import tempfile

from .common import (
    CAPTURE_MAX_EXPORT_BYTES, CAPTURE_MAX_PROCS, CAPTURE_MAX_TASKS, OracleError,
    _read_regular_file_bytes,
)
from .corpus import parse_compile_flags
from .bounded import (
    _CancelToken, _sanitize_detail, classify_eval_result, run_bounded, sanitized_child_env,
)


def _profile_eval_args(profile: str) -> list[str]:
    """Map harness profile mode to explicit `anneal-mir-eval` CLI flags.

    - `auto`: omit profile overrides so `anneal-mir-eval` selects Profile v1
      or v2 from each emitted program's `mir_profile_version`.
    - `v1`: pass `--strict-v1` to enforce Profile v1 explicitly.
    - `v2`: pass `--profile-v2` to enforce Profile v2 explicitly.
    """
    if profile == "auto":
        return []
    if profile == "v1":
        return ["--strict-v1"]
    if profile == "v2":
        return ["--profile-v2"]
    raise OracleError(f"unsupported profile: {profile!r}")


def _sanitize_crate_name(rel_path: str) -> str:
    stem = Path(rel_path).stem
    name = re.sub(r"[^A-Za-z0-9_]", "_", stem)
    if not name or name[0].isdigit():
        name = "t_" + name
    return name


def evaluate_rust_unit(
    src_path: Path,
    rel_label: str,
    *,
    revision: str | None,
    flags: list[str],
    capture_bin: Path,
    eval_bin: Path,
    sysroot: Path,
    target: str,
    fuel: int,
    profile: str,
    timeout_secs: int,
    max_memory_mb: int,
    expect_valid: bool,
    body_selector: str = "main",
    args: list[str] | None = None,
    edition_override: str | None = None,
    panic_override: str | None = None,
    expected_rustc_commit: str | None = None,
    cancel_token: _CancelToken | None = None,
) -> dict[str, object]:
    """Run one standalone Rust file through `anneal-rustc-capture` + `eval`."""
    edition, panic, unforwarded = parse_compile_flags(flags)
    if edition_override is not None:
        edition = edition_override
    if panic_override is not None:
        panic = panic_override
    if unforwarded:
        # Fail closed before capture when a fixture requires build-affecting
        # rustc compile-flags that `anneal-rustc-capture` does not forward or
        # enforce by default, so coverage is never attributed to a mismatched
        # compilation configuration.
        return {
            "file": rel_label,
            "revision": revision,
            "edition": edition,
            "panic": panic,
            "profile": profile,
            "unforwarded_rustc_flags": unforwarded,
            "capture_rc": None,
            "capture_status": "skipped_unforwarded_flags",
            "bucket": "rustc_or_harness_rejected",
            "sub_bucket": "harness_unforwarded_flags",
            "detail": f"unforwarded compile-flags: {' '.join(unforwarded)}",
        }

    capture_env = sanitized_child_env()
    eval_env = sanitized_child_env()

    with tempfile.TemporaryDirectory(prefix="anneal-miri-unit-") as tmp:
        tmp_path = Path(tmp)
        src_dir = tmp_path / "src"
        src_dir.mkdir()
        copied_root = src_dir / "main.rs"
        shutil.copyfile(src_path, copied_root)
        work_dir = tmp_path / "work"
        work_dir.mkdir()
        export_dir = tmp_path / "export"
        out_dir = work_dir / "out"
        cap_tmp = work_dir / "tmp"
        capture_env["TMPDIR"] = str(cap_tmp)

        crate_name = _sanitize_crate_name(rel_label)
        cap_cmd = [
            str(capture_bin),
            "capture",
            "--crate-root",
            str(copied_root),
            "--crate-name",
            crate_name,
            "--crate-type",
            "bin",
            "--edition",
            edition,
            "--panic",
            panic,
            "--target",
            target,
            "--out-dir",
            str(out_dir),
            "--sysroot",
            str(sysroot),
            "--scope",
            "crate",
            "--source-file",
            str(copied_root),
        ]
        if revision:
            cap_cmd.extend(["--cfg", revision])

        # Isolate candidate `anneal-rustc-capture` inside private user/PID/
        # mount/network namespaces with a bounded `tmpfs` mounted on
        # `work_dir`, Landlock ABI >= 3 (read-only source/sysroot + narrow
        # writable `work_dir`), default-deny seccomp, `RLIMIT_NPROC`/
        # `RLIMIT_NOFILE`/`RLIMIT_AS`/`RLIMIT_FSIZE`, and bounded post-teardown
        # export of regular output files to `export_dir`.
        cap_rc, cap_out, cap_err, _ = run_bounded(
            cap_cmd,
            env=capture_env,
            timeout_secs=timeout_secs,
            max_memory_mb=max_memory_mb,
            confinement="capture",
            max_procs=CAPTURE_MAX_PROCS,
            max_tasks=CAPTURE_MAX_TASKS,
            read_only_paths=(src_dir,),
            read_only_exec_paths=(sysroot,),
            read_write_paths=(work_dir,),
            prepend_ld_library_path=sysroot / "lib",
            export_src=out_dir / "capture.json",
            export_dst=export_dir / "capture.json",
            cancel_token=cancel_token,
        )

        rec: dict[str, object] = {
            "file": rel_label,
            "revision": revision,
            "edition": edition,
            "panic": panic,
            "profile": profile,
            "unforwarded_rustc_flags": unforwarded,
            "capture_rc": cap_rc,
        }

        status: str | None = None
        cap_json: dict[str, object] = {}
        non_empty_lines = [ln for ln in cap_out.splitlines() if ln.strip()]
        if non_empty_lines:
            try:
                parsed = json.loads(non_empty_lines[-1])
                if isinstance(parsed, dict):
                    cap_json = parsed
                    raw_status = parsed.get("status")
                    if isinstance(raw_status, str):
                        status = raw_status
            except json.JSONDecodeError:
                status = "unparsed"

        rec["capture_status"] = status or "missing"
        if not (status == "captured" and cap_rc == 0):
            if status == "unsupported" and cap_rc == 1:
                rec["bucket"] = "capture_refused"
                rec["sub_bucket"] = None
                unsupported = cap_json.get("unsupported")
                diags = cap_json.get("diagnostics")
                if isinstance(unsupported, list) and unsupported:
                    first = unsupported[0]
                    if isinstance(first, dict) and first.get("reason"):
                        rec["detail"] = str(first["reason"]).replace(
                            str(tmp_path), "<tmp>"
                        )[:240]
                if "detail" not in rec and isinstance(diags, list) and diags:
                    rec["detail"] = str(diags[0]).replace(
                        str(tmp_path), "<tmp>"
                    )[:240]
            elif status == "compiler_failed" and cap_rc == 1:
                rec["bucket"] = "rustc_or_harness_rejected"
                rec["sub_bucket"] = "compiler_failed"
                diags = cap_json.get("diagnostics")
                if isinstance(diags, list) and diags:
                    rec["detail"] = str(diags[0]).replace(
                        str(tmp_path), "<tmp>"
                    )[:240]
            else:
                rec["bucket"] = "tool_error"
                rec["sub_bucket"] = (
                    str(cap_rc)
                    if not isinstance(cap_rc, int)
                    else f"capture_rc_status_mismatch:{cap_rc}:{status or 'missing'}"
                )
                rec["detail"] = _sanitize_detail(
                    (cap_err or cap_out)[-480:], tmp_path, max_len=240
                )
            return rec

        capture_json = export_dir / "capture.json"
        if not capture_json.is_file():
            rec["bucket"] = "tool_error"
            rec["sub_bucket"] = "missing_capture_json"
            return rec

        if expected_rustc_commit is not None:
            try:
                manifest_bytes = _read_regular_file_bytes(
                    capture_json,
                    max_bytes=CAPTURE_MAX_EXPORT_BYTES,
                    label="capture manifest",
                )
                manifest_obj = json.loads(manifest_bytes.decode("utf-8"))
            except (OracleError, UnicodeDecodeError, json.JSONDecodeError) as exc:
                rec["bucket"] = "tool_error"
                rec["sub_bucket"] = "invalid_capture_json"
                rec["detail"] = _sanitize_detail(str(exc), tmp_path, max_len=240)
                return rec
            compiler_meta = (
                manifest_obj.get("compiler")
                if isinstance(manifest_obj, dict)
                else None
            )
            actual_commit = (
                compiler_meta.get("commit")
                if isinstance(compiler_meta, dict)
                else None
            )
            if (
                not isinstance(actual_commit, str)
                or actual_commit != expected_rustc_commit
            ):
                rec["bucket"] = "tool_error"
                rec["sub_bucket"] = "compiler_commit_mismatch"
                rec["detail"] = (
                    f"capture.json compiler.commit {actual_commit!r} != "
                    f"pinned rustc_commit {expected_rustc_commit!r}"
                )[:240]
                return rec

        eval_cmd = [
            str(eval_bin),
            "eval",
            str(capture_json),
            "--body",
            body_selector,
            "--fuel",
            str(fuel),
            "--json",
        ]
        for arg in args or []:
            eval_cmd.extend(["--arg", arg])
        eval_cmd.extend(_profile_eval_args(profile))

        eval_rc, eval_out, eval_err, _ = run_bounded(
            eval_cmd,
            env=eval_env,
            timeout_secs=timeout_secs,
            max_memory_mb=max_memory_mb,
            read_only_paths=(capture_json,),
            cancel_token=cancel_token,
        )
        bucket, sub_bucket, detail = classify_eval_result(
            eval_rc, eval_out, eval_err, expect_valid=expect_valid
        )
        rec["eval_rc"] = eval_rc
        rec["bucket"] = bucket
        rec["sub_bucket"] = sub_bucket
        if detail is not None:
            rec["detail"] = _sanitize_detail(detail, tmp_path, max_len=300)
        return rec


def evaluate_mir_json_unit(
    mir_json_path: Path,
    rel_label: str,
    *,
    eval_bin: Path,
    fuel: int,
    profile: str,
    timeout_secs: int,
    max_memory_mb: int,
    expect_valid: bool,
    body_selector: str | None = None,
    args: list[str] | None = None,
    cancel_token: _CancelToken | None = None,
) -> dict[str, object]:
    """Run one direct MIR JSON fixture through `anneal-mir-eval eval --json`."""
    eval_cmd = [
        str(eval_bin),
        "eval",
        str(mir_json_path),
        "--fuel",
        str(fuel),
        "--json",
    ]
    if body_selector is not None:
        eval_cmd.extend(["--body", body_selector])
    for arg in args or []:
        eval_cmd.extend(["--arg", arg])
    eval_cmd.extend(_profile_eval_args(profile))

    eval_rc, eval_out, eval_err, _ = run_bounded(
        eval_cmd,
        env=sanitized_child_env(),
        timeout_secs=timeout_secs,
        max_memory_mb=max_memory_mb,
        read_only_paths=(mir_json_path,),
        cancel_token=cancel_token,
    )
    bucket, sub_bucket, detail = classify_eval_result(
        eval_rc, eval_out, eval_err, expect_valid=expect_valid
    )
    rec: dict[str, object] = {
        "file": rel_label,
        "revision": None,
        "profile": profile,
        "eval_rc": eval_rc,
        "bucket": bucket,
        "sub_bucket": sub_bucket,
    }
    if detail is not None:
        rec["detail"] = _sanitize_detail(
            detail, mir_json_path.parent, max_len=300
        )
    return rec
