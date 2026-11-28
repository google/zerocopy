# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tier A and Tier B runs and the worker memory budget."""

from __future__ import annotations

from collections import Counter
import concurrent.futures as cf
import os
from pathlib import Path
import tempfile

from .common import (
    ALLOWED_PROFILES, CAPTURE_MAX_DISK_MB, CAPTURE_MAX_TASKS, DEFAULT_MAX_TOTAL_MEMORY_MB,
    DEFAULT_MAX_WORKERS, DEFAULT_PIN_PATH, DEFAULT_TIER_B_DIR, MAX_SINGLE_FILE_BYTES, OracleError,
    REPORT_SCHEMA_VERSION, _read_regular_file_bytes,
)
from .pins import load_pin, load_tier_b_manifest
from .archive import (
    _expected_archive_tree_shas, copy_and_verify_archive_sha256, download_verified_archive,
    safe_extract_miri_corpus, verify_rustc_miri_linkage,
)
from .corpus import harness_skip_reason, parse_miri_headers, verify_corpus_manifest
from .landlock import _require_confinement_support
from .bounded import _CancelToken, _sanitize_detail
from .evaluate import evaluate_mir_json_unit, evaluate_rust_unit
from .gates import evaluate_tier_a_gate, evaluate_tier_b_gate


def _resolve_worker_memory_budget(
    *,
    workers: int | None,
    max_memory_mb: int,
    max_total_memory_mb: int,
    procs_per_worker: int = CAPTURE_MAX_TASKS,
) -> tuple[int, int]:
    """Enforce aggregate `workers * (procs_per_worker * max_memory_mb + CAPTURE_MAX_DISK_MB) <= max_total_memory_mb`.

    Each evaluator runs with `confinement="eval"` (strictly 1 task and read-only
    filesystem via Landlock + seccomp + `RLIMIT_FSIZE=0`), whereas
    `anneal-rustc-capture` runs inside private user/PID/mount/network namespaces
    with a kernel-enforced task ceiling (`CAPTURE_MAX_TASKS` via `RLIMIT_NPROC`),
    a `CAPTURE_MAX_DISK_MB` `tmpfs` work quota, Landlock ABI >= 3 filesystem
    isolation, default-deny seccomp, and defense-in-depth PGID process counting.
    """
    _require_confinement_support(
        max_memory_mb, require_truncate_mediation=procs_per_worker > 1
    )
    if (
        isinstance(max_total_memory_mb, bool)
        or not isinstance(max_total_memory_mb, int)
        or max_total_memory_mb <= 0
    ):
        raise OracleError(
            f"--max-total-memory-mb must be a positive integer MiB value, got {max_total_memory_mb!r}"
        )
    if (
        isinstance(procs_per_worker, bool)
        or not isinstance(procs_per_worker, int)
        or procs_per_worker <= 0
    ):
        raise OracleError(
            f"procs_per_worker must be a positive integer, got {procs_per_worker!r}"
        )
    per_worker_mb = procs_per_worker * max_memory_mb + CAPTURE_MAX_DISK_MB
    if per_worker_mb > max_total_memory_mb:
        raise OracleError(
            f"per-worker memory budget ({procs_per_worker} procs * "
            f"--max-memory-mb={max_memory_mb} MiB + {CAPTURE_MAX_DISK_MB} MiB "
            f"capture tmpfs = {per_worker_mb} MiB) exceeds aggregate "
            f"--max-total-memory-mb={max_total_memory_mb} MiB"
        )
    budget_workers = max_total_memory_mb // per_worker_mb
    if workers is None:
        cpu_cap = min(DEFAULT_MAX_WORKERS, os.cpu_count() or 4)
        return max(1, min(cpu_cap, budget_workers)), max_memory_mb
    if isinstance(workers, bool) or not isinstance(workers, int) or workers <= 0:
        raise OracleError(
            f"--workers must be a positive integer, got {workers!r}"
        )
    if workers * per_worker_mb > max_total_memory_mb:
        raise OracleError(
            f"aggregate child memory budget exceeded: {workers} workers * "
            f"({procs_per_worker} procs * {max_memory_mb} MiB + "
            f"{CAPTURE_MAX_DISK_MB} MiB tmpfs) = {workers * per_worker_mb} MiB > "
            f"--max-total-memory-mb={max_total_memory_mb} MiB"
        )
    return workers, max_memory_mb


def run_tier_a(
    *,
    pin_path: Path,
    capture_bin: Path,
    eval_bin: Path,
    sysroot: Path,
    archive_path: Path | None,
    corpus_dir: Path | None,
    no_network: bool,
    profile_override: str | None,
    workers: int | None,
    timeout_secs: int,
    max_memory_mb: int,
    fuel_override: int | None,
    max_total_memory_mb: int = DEFAULT_MAX_TOTAL_MEMORY_MB,
    pin: dict[str, object] | None = None,
    verify_upstream_linkage: bool = False,
) -> dict[str, object]:
    """Execute Tier A over the SHA-256-pinned upstream `rust-lang/miri` suite."""
    effective_workers, max_memory_mb = _resolve_worker_memory_budget(
        workers=workers,
        max_memory_mb=max_memory_mb,
        max_total_memory_mb=max_total_memory_mb,
        procs_per_worker=CAPTURE_MAX_TASKS,
    )
    pin = dict(pin) if pin is not None else load_pin(pin_path)
    profile = profile_override or str(pin["profile"])
    if profile not in ALLOWED_PROFILES:
        raise OracleError(f"unsupported profile: {profile!r}")
    fuel = fuel_override if fuel_override is not None else int(pin["fuel"])  # type: ignore[arg-type]
    target = str(pin["target"])
    subdirs = list(pin["extract_subdirs"])  # type: ignore[arg-type]

    if verify_upstream_linkage:
        if no_network:
            raise OracleError(
                "--verify-upstream-linkage cannot be combined with --no-network"
            )
        verify_rustc_miri_linkage(pin)

    with tempfile.TemporaryDirectory(prefix="anneal-miri-tier-a-") as tmp:
        tmp_path = Path(tmp)
        if corpus_dir is not None:
            if corpus_dir.is_symlink():
                raise OracleError(
                    f"corpus directory must not be a symlink: {corpus_dir}"
                )
            active_corpus = tmp_path / "corpus_snapshot"
            manifest_sha, files = verify_corpus_manifest(
                corpus_dir, pin, snapshot_dir=active_corpus
            )
        else:
            verified_archive = tmp_path / "miri-pinned.tar.gz"
            if archive_path is not None:
                copy_and_verify_archive_sha256(
                    archive_path, verified_archive, str(pin["archive_sha256"])
                )
            else:
                if no_network:
                    raise OracleError(
                        "Tier A requires --archive or --corpus-dir when "
                        "--no-network is set"
                    )
                if not verify_upstream_linkage:
                    verify_rustc_miri_linkage(pin)
                download_verified_archive(
                    str(pin["archive_url"]),
                    str(pin["archive_sha256"]),
                    verified_archive,
                )
            active_corpus = tmp_path / "tests"
            safe_extract_miri_corpus(
                verified_archive,
                active_corpus,
                expected_top_dir=str(pin["expected_top_dir"]),
                extract_subdirs=subdirs,
                expected_tree_shas=_expected_archive_tree_shas(pin),
            )
            manifest_sha, files = verify_corpus_manifest(active_corpus, pin)

        work_items: list[tuple[str, str | None, list[str], str | None]] = []
        for rel in files:
            text = _read_regular_file_bytes(
                active_corpus / rel,
                max_bytes=MAX_SINGLE_FILE_BYTES,
                label="corpus file",
            ).decode("utf-8", errors="replace")
            hdr = parse_miri_headers(text)
            revs = list(hdr["revisions"]) or [None]  # type: ignore[arg-type]
            hdr_flags: dict[str | None, list[str]] = hdr["flags"]  # type: ignore[assignment]
            for rev in revs:
                skip = harness_skip_reason(hdr, target, rev)
                combined_flags = list(hdr_flags.get(None, []))
                if rev is not None:
                    combined_flags.extend(hdr_flags.get(rev, []))
                work_items.append((rel, rev, combined_flags, skip))

        cancel_token = _CancelToken()

        def _run_one(
            item: tuple[str, str | None, list[str], str | None],
        ) -> dict[str, object]:
            rel, rev, flags, skip = item
            if skip is not None:
                return {
                    "file": rel,
                    "revision": rev,
                    "profile": profile,
                    "bucket": "rustc_or_harness_rejected",
                    "sub_bucket": "harness_target",
                    "detail": skip,
                }
            return evaluate_rust_unit(
                active_corpus / rel,
                rel,
                revision=rev,
                flags=flags,
                capture_bin=capture_bin,
                eval_bin=eval_bin,
                sysroot=sysroot,
                target=target,
                fuel=fuel,
                profile=profile,
                timeout_secs=timeout_secs,
                max_memory_mb=max_memory_mb,
                expect_valid=False,
                expected_rustc_commit=str(pin["rustc_commit"]),
                cancel_token=cancel_token,
            )

        def _run_one_guarded(
            item: tuple[str, str | None, list[str], str | None],
        ) -> dict[str, object]:
            cancel_token.check_cancelled()
            return _run_one(item)

        units: list[dict[str, object]] = []
        pool = cf.ThreadPoolExecutor(max_workers=effective_workers)
        interrupted = False
        try:
            fut_map = {
                pool.submit(_run_one_guarded, item): item for item in work_items
            }
            for fut in cf.as_completed(fut_map):
                rel, rev, _, _ = fut_map[fut]
                try:
                    units.append(fut.result())
                except Exception as exc:  # noqa: BLE001
                    units.append({
                        "file": rel,
                        "revision": rev,
                        "profile": profile,
                        "bucket": "tool_error",
                        "sub_bucket": "worker_exception",
                        "detail": _sanitize_detail(repr(exc), max_len=300),
                    })
        except BaseException:
            interrupted = True
            cancel_token.cancel_and_kill_all()
            pool.shutdown(wait=True, cancel_futures=True)
            raise
        finally:
            if not interrupted:
                pool.shutdown(wait=True)

    units.sort(key=lambda u: (str(u["file"]), str(u.get("revision") or "")))
    passed, failures, counts = evaluate_tier_a_gate(
        units, total_files=len(files), pin=pin
    )
    refusal_ctr = Counter(
        str(u.get("detail") or "<no reason>")
        for u in units
        if u.get("bucket") == "capture_refused"
    )
    top_refusal_reasons = [
        {"reason": reason, "count": cnt}
        for reason, cnt in sorted(
            refusal_ctr.items(), key=lambda kv: (-kv[1], kv[0])
        )[:10]
    ]

    return {
        "schema_version": REPORT_SCHEMA_VERSION,
        "tier": "tier_a",
        "passed": passed,
        "failures": failures,
        "profile": profile,
        "target": target,
        "fuel": fuel,
        "total_files": len(files),
        "total_units": len(units),
        "counts": counts,
        "top_refusal_reasons": top_refusal_reasons,
        "pin": {
            "upstream_repo": pin["upstream_repo"],
            "miri_commit": pin["miri_commit"],
            "rustc_commit": pin["rustc_commit"],
            "archive_sha256": pin["archive_sha256"],
            "corpus_manifest_sha256": manifest_sha,
            "min_caught_ub": pin["min_caught_ub"],
            "max_unsound_accepts": 0,
            "max_tool_errors": 0,
        },
        "caught_ub_files": [
            f"{u['file']}" + (f"[{u['revision']}]" if u.get("revision") else "")
            for u in units
            if u.get("bucket") == "caught_ub"
        ],
        "unsound_accept_files": [
            f"{u['file']}" + (f"[{u['revision']}]" if u.get("revision") else "")
            for u in units
            if u.get("bucket") == "unsound_accept"
        ],
        "units": units,
    }


def run_tier_b(
    *,
    tier_b_dir: Path,
    capture_bin: Path,
    eval_bin: Path,
    sysroot: Path,
    target: str,
    fuel: int,
    profile: str,
    workers: int | None,
    timeout_secs: int,
    max_memory_mb: int,
    max_total_memory_mb: int = DEFAULT_MAX_TOTAL_MEMORY_MB,
    pin: dict[str, object] | None = None,
) -> dict[str, object]:
    """Execute Tier B curated minimal UB regression corpus + valid controls."""
    _require_confinement_support(max_memory_mb, require_truncate_mediation=False)
    expected_sha: str | None = None
    min_counts: dict[str, int] | None = None
    expected_rustc_commit: str | None = None
    if not tier_b_dir.is_symlink() and (
        tier_b_dir.resolve() == DEFAULT_TIER_B_DIR.resolve()
    ):
        active_pin = dict(pin) if pin is not None else load_pin(DEFAULT_PIN_PATH)
        raw_sha = active_pin.get("tier_b_corpus_sha256")
        raw_counts = active_pin.get("tier_b_min_counts")
        raw_rustc_commit = active_pin.get("rustc_commit")
        if (
            not isinstance(raw_sha, str)
            or not isinstance(raw_counts, dict)
            or not isinstance(raw_rustc_commit, str)
            or len(raw_rustc_commit) != 40
            or not all(c in "0123456789abcdef" for c in raw_rustc_commit)
        ):
            raise OracleError(
                "pinned manifest must declare tier_b_corpus_sha256, "
                "tier_b_min_counts, and a 40-hex rustc_commit for the "
                "repository Tier B corpus"
            )
        expected_sha = raw_sha
        min_counts = {str(k): int(v) for k, v in raw_counts.items()}
        expected_rustc_commit = raw_rustc_commit

    with tempfile.TemporaryDirectory(prefix="anneal-miri-tier-b-") as tmp:
        root = Path(tmp) / "corpus_snapshot"
        manifest = load_tier_b_manifest(
            tier_b_dir,
            expected_corpus_sha256=expected_sha,
            min_kind_counts=min_counts,
            snapshot_dir=root,
        )
        fixtures: list[dict[str, object]] = manifest["fixtures"]  # type: ignore[assignment]
        has_rust_fixtures = any(
            str(entry["kind"]) not in ("mir_ub_caught", "mir_valid_control")
            for entry in fixtures
        )
        effective_workers, max_memory_mb = _resolve_worker_memory_budget(
            workers=workers,
            max_memory_mb=max_memory_mb,
            max_total_memory_mb=max_total_memory_mb,
            procs_per_worker=CAPTURE_MAX_TASKS if has_rust_fixtures else 1,
        )

        cancel_token = _CancelToken()

        def _run_fixture(entry: dict[str, object]) -> dict[str, object]:
            fid = str(entry["id"])
            rel = str(entry["path"])
            kind = str(entry["kind"])
            category = str(entry["category"])
            expect_valid = kind in ("rust_valid_control", "mir_valid_control")
            fpath = root / rel
            entry_profile = str(entry.get("profile") or profile)

            if kind in ("mir_ub_caught", "mir_valid_control"):
                rec = evaluate_mir_json_unit(
                    fpath,
                    rel,
                    eval_bin=eval_bin,
                    fuel=int(entry.get("fuel") or fuel),  # type: ignore[arg-type]
                    profile=entry_profile,
                    timeout_secs=timeout_secs,
                    max_memory_mb=max_memory_mb,
                    expect_valid=expect_valid,
                    body_selector=(
                        str(entry["body"]) if entry.get("body") is not None else None
                    ),
                    args=[str(a) for a in entry.get("args", [])],  # type: ignore[union-attr]
                    cancel_token=cancel_token,
                )
            else:
                rec = evaluate_rust_unit(
                    fpath,
                    rel,
                    revision=None,
                    flags=[],
                    capture_bin=capture_bin,
                    eval_bin=eval_bin,
                    sysroot=sysroot,
                    target=target,
                    fuel=int(entry.get("fuel") or fuel),  # type: ignore[arg-type]
                    profile=entry_profile,
                    timeout_secs=timeout_secs,
                    max_memory_mb=max_memory_mb,
                    expect_valid=expect_valid,
                    body_selector=str(entry.get("body") or "main"),
                    args=[str(a) for a in entry.get("args", [])],  # type: ignore[union-attr]
                    edition_override=str(entry.get("edition") or "2024"),
                    panic_override=str(entry.get("panic") or "unwind"),
                    expected_rustc_commit=expected_rustc_commit,
                    cancel_token=cancel_token,
                )

            rec["id"] = fid
            rec["kind"] = kind
            rec["category"] = category
            if "expected_fault_substring" in entry:
                rec["expected_fault_substring"] = entry["expected_fault_substring"]
            return rec

        def _run_fixture_guarded(
            entry: dict[str, object],
        ) -> dict[str, object]:
            cancel_token.check_cancelled()
            return _run_fixture(entry)

        results: list[dict[str, object]] = []
        pool = cf.ThreadPoolExecutor(max_workers=effective_workers)
        interrupted = False
        try:
            fut_map = {
                pool.submit(_run_fixture_guarded, entry): entry
                for entry in fixtures
            }
            for fut in cf.as_completed(fut_map):
                entry = fut_map[fut]
                try:
                    results.append(fut.result())
                except Exception as exc:  # noqa: BLE001
                    results.append({
                        "id": str(entry["id"]),
                        "file": str(entry["path"]),
                        "kind": str(entry["kind"]),
                        "category": str(entry["category"]),
                        "revision": None,
                        "profile": str(entry.get("profile") or profile),
                        "bucket": "tool_error",
                        "sub_bucket": "worker_exception",
                        "detail": _sanitize_detail(repr(exc), max_len=300),
                    })
        except BaseException:
            interrupted = True
            cancel_token.cancel_and_kill_all()
            pool.shutdown(wait=True, cancel_futures=True)
            raise
        finally:
            if not interrupted:
                pool.shutdown(wait=True)

    results.sort(key=lambda r: str(r["id"]))
    passed, failures, counts = evaluate_tier_b_gate(results)
    promotion_candidates = [
        str(r["id"])
        for r in results
        if r.get("kind") == "rust_ub_fail_closed" and r.get("bucket") == "caught_ub"
    ]
    kind_counts = dict(sorted(Counter(str(r["kind"]) for r in results).items()))
    return {
        "schema_version": REPORT_SCHEMA_VERSION,
        "tier": "tier_b",
        "passed": passed,
        "failures": failures,
        "profile": profile,
        "target": target,
        "fuel": fuel,
        "total_fixtures": len(results),
        "kind_counts": kind_counts,
        "counts": counts,
        "promotion_candidates": promotion_candidates,
        "units": results,
    }
