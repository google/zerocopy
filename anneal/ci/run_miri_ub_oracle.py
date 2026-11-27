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
from collections import Counter
from collections.abc import Callable
import concurrent.futures as cf
import ctypes
import errno
import gzip
import hashlib
import hmac
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import resource
import shutil
import signal
import stat
import struct
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import urllib.parse
import urllib.request
import zlib


CI_DIR = Path(__file__).resolve().parent
ANNEAL_DIR = CI_DIR.parent
REPO_ROOT = ANNEAL_DIR.parent
DEFAULT_PIN_PATH = CI_DIR / "miri_oracle_pin.json"
DEFAULT_TIER_B_DIR = ANNEAL_DIR / "tests" / "corpora" / "miri_ub"

PIN_SCHEMA_VERSION = 1
TIER_B_SCHEMA_VERSION = 1
REPORT_SCHEMA_VERSION = 1

HEX40_RE = re.compile(r"^[0-9a-f]{40}$")
HEX64_RE = re.compile(r"^[0-9a-f]{64}$")
MIRI_HEADER_RE = re.compile(r"^//@(?:\[([^\]]+)\])?\s*([a-z-]+)\s*:?\s*(.*)$")

ALLOWED_ARCHIVE_HOSTS = frozenset({"github.com", "codeload.github.com"})
ALLOWED_API_HOSTS = frozenset({"api.github.com"})
ALLOWED_ARCHIVE_URL_PREFIX = "https://github.com/rust-lang/miri/archive/"

MAX_ARCHIVE_BYTES = 32 * 1024 * 1024
MAX_DECOMPRESSED_TAR_BYTES = 128 * 1024 * 1024
MAX_TAR_MEMBERS = 10_000
MAX_CORPUS_DIR_ENTRIES = 10_000
MAX_TIER_B_DIR_ENTRIES = 2_048
MAX_CORPUS_DIR_DEPTH = 32
MAX_SINGLE_FILE_BYTES = 1 * 1024 * 1024
MAX_PIN_BYTES = 1 * 1024 * 1024
MAX_TOTAL_EXTRACTED_BYTES = 16 * 1024 * 1024
MAX_SUBPROCESS_FSIZE_BYTES = 32 * 1024 * 1024
EVAL_MAX_NOFILE = 32
CAPTURE_MAX_NOFILE = 256
CAPTURE_MAX_DISK_MB = 32
CAPTURE_MAX_DISK_BYTES = CAPTURE_MAX_DISK_MB * 1024 * 1024
CAPTURE_MAX_INODES = 1024
CAPTURE_MAX_EXPORT_BYTES = 16 * 1024 * 1024
MAX_CHILD_OUTPUT_BYTES = 4 * 1024 * 1024
DEFAULT_MAX_MEMORY_MB = 1024
DEFAULT_MAX_TOTAL_MEMORY_MB = 16384
DEFAULT_MAX_WORKERS = 8
CAPTURE_MAX_PROCS = 2  # PGID watchdog cap: capture + rustc --version probe
CAPTURE_MAX_TASKS = 8  # Kernel-enforced task cap (CLONE_NEWUSER + RLIMIT_NPROC)
CHILD_READ_CHUNK_BYTES = 64 * 1024
DOWNLOAD_CHUNK_BYTES = 64 * 1024

ALLOWED_TIER_B_KINDS = frozenset({
    "rust_ub_caught",
    "rust_ub_fail_closed",
    "mir_ub_caught",
    "rust_valid_control",
    "mir_valid_control",
})

ALLOWED_PROFILES = ("auto", "v1", "v2")

# Environment variables that carry GitHub Actions credentials, workflow-command
# files (`GITHUB_ENV`, `GITHUB_PATH`, `GITHUB_OUTPUT`, `GITHUB_STEP_SUMMARY`),
# or runner paths and must never be forwarded to child processes (especially
# PR-modifiable zero-TCB `tools/`). Matches `ci-core` prefix scrubbing.
STRIPPED_CI_ENV_VARS = frozenset({
    "GH_TOKEN",
})
STRIPPED_CI_ENV_PREFIXES = (
    "ACTIONS_",
    "GITHUB_",
    "RUNNER_",
)

BUCKETS = (
    "caught_ub",
    "accepted_valid",
    "unsound_accept",
    "eval_fail_closed",
    "capture_refused",
    "rustc_or_harness_rejected",
    "tool_error",
)


class OracleError(RuntimeError):
    """Fail-closed configuration, supply-chain, or archive safety error."""


def _validate_hex(value: object, pattern: re.Pattern[str], field: str) -> str:
    if not isinstance(value, str) or not pattern.fullmatch(value):
        raise OracleError(f"pin field '{field}' must match {pattern.pattern}")
    return value


def _validate_positive_int(value: object, field: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        raise OracleError(f"pin field '{field}' must be a positive integer")
    return value


def _read_regular_file_bytes(
    path: Path, *, max_bytes: int, label: str
) -> bytes:
    """Atomically open a non-symlink regular file with a hard byte bound."""
    flags = (
        os.O_RDONLY
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    try:
        fd = os.open(path, flags)
    except OSError as exc:
        if exc.errno == errno.ELOOP:
            raise OracleError(
                f"{label} must be a non-symlink regular file: {path}"
            ) from exc
        raise OracleError(f"failed to load {label} '{path}': {exc}") from exc
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise OracleError(
                f"{label} must be a non-symlink regular file: {path}"
            )
        if st.st_size > max_bytes:
            raise OracleError(
                f"{label} '{path}' exceeds max size "
                f"({st.st_size} > {max_bytes} bytes)"
            )
        buf = bytearray()
        while True:
            chunk = os.read(fd, 65536)
            if not chunk:
                break
            if len(buf) + len(chunk) > max_bytes:
                raise OracleError(
                    f"{label} '{path}' exceeds max size ({max_bytes} bytes)"
                )
            buf.extend(chunk)
        return bytes(buf)
    except OSError as exc:
        raise OracleError(f"failed to load {label} '{path}': {exc}") from exc
    finally:
        os.close(fd)


def load_pin(pin_path: Path) -> dict[str, object]:
    """Load and fail-closed validate `miri_oracle_pin.json`."""
    raw_bytes = _read_regular_file_bytes(
        pin_path, max_bytes=MAX_PIN_BYTES, label="--pin"
    )
    try:
        data = json.loads(raw_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise OracleError(f"failed to load pin '{pin_path}': {exc}") from exc

    if not isinstance(data, dict):
        raise OracleError("pin manifest must be a JSON object")
    if data.get("schema_version") != PIN_SCHEMA_VERSION:
        raise OracleError(
            f"unsupported pin schema_version: {data.get('schema_version')!r}"
        )
    if data.get("upstream_repo") != "rust-lang/miri":
        raise OracleError(
            "pin field 'upstream_repo' must equal 'rust-lang/miri', "
            f"got {data.get('upstream_repo')!r}"
        )

    miri_commit = _validate_hex(data.get("miri_commit"), HEX40_RE, "miri_commit")
    _validate_hex(data.get("rustc_commit"), HEX40_RE, "rustc_commit")
    _validate_hex(data.get("miri_tree_sha"), HEX40_RE, "miri_tree_sha")
    _validate_hex(data.get("fail_tree_sha"), HEX40_RE, "fail_tree_sha")
    if "fail_dep_tree_sha" in data:
        _validate_hex(
            data.get("fail_dep_tree_sha"), HEX40_RE, "fail_dep_tree_sha"
        )
    _validate_hex(data.get("archive_sha256"), HEX64_RE, "archive_sha256")
    _validate_hex(
        data.get("corpus_manifest_sha256"), HEX64_RE, "corpus_manifest_sha256"
    )

    archive_url = data.get("archive_url")
    expected_url = f"{ALLOWED_ARCHIVE_URL_PREFIX}{miri_commit}.tar.gz"
    if archive_url != expected_url:
        raise OracleError(
            f"archive_url must equal '{expected_url}', got {archive_url!r}"
        )

    expected_top_dir = data.get("expected_top_dir")
    if expected_top_dir != f"miri-{miri_commit}":
        raise OracleError(
            f"expected_top_dir must equal 'miri-{miri_commit}', "
            f"got {expected_top_dir!r}"
        )

    extract_subdirs = data.get("extract_subdirs")
    if not isinstance(extract_subdirs, list) or not extract_subdirs:
        raise OracleError("extract_subdirs must be a non-empty list of tests/*")
    seen_subdirs: set[str] = set()
    for raw_sub in extract_subdirs:
        if (
            not isinstance(raw_sub, str)
            or not raw_sub
            or "\\" in raw_sub
            or "\x00" in raw_sub
            or raw_sub.startswith("/")
        ):
            raise OracleError(f"invalid extract_subdirs entry: {raw_sub!r}")
        parts = raw_sub.split("/")
        if len(parts) < 2 or parts[0] != "tests":
            raise OracleError(
                f"extract_subdirs entry must be under 'tests/': {raw_sub!r}"
            )
        for seg in parts:
            if seg in ("", ".", "..") or ":" in seg:
                raise OracleError(
                    f"forbidden segment {seg!r} in extract_subdirs: {raw_sub!r}"
                )
        norm_sub = "/".join(parts)
        if norm_sub in seen_subdirs:
            raise OracleError(f"duplicate extract_subdirs entry: {raw_sub!r}")
        seen_subdirs.add(norm_sub)
    sorted_subdirs = sorted(seen_subdirs)
    for idx, prev in enumerate(sorted_subdirs):
        prefix = prev + "/"
        for nxt in sorted_subdirs[idx + 1 :]:
            if nxt.startswith(prefix):
                raise OracleError(
                    f"overlapping extract_subdirs entries: {prev!r} and {nxt!r}"
                )

    _validate_positive_int(data.get("expected_file_count"), "expected_file_count")
    if "expected_unit_count" in data:
        _validate_positive_int(data.get("expected_unit_count"), "expected_unit_count")
    if "max_harness_skips" in data:
        val = data.get("max_harness_skips")
        if isinstance(val, bool) or not isinstance(val, int) or val < 0:
            raise OracleError("pin field 'max_harness_skips' must be a non-negative int")
    if "max_rustc_or_harness_rejected" in data:
        val = data.get("max_rustc_or_harness_rejected")
        if isinstance(val, bool) or not isinstance(val, int) or val < 0:
            raise OracleError(
                "pin field 'max_rustc_or_harness_rejected' must be a non-negative int"
            )
    if "tests/fail-dep" in seen_subdirs and "fail_dep_tree_sha" not in data:
        raise OracleError(
            "pin must declare fail_dep_tree_sha when tests/fail-dep is extracted"
        )
    _validate_positive_int(data.get("fuel"), "fuel")
    min_caught = _validate_positive_int(data.get("min_caught_ub"), "min_caught_ub")
    if "expected_caught_ub_units" in data:
        exp_units = data.get("expected_caught_ub_units")
        if (
            not isinstance(exp_units, list)
            or not all(isinstance(u, str) and u for u in exp_units)
            or len(set(exp_units)) != len(exp_units)
        ):
            raise OracleError(
                "pin field 'expected_caught_ub_units' must be unique non-empty strings"
            )
        if len(exp_units) > min_caught:
            raise OracleError(
                "len(expected_caught_ub_units) cannot exceed min_caught_ub"
            )

    if data.get("max_unsound_accepts") != 0:
        raise OracleError("max_unsound_accepts must be 0 (fail-closed)")
    if data.get("max_tool_errors") != 0:
        raise OracleError("max_tool_errors must be 0 (fail-closed)")
    if data.get("capture_scope") != "crate":
        raise OracleError("capture_scope must be 'crate' (whole-crate oracle)")
    if data.get("profile") not in ALLOWED_PROFILES:
        raise OracleError(f"unsupported profile: {data.get('profile')!r}")
    if not isinstance(data.get("target"), str) or not data["target"]:
        raise OracleError("target must be a non-empty string")
    if "tier_b_corpus_sha256" in data:
        _validate_hex(
            data.get("tier_b_corpus_sha256"), HEX64_RE, "tier_b_corpus_sha256"
        )
    if "tier_b_min_counts" in data:
        min_counts = data.get("tier_b_min_counts")
        if not isinstance(min_counts, dict) or not min_counts:
            raise OracleError(
                "pin field 'tier_b_min_counts' must be a non-empty object"
            )
        for kind, floor in min_counts.items():
            if kind not in ALLOWED_TIER_B_KINDS:
                raise OracleError(
                    f"unsupported kind in tier_b_min_counts: {kind!r}"
                )
            _validate_positive_int(floor, f"tier_b_min_counts.{kind}")
    return data


def _validate_https_host(
    url: str, *, allowed_hosts: frozenset[str] = ALLOWED_ARCHIVE_HOSTS
) -> None:
    parsed = urllib.parse.urlparse(url)
    if parsed.scheme != "https":
        raise OracleError(f"refusing non-HTTPS archive URL: {url!r}")
    if parsed.hostname not in allowed_hosts:
        raise OracleError(
            f"refusing archive host {parsed.hostname!r} (allowed: "
            f"{sorted(allowed_hosts)})"
        )


class _PinnedHttpsRedirectHandler(urllib.request.HTTPRedirectHandler):
    """Fail closed on any redirect leaving HTTPS or allowed GitHub hosts."""

    def __init__(
        self, *, allowed_hosts: frozenset[str] = ALLOWED_ARCHIVE_HOSTS
    ) -> None:
        super().__init__()
        self._allowed_hosts = allowed_hosts

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        resolved = urllib.parse.urljoin(req.full_url, newurl)
        _validate_https_host(resolved, allowed_hosts=self._allowed_hosts)
        return super().redirect_request(req, fp, code, msg, headers, resolved)


def _fetch_pinned_github_json(
    url: str,
    *,
    deadline: float,
    max_bytes: int = MAX_PIN_BYTES,
) -> dict[str, object]:
    """Fetch bounded JSON from `api.github.com` under a wall-clock deadline."""
    _validate_https_host(url, allowed_hosts=ALLOWED_API_HOSTS)
    opener = urllib.request.build_opener(
        _PinnedHttpsRedirectHandler(allowed_hosts=ALLOWED_API_HOSTS)
    )
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": "anneal-miri-ub-oracle/1",
            "Accept": "application/vnd.github+json",
        },
    )
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise OracleError(f"upstream linkage check exceeded wall-clock deadline: {url}")
    buf = bytearray()
    try:
        with opener.open(req, timeout=remaining) as resp:
            _validate_https_host(resp.geturl(), allowed_hosts=ALLOWED_API_HOSTS)
            while True:
                rem = deadline - time.monotonic()
                if rem <= 0:
                    raise OracleError(
                        f"upstream linkage check exceeded wall-clock deadline: {url}"
                    )
                raw_sock = getattr(getattr(resp, "fp", None), "raw", None)
                sock = getattr(raw_sock, "_sock", None)
                if sock is not None and hasattr(sock, "settimeout"):
                    sock.settimeout(rem)
                chunk = resp.read(DOWNLOAD_CHUNK_BYTES)
                if time.monotonic() > deadline:
                    raise OracleError(
                        f"upstream linkage check exceeded wall-clock deadline: {url}"
                    )
                if not chunk:
                    break
                if len(buf) + len(chunk) > max_bytes:
                    raise OracleError(
                        f"upstream linkage JSON from '{url}' exceeds {max_bytes} B"
                    )
                buf.extend(chunk)
    except OracleError:
        raise
    except Exception as exc:
        raise OracleError(
            f"failed to query upstream linkage endpoint '{url}': {exc}"
        ) from exc
    try:
        parsed = json.loads(buf.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise OracleError(
            f"invalid JSON from upstream linkage endpoint '{url}': {exc}"
        ) from exc
    if not isinstance(parsed, dict):
        raise OracleError(
            f"expected JSON object from upstream linkage endpoint '{url}'"
        )
    return parsed


def _resolve_github_subtree_sha(
    repo: str,
    root_tree_sha: str,
    segments: tuple[str, ...],
    *,
    deadline: float,
) -> str:
    """Walk documented `/git/trees/{sha}` endpoints one segment at a time."""
    cur_sha = root_tree_sha
    walked: list[str] = []
    for seg in segments:
        tree_obj = _fetch_pinned_github_json(
            f"https://api.github.com/repos/{repo}/git/trees/{cur_sha}",
            deadline=deadline,
        )
        entries = tree_obj.get("tree")
        if not isinstance(entries, list):
            raise OracleError(f"{repo} tree {cur_sha} missing 'tree' list")
        match_sha: str | None = None
        for entry in entries:
            if (
                isinstance(entry, dict)
                and entry.get("path") == seg
                and entry.get("type") == "tree"
                and isinstance(entry.get("sha"), str)
                and HEX40_RE.fullmatch(entry["sha"])
            ):
                match_sha = entry["sha"]
                break
        walked.append(seg)
        if match_sha is None:
            raise OracleError(
                f"{repo} tree {root_tree_sha} missing subtree "
                f"'{'/'.join(walked)}'"
            )
        cur_sha = match_sha
    return cur_sha


def verify_rustc_miri_linkage(
    pin: dict[str, object], *, timeout_secs: float = 30.0
) -> None:
    """Verify upstream `rust-lang/rust@rustc_commit` matches `miri_commit` trees.

    Uses only documented 40-char SHA Git Data API endpoints (`/git/commits/{sha}`
    and `/git/trees/{sha}`) over pinned HTTPS `api.github.com` to confirm:
    1. Walking `src/tools/miri` from `rust-lang/rust@<rustc_commit>`'s root
       tree yields `pin["miri_tree_sha"]`.
    2. Walking `tests/fail` (and `tests/fail-dep` when configured) under that
       subtree matches `pin["fail_tree_sha"]` (and `pin["fail_dep_tree_sha"]`).
    3. `rust-lang/miri@<miri_commit>`'s commit root tree SHA equals
       `pin["miri_tree_sha"]`, cryptographically binding the Miri pin to the
       pinned `rustc_commit` subtree.
    """
    rustc_commit = str(pin["rustc_commit"])
    miri_commit = str(pin["miri_commit"])
    expected_miri_tree = str(pin["miri_tree_sha"])
    subdirs = set(pin["extract_subdirs"])  # type: ignore[arg-type]
    deadline = time.monotonic() + timeout_secs

    rustc_commit_obj = _fetch_pinned_github_json(
        f"https://api.github.com/repos/rust-lang/rust/git/commits/{rustc_commit}",
        deadline=deadline,
    )
    rustc_tree_meta = rustc_commit_obj.get("tree")
    rustc_root_sha = (
        rustc_tree_meta.get("sha") if isinstance(rustc_tree_meta, dict) else None
    )
    if not isinstance(rustc_root_sha, str) or not HEX40_RE.fullmatch(rustc_root_sha):
        raise OracleError(
            f"rust-lang/rust@{rustc_commit} git commit missing valid root tree SHA"
        )

    actual_rustc_miri_sha = _resolve_github_subtree_sha(
        "rust-lang/rust", rustc_root_sha, ("src", "tools", "miri"), deadline=deadline
    )
    if not hmac.compare_digest(actual_rustc_miri_sha, expected_miri_tree):
        raise OracleError(
            f"rust-lang/rust@{rustc_commit}:src/tools/miri tree SHA mismatch: "
            f"expected {expected_miri_tree}, got {actual_rustc_miri_sha!r}"
        )

    tests_tree_sha = _resolve_github_subtree_sha(
        "rust-lang/rust", actual_rustc_miri_sha, ("tests",), deadline=deadline
    )
    expected_subtrees: list[tuple[str, str]] = [("fail", str(pin["fail_tree_sha"]))]
    if "tests/fail-dep" in subdirs:
        expected_subtrees.append(("fail-dep", str(pin["fail_dep_tree_sha"])))
    for sub_name, expected_sha in expected_subtrees:
        actual_sub = _resolve_github_subtree_sha(
            "rust-lang/rust", tests_tree_sha, (sub_name,), deadline=deadline
        )
        if not hmac.compare_digest(actual_sub, expected_sha):
            raise OracleError(
                f"rust-lang/rust@{rustc_commit}:src/tools/miri/tests/{sub_name} "
                f"tree SHA mismatch: expected {expected_sha}, got {actual_sub!r}"
            )

    miri_commit_obj = _fetch_pinned_github_json(
        f"https://api.github.com/repos/rust-lang/miri/git/commits/{miri_commit}",
        deadline=deadline,
    )
    miri_tree_meta = miri_commit_obj.get("tree")
    actual_miri_root_sha = (
        miri_tree_meta.get("sha") if isinstance(miri_tree_meta, dict) else None
    )
    if not isinstance(actual_miri_root_sha, str) or not hmac.compare_digest(
        actual_miri_root_sha, expected_miri_tree
    ):
        raise OracleError(
            f"rust-lang/miri@{miri_commit} root tree SHA mismatch against "
            f"rust-lang/rust@{rustc_commit}:src/tools/miri: "
            f"expected {expected_miri_tree}, got {actual_miri_root_sha!r}"
        )


def copy_and_verify_archive_sha256(
    src_path: Path,
    dest_path: Path,
    expected_sha256: str,
    *,
    max_bytes: int = MAX_ARCHIVE_BYTES,
) -> str:
    """Copy a local archive into a private temp file while verifying SHA-256.

    Opens `src_path` once with `O_NOFOLLOW | O_NONBLOCK`, validates `fstat`
    on the resulting descriptor (rejecting symlinks and special files such as
    FIFOs without blocking or check-then-open TOCTOU), and hashes while copying
    so verification and extraction see identical bytes.
    """
    flags = (
        os.O_RDONLY
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    try:
        fd = os.open(src_path, flags)
    except OSError as exc:
        if exc.errno == errno.ELOOP:
            raise OracleError(
                f"archive path must be a regular non-symlink file: {src_path}"
            ) from exc
        raise OracleError(
            f"failed opening archive '{src_path}': {exc}"
        ) from exc

    hasher = hashlib.sha256()
    total = 0
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise OracleError(
                f"archive path must be a regular non-symlink file: {src_path}"
            )
        if st.st_size > max_bytes:
            raise OracleError(
                f"archive '{src_path}' exceeds max allowed size ({max_bytes} B)"
            )
        with (
            os.fdopen(fd, "rb", closefd=False) as inp,
            dest_path.open("wb") as out,
        ):
            while True:
                chunk = inp.read(DOWNLOAD_CHUNK_BYTES)
                if not chunk:
                    break
                total += len(chunk)
                if total > max_bytes:
                    raise OracleError(
                        f"archive '{src_path}' exceeds max allowed size "
                        f"({max_bytes} B)"
                    )
                hasher.update(chunk)
                out.write(chunk)
    except OracleError:
        dest_path.unlink(missing_ok=True)
        raise
    except OSError as exc:
        dest_path.unlink(missing_ok=True)
        raise OracleError(f"failed reading archive '{src_path}': {exc}") from exc
    finally:
        os.close(fd)

    actual = hasher.hexdigest()
    if not hmac.compare_digest(actual, expected_sha256):
        dest_path.unlink(missing_ok=True)
        raise OracleError(
            f"archive SHA-256 mismatch for '{src_path}': "
            f"expected {expected_sha256}, got {actual}"
        )
    return actual


def download_verified_archive(
    url: str,
    expected_sha256: str,
    dest_path: Path,
    *,
    timeout_secs: float = 60.0,
    max_bytes: int = MAX_ARCHIVE_BYTES,
) -> str:
    """Download an archive over HTTPS, enforcing host, size, and SHA-256."""
    _validate_https_host(url)
    opener = urllib.request.build_opener(_PinnedHttpsRedirectHandler())
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "anneal-miri-ub-oracle/1"},
    )
    hasher = hashlib.sha256()
    total = 0
    deadline = time.monotonic() + timeout_secs
    try:
        with opener.open(req, timeout=timeout_secs) as resp:
            _validate_https_host(resp.geturl())
            with dest_path.open("wb") as out:
                while True:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        raise OracleError(
                            f"archive download exceeded {timeout_secs:.1f}s "
                            "wall-clock deadline"
                        )
                    raw_sock = getattr(getattr(resp, "fp", None), "raw", None)
                    sock = getattr(raw_sock, "_sock", None)
                    if sock is not None and hasattr(sock, "settimeout"):
                        sock.settimeout(remaining)
                    chunk = resp.read(DOWNLOAD_CHUNK_BYTES)
                    if time.monotonic() > deadline:
                        raise OracleError(
                            f"archive download exceeded {timeout_secs:.1f}s "
                            "wall-clock deadline"
                        )
                    if not chunk:
                        break
                    total += len(chunk)
                    if total > max_bytes:
                        raise OracleError(
                            f"downloaded archive exceeds {max_bytes} B ceiling"
                        )
                    hasher.update(chunk)
                    out.write(chunk)
    except OracleError:
        dest_path.unlink(missing_ok=True)
        raise
    except Exception as exc:
        dest_path.unlink(missing_ok=True)
        raise OracleError(f"failed to download '{url}': {exc}") from exc

    actual = hasher.hexdigest()
    if not hmac.compare_digest(actual, expected_sha256):
        dest_path.unlink(missing_ok=True)
        raise OracleError(
            f"downloaded archive SHA-256 mismatch: "
            f"expected {expected_sha256}, got {actual}"
        )
    return actual


def _validate_tar_member_path(raw_name: str, expected_top_dir: str) -> PurePosixPath:
    """Reject path traversal, absolute paths, Windows drives, and bad roots."""
    if not raw_name:
        raise OracleError("tar archive contains empty member name")
    if "\x00" in raw_name or "\\" in raw_name:
        raise OracleError(f"tar member contains forbidden character: {raw_name!r}")
    if raw_name.startswith("/") or raw_name.startswith("~"):
        raise OracleError(f"tar member has absolute or home path: {raw_name!r}")

    parts = raw_name.split("/")
    # GitHub tarballs include a trailing '/' on directory entries.
    if parts and parts[-1] == "":
        parts = parts[:-1]
    if not parts:
        raise OracleError(f"tar member normalizes to empty path: {raw_name!r}")
    for seg in parts:
        if seg in ("", ".", "..") or ":" in seg:
            raise OracleError(
                f"tar member contains forbidden path segment {seg!r}: {raw_name!r}"
            )
    if parts[0] != expected_top_dir:
        raise OracleError(
            f"tar member escapes expected top dir '{expected_top_dir}': {raw_name!r}"
        )
    return PurePosixPath(*parts)


def _compute_git_tree_sha1(tree_node: dict[str, object]) -> bytes:
    """Compute canonical Git tree SHA-1 (raw 20-byte digest) for a tree dict."""
    items: list[tuple[bytes, bytes, bytes, bytes]] = []
    for name, val in tree_node.items():
        name_bytes = name.encode("utf-8")
        if isinstance(val, dict):
            sub_sha = _compute_git_tree_sha1(val)
            items.append((name_bytes + b"/", b"40000", name_bytes, sub_sha))
        else:
            mode, blob_sha = val  # type: ignore[misc]
            items.append((name_bytes, mode, name_bytes, blob_sha))
    items.sort(key=lambda entry: entry[0])
    payload = b"".join(
        mode + b" " + name_b + b"\x00" + sha for _, mode, name_b, sha in items
    )
    header = f"tree {len(payload)}\x00".encode("ascii")
    return hashlib.sha1(header + payload).digest()


def _expected_archive_tree_shas(pin: dict[str, object]) -> dict[str, str]:
    expected = {"": str(pin["miri_tree_sha"])}
    subdirs = set(pin["extract_subdirs"])  # type: ignore[arg-type]
    if "tests/fail" in subdirs:
        expected["tests/fail"] = str(pin["fail_tree_sha"])
    if "tests/fail-dep" in subdirs:
        expected["tests/fail-dep"] = str(pin["fail_dep_tree_sha"])
    return expected


class _BoundedReadStream:
    """Read-only wrapper enforcing a hard decompressed byte ceiling.

    Bounds the raw stream fed to `tarfile.open(..., mode="r|")` so oversized
    compressed PAX or GNU extended headers fail closed before `tarfile` can
    materialize unbounded metadata in memory.
    """

    def __init__(self, inner: object, max_bytes: int) -> None:
        self._inner = inner
        self._max_bytes = max_bytes
        self._total = 0

    def read(self, size: int = -1) -> bytes:
        remaining = self._max_bytes - self._total
        if size is None or size < 0 or size > remaining + 1:
            to_read = remaining + 1
        else:
            to_read = size
        data: bytes = self._inner.read(to_read)  # type: ignore[attr-defined]
        self._total += len(data)
        if self._total > self._max_bytes:
            raise OracleError(
                f"decompressed tar stream exceeds {self._max_bytes} B cap"
            )
        return data


def safe_extract_miri_corpus(
    archive_path: Path,
    dest_dir: Path,
    *,
    expected_top_dir: str,
    extract_subdirs: list[str],
    expected_tree_shas: dict[str, str] | None = None,
) -> list[str]:
    """Safely extract `tests/fail*/*.rs` without ever calling `extractall`.

    Every member in the tarball is inspected for symlinks, hardlinks, device
    nodes, and path traversal before extracting the requested `.rs` files.
    When `expected_tree_shas` is supplied, recomputes exact Git tree SHA-1
    digests from the streamed archive members and fails closed on mismatch.
    """
    dest_root = dest_dir.resolve()
    dest_root.mkdir(parents=True, exist_ok=True)
    subdir_prefixes = tuple(s.rstrip("/") + "/" for s in extract_subdirs)

    extracted_relpaths: set[str] = set()
    seen_archive_files: set[str] = set()
    git_tree_root: dict[str, object] = {}
    total_extracted_bytes = 0

    try:
        with (
            archive_path.open("rb") as raw_fh,
            gzip.GzipFile(fileobj=raw_fh, mode="rb") as gz_fh,
            tarfile.open(
                fileobj=_BoundedReadStream(gz_fh, MAX_DECOMPRESSED_TAR_BYTES),
                mode="r|",
            ) as tf,
        ):
            member_count = 0
            while True:
                member = tf.next()
                if member is None:
                    break
                member_count += 1
                if member_count > MAX_TAR_MEMBERS:
                    raise OracleError(
                        f"tar archive exceeds {MAX_TAR_MEMBERS} members "
                        f"(cap {MAX_TAR_MEMBERS})"
                    )
                if (
                    member.issym()
                    or member.islnk()
                    or member.ischr()
                    or member.isblk()
                    or member.isfifo()
                    or member.isdev()
                ):
                    raise OracleError(
                        f"tar archive contains forbidden link/special member: "
                        f"{member.name!r} (type={member.type!r})"
                    )
                if not (member.isfile() or member.isdir()):
                    raise OracleError(
                        f"tar archive contains unsupported member type: "
                        f"{member.name!r} (type={member.type!r})"
                    )
                norm = _validate_tar_member_path(member.name, expected_top_dir)
                if not member.isfile():
                    tf.members.clear()
                    continue
                if len(norm.parts) < 2:
                    tf.members.clear()
                    continue
                inner_parts = norm.parts[1:]
                inner = PurePosixPath(*inner_parts).as_posix()
                if inner in seen_archive_files:
                    raise OracleError(
                        f"tar archive contains duplicate path '{inner}'"
                    )
                seen_archive_files.add(inner)

                is_extract_rs = inner.startswith(subdir_prefixes) and inner.endswith(
                    ".rs"
                )
                need_payload = is_extract_rs or (expected_tree_shas is not None)
                if not need_payload:
                    tf.members.clear()
                    continue

                if member.size < 0 or member.size > MAX_SINGLE_FILE_BYTES:
                    raise OracleError(
                        f"tar member '{inner}' exceeds single-file cap "
                        f"({member.size} > {MAX_SINGLE_FILE_BYTES})"
                    )
                fileobj = tf.extractfile(member)
                if fileobj is None:
                    raise OracleError(f"failed to extract tar member '{inner}'")
                payload = fileobj.read(MAX_SINGLE_FILE_BYTES + 1)
                if len(payload) > MAX_SINGLE_FILE_BYTES or len(payload) != member.size:
                    raise OracleError(
                        f"tar member '{inner}' decompressed size mismatch "
                        f"({len(payload)} vs header {member.size})"
                    )
                total_extracted_bytes += len(payload)
                if total_extracted_bytes > MAX_TOTAL_EXTRACTED_BYTES:
                    raise OracleError(
                        f"extracted corpus exceeds {MAX_TOTAL_EXTRACTED_BYTES} B cap"
                    )

                if expected_tree_shas is not None:
                    blob_header = f"blob {len(payload)}\x00".encode("ascii")
                    blob_sha = hashlib.sha1(blob_header + payload).digest()
                    mode = b"100755" if (member.mode & 0o111) else b"100644"
                    cur_node: dict[str, object] = git_tree_root
                    for seg in inner_parts[:-1]:
                        nxt = cur_node.get(seg)
                        if nxt is None:
                            nxt = {}
                            cur_node[seg] = nxt
                        elif not isinstance(nxt, dict):
                            raise OracleError(
                                f"tar archive path conflict at '{inner}'"
                            )
                        cur_node = nxt
                    if inner_parts[-1] in cur_node:
                        raise OracleError(
                            f"tar archive path conflict at '{inner}'"
                        )
                    cur_node[inner_parts[-1]] = (mode, blob_sha)

                if is_extract_rs:
                    rel_under_tests = inner[len("tests/"):]
                    extracted_relpaths.add(rel_under_tests)
                    dst = (dest_root / rel_under_tests).resolve()
                    try:
                        dst.relative_to(dest_root)
                    except ValueError as exc:
                        raise OracleError(
                            f"extracted path escapes destination root: {dst}"
                        ) from exc
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    with dst.open("xb") as out:
                        out.write(payload)
                tf.members.clear()
    except OracleError:
        raise
    except (tarfile.TarError, OSError, EOFError, zlib.error) as exc:
        raise OracleError(f"failed reading tar archive '{archive_path}': {exc}") from exc

    if expected_tree_shas is not None:
        for subtree_key, expected_sha in sorted(expected_tree_shas.items()):
            node: object = git_tree_root
            if subtree_key:
                for seg in subtree_key.split("/"):
                    if not isinstance(node, dict) or seg not in node:
                        raise OracleError(
                            f"tar archive missing expected subtree '{subtree_key}'"
                        )
                    node = node[seg]
            if not isinstance(node, dict):
                raise OracleError(
                    f"tar archive subtree '{subtree_key}' is not a directory"
                )
            actual_sha = _compute_git_tree_sha1(node).hex()
            if not hmac.compare_digest(actual_sha, expected_sha):
                label = subtree_key or "<root>"
                raise OracleError(
                    f"tar archive Git tree SHA-1 mismatch for '{label}': "
                    f"expected {expected_sha}, got {actual_sha}"
                )

    return sorted(extracted_relpaths)


def _stream_regular_file_sha256(
    path: str | Path,
    *,
    max_bytes: int,
    copy_to: Path | None = None,
    dir_fd: int | None = None,
    display_path: Path | None = None,
) -> tuple[str, int]:
    """Hash a regular, non-symlink file with bounded streaming I/O.

    Opens with `O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC` (anchored at `dir_fd`
    when provided so concurrent ancestor/entry renames cannot redirect the
    open), then verifies `S_ISREG` and `st_size` on the opened file descriptor
    before streaming chunks up to `max_bytes`. When `copy_to` is provided,
    writes the exact verified bytes to `copy_to` in the same read pass so
    callers never reopen the source path after hashing.
    """
    shown = display_path if display_path is not None else path
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    if hasattr(os, "O_NONBLOCK"):
        flags |= os.O_NONBLOCK
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        if dir_fd is not None:
            fd = os.open(path, flags, dir_fd=dir_fd)
        else:
            fd = os.open(path, flags)
    except OSError as exc:
        raise OracleError(f"failed to open corpus file '{shown}': {exc}") from exc
    out_fh = None
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise OracleError(f"corpus contains non-regular file: {shown}")
        if st.st_size > max_bytes:
            raise OracleError(
                f"corpus file exceeds size limit ({st.st_size} > {max_bytes}): {shown}"
            )
        if copy_to is not None:
            copy_to.parent.mkdir(parents=True, exist_ok=True)
            out_fh = copy_to.open("xb")
        hasher = hashlib.sha256()
        total = 0
        with os.fdopen(fd, "rb", closefd=False) as fh:
            while True:
                chunk = fh.read(DOWNLOAD_CHUNK_BYTES)
                if not chunk:
                    break
                total += len(chunk)
                if total > max_bytes:
                    raise OracleError(
                        f"corpus file exceeded size limit during read: {shown}"
                    )
                hasher.update(chunk)
                if out_fh is not None:
                    out_fh.write(chunk)
        return hasher.hexdigest(), total
    except BaseException:
        if out_fh is not None:
            out_fh.close()
            out_fh = None
        if copy_to is not None:
            copy_to.unlink(missing_ok=True)
        raise
    finally:
        if out_fh is not None:
            out_fh.close()
        os.close(fd)


def _walk_corpus_tree(
    corpus_dir: Path,
    subdirs: list[str],
    *,
    suffixes: tuple[str, ...],
    max_entries: int = MAX_CORPUS_DIR_ENTRIES,
    max_depth: int = MAX_CORPUS_DIR_DEPTH,
    max_matching_files: int | None = None,
    snapshot_dir: Path | None = None,
    label: str = "corpus",
) -> tuple[str, list[str]]:
    """Bounded streaming directory walk computing a canonical SHA-256 manifest.

    Anchors every directory descent and file open to open parent directory
    descriptors (`dir_fd` with `O_NOFOLLOW | O_DIRECTORY | O_CLOEXEC`) and
    `os.scandir`, rejecting symlinks, non-regular files (such as FIFOs),
    excessive entry counts or nesting depth, and byte-limit overflows. When
    `snapshot_dir` is given, copies every matched file into `snapshot_dir`
    during the single hashing pass so later processing never reopens
    `corpus_dir`.
    """
    if corpus_dir.is_symlink():
        raise OracleError(f"{label} directory must not be a symlink: {corpus_dir}")
    root = corpus_dir.resolve()
    snap_root = snapshot_dir.resolve() if snapshot_dir is not None else None
    if snap_root is not None:
        snap_root.mkdir(parents=True, exist_ok=True)
    entries: list[tuple[str, str]] = []
    total_bytes = 0
    seen_entries = 0
    dir_flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_CLOEXEC", 0)
    )
    try:
        root_fd = os.open(corpus_dir, dir_flags)
    except OSError as exc:
        if exc.errno == errno.ELOOP:
            raise OracleError(
                f"{label} directory must not be a symlink: {corpus_dir}"
            ) from exc
        raise OracleError(
            f"failed opening {label} directory '{corpus_dir}': {exc}"
        ) from exc

    try:
        for sub in subdirs:
            rel_sub = sub[len("tests/"):] if sub.startswith("tests/") else sub
            cur_path = root
            cur_fd = os.open(".", dir_flags, dir_fd=root_fd)
            try:
                if rel_sub:
                    for part in Path(rel_sub).parts:
                        if part in ("", "."):
                            continue
                        if part == ".." or "/" in part or "\\" in part:
                            raise OracleError(
                                f"unsafe {label} subdirectory component: {rel_sub}"
                            )
                        cur_path = cur_path / part
                        try:
                            next_fd = os.open(part, dir_flags, dir_fd=cur_fd)
                        except OSError as exc:
                            if exc.errno == errno.ELOOP:
                                raise OracleError(
                                    f"{label} directory must not be a symlink: "
                                    f"{cur_path}"
                                ) from exc
                            if exc.errno in (errno.ENOENT, errno.ENOTDIR):
                                raise OracleError(
                                    f"missing {label} subdirectory: {cur_path}"
                                ) from exc
                            raise OracleError(
                                f"failed opening {label} directory "
                                f"'{cur_path}': {exc}"
                            ) from exc
                        os.close(cur_fd)
                        cur_fd = next_fd
            except BaseException:
                os.close(cur_fd)
                raise

            stack: list[tuple[int, Path, int]] = [(cur_fd, cur_path, 0)]
            try:
                while stack:
                    dir_fd, cur_dir, depth = stack.pop()
                    try:
                        if depth > max_depth:
                            raise OracleError(
                                f"{label} directory exceeds max depth "
                                f"({max_depth}): {cur_dir}"
                            )
                        with os.scandir(dir_fd) as it:
                            for entry in it:
                                seen_entries += 1
                                if seen_entries > max_entries:
                                    raise OracleError(
                                        f"{label} directory exceeds max entry "
                                        f"limit ({max_entries})"
                                    )
                                epath = cur_dir / entry.name
                                if entry.is_symlink():
                                    raise OracleError(
                                        f"{label} contains forbidden symlink: "
                                        f"{epath}"
                                    )
                                if entry.is_dir(follow_symlinks=False):
                                    if depth + 1 > max_depth:
                                        raise OracleError(
                                            f"{label} directory exceeds max "
                                            f"depth ({max_depth}): {epath}"
                                        )
                                    try:
                                        child_fd = os.open(
                                            entry.name,
                                            dir_flags,
                                            dir_fd=dir_fd,
                                        )
                                    except OSError as exc:
                                        if exc.errno == errno.ELOOP:
                                            raise OracleError(
                                                f"{label} contains forbidden "
                                                f"symlink dir: {epath}"
                                            ) from exc
                                        raise OracleError(
                                            f"failed opening {label} directory "
                                            f"'{epath}': {exc}"
                                        ) from exc
                                    stack.append((child_fd, epath, depth + 1))
                                    continue
                                if not entry.name.endswith(suffixes):
                                    continue
                                if (
                                    max_matching_files is not None
                                    and len(entries) >= max_matching_files
                                ):
                                    raise OracleError(
                                        f"{label} file count mismatch: exceeds "
                                        f"expected {max_matching_files} files"
                                    )
                                rel = epath.relative_to(root).as_posix()
                                copy_dst = None
                                if snap_root is not None:
                                    copy_dst = (snap_root / rel).resolve()
                                    try:
                                        copy_dst.relative_to(snap_root)
                                    except ValueError as exc:
                                        raise OracleError(
                                            f"snapshot path escapes root: "
                                            f"{copy_dst}"
                                        ) from exc
                                digest, size = _stream_regular_file_sha256(
                                    entry.name,
                                    max_bytes=MAX_SINGLE_FILE_BYTES,
                                    copy_to=copy_dst,
                                    dir_fd=dir_fd,
                                    display_path=epath,
                                )
                                total_bytes += size
                                if total_bytes > MAX_TOTAL_EXTRACTED_BYTES:
                                    raise OracleError(
                                        f"{label} exceeds total size limit "
                                        f"({total_bytes} > "
                                        f"{MAX_TOTAL_EXTRACTED_BYTES})"
                                    )
                                entries.append((rel, digest))
                    finally:
                        os.close(dir_fd)
            finally:
                while stack:
                    rem_fd, _, _ = stack.pop()
                    os.close(rem_fd)
    finally:
        os.close(root_fd)

    entries.sort()
    manifest_text = "".join(f"{digest}  {rel}\n" for rel, digest in entries)
    manifest_sha = hashlib.sha256(manifest_text.encode("utf-8")).hexdigest()
    return manifest_sha, [rel for rel, _ in entries]


def compute_corpus_manifest_sha256(
    corpus_dir: Path,
    extract_subdirs: list[str],
    *,
    max_entries: int = MAX_CORPUS_DIR_ENTRIES,
    max_rs_files: int | None = None,
    snapshot_dir: Path | None = None,
) -> tuple[str, list[str]]:
    """Compute canonical SHA-256 over sorted `<sha256>  <relpath>\\n` `.rs`."""
    return _walk_corpus_tree(
        corpus_dir,
        extract_subdirs,
        suffixes=(".rs",),
        max_entries=max_entries,
        max_depth=MAX_CORPUS_DIR_DEPTH,
        max_matching_files=max_rs_files,
        snapshot_dir=snapshot_dir,
        label="corpus",
    )


def verify_corpus_manifest(
    corpus_dir: Path,
    pin: dict[str, object],
    *,
    snapshot_dir: Path | None = None,
) -> tuple[str, list[str]]:
    """Fail-closed check of extracted/local corpus file count and digest."""
    subdirs = list(pin["extract_subdirs"])  # type: ignore[arg-type]
    expected_count = int(pin["expected_file_count"])  # type: ignore[arg-type]
    actual_sha, files = compute_corpus_manifest_sha256(
        corpus_dir,
        subdirs,
        max_rs_files=expected_count,
        snapshot_dir=snapshot_dir,
    )
    if len(files) != expected_count:
        raise OracleError(
            f"corpus file count mismatch: expected {expected_count}, "
            f"found {len(files)}"
        )
    expected_sha = str(pin["corpus_manifest_sha256"])
    if not hmac.compare_digest(actual_sha, expected_sha):
        raise OracleError(
            f"corpus manifest SHA-256 mismatch: "
            f"expected {expected_sha}, got {actual_sha}"
        )
    return actual_sha, files


def parse_miri_headers(text: str) -> dict[str, object]:
    """Parse relevant `//@` ui_test directives from upstream Miri fail tests.

    Target and bitwidth filters (`only-target`, `ignore-target`,
    `ignore-bitwidth`) are keyed by optional `[rev]` qualifier just like
    `compile-flags`, and multiple `//@revisions:` lines accumulate rather
    than overwriting earlier declarations.
    """
    revisions: list[str] = []
    flags: dict[str | None, list[str]] = {None: []}
    only_targets: dict[str | None, list[list[str]]] = {None: []}
    ignore_targets: dict[str | None, list[list[str]]] = {None: []}
    ignore_bitwidth: dict[str | None, list[str]] = {None: []}

    for line in text.splitlines():
        match = MIRI_HEADER_RE.match(line.strip())
        if not match:
            continue
        rev, key, raw_val = match.group(1), match.group(2), match.group(3)
        val = raw_val.split("#", 1)[0].strip()
        if key == "revisions":
            for r in val.split():
                if r not in revisions:
                    revisions.append(r)
        elif key == "compile-flags":
            flags.setdefault(rev, []).extend(val.split())
        elif key == "only-target":
            only_targets.setdefault(rev, []).append(val.split())
        elif key == "ignore-target":
            ignore_targets.setdefault(rev, []).append(val.split())
        elif key == "ignore-bitwidth":
            ignore_bitwidth.setdefault(rev, []).extend(val.split())

    return {
        "revisions": revisions,
        "flags": flags,
        "only_targets": only_targets,
        "ignore_targets": ignore_targets,
        "ignore_bitwidth": ignore_bitwidth,
    }


def _target_bitwidth(target: str) -> str:
    """Return pointer width (`'32'` or `'64'`) inferred from a Rust target triple."""
    arch = target.split("-", 1)[0]
    if arch in {"i386", "i586", "i686", "wasm32", "riscv32", "arm", "armv7", "mips", "powerpc"} or arch.startswith(
        ("thumbv", "armv", "riscv32")
    ):
        return "32"
    return "64"


def harness_skip_reason(
    hdr: dict[str, object], target: str, revision: str | None = None
) -> str | None:
    """Return a target-mismatch skip reason for `target` and `revision`."""
    only_map: dict[str | None, list[list[str]]] = hdr["only_targets"]  # type: ignore[assignment]
    ignore_map: dict[str | None, list[list[str]]] = hdr["ignore_targets"]  # type: ignore[assignment]
    bitwidth_map: dict[str | None, list[str]] = hdr["ignore_bitwidth"]  # type: ignore[assignment]

    only_list = list(only_map.get(None, []))
    ignore_list = list(ignore_map.get(None, []))
    bitwidth_list = list(bitwidth_map.get(None, []))
    if revision is not None:
        only_list.extend(only_map.get(revision, []))
        ignore_list.extend(ignore_map.get(revision, []))
        bitwidth_list.extend(bitwidth_map.get(revision, []))

    for pats in only_list:
        if not any(p in target for p in pats):
            return f"only-target {' '.join(pats)}"
    for pats in ignore_list:
        if any(p in target for p in pats):
            return f"ignore-target {' '.join(pats)}"
    bw = _target_bitwidth(target)
    if bw in bitwidth_list:
        return f"ignore-bitwidth {bw}"
    return None


# Baseline rustc flags unconditionally enforced by `anneal-rustc-capture`
# (`anneal/trusted/rustc-capture/src/capture.rs`). A Miri fixture that requests
# one of these flags already runs under the exact requested setting.
_CAPTURE_FIXED_RUSTC_FLAGS: frozenset[str] = frozenset({
    "-Copt-level=0",
    "-Cdebug-assertions=no",
    "-Cdebug-assertions=off",
    "-Cdebug-assertions=false",
    "-Coverflow-checks=no",
    "-Coverflow-checks=off",
    "-Coverflow-checks=false",
    "-Zmir-opt-level=0",
})


def parse_compile_flags(flags: list[str]) -> tuple[str, str, list[str]]:
    """Extract edition and panic strategy; record unforwarded rustc flags."""
    edition = "2021"
    panic = "unwind"
    unforwarded: list[str] = []
    i = 0
    while i < len(flags):
        flag = flags[i]
        if flag.startswith("--edition"):
            if "=" in flag:
                edition = flag.split("=", 1)[1]
                i += 1
            elif i + 1 < len(flags):
                edition = flags[i + 1]
                i += 2
            else:
                unforwarded.append(flag)
                i += 1
            continue
        if flag in ("-C", "-Z") and i + 1 < len(flags):
            flag = flag + flags[i + 1]
            i += 1
        if flag == "-Cpanic=abort":
            panic = "abort"
        elif flag == "-Cpanic=unwind":
            panic = "unwind"
        elif flag in _CAPTURE_FIXED_RUSTC_FLAGS:
            pass
        elif not flag.startswith("-Zmiri-"):
            unforwarded.append(flag)
        i += 1
    if edition not in ("2015", "2018", "2021", "2024"):
        unforwarded.append(f"--edition={edition}")
        edition = "2021"
    return edition, panic, unforwarded


_PR_GET_DUMPABLE = 3
_PR_SET_DUMPABLE = 4
_PR_SET_NO_NEW_PRIVS = 38
_PR_SET_SECCOMP = 22
_SECCOMP_MODE_FILTER = 2
_BPF_LD_W_ABS = 0x20
_BPF_JMP_JEQ_K = 0x15
_BPF_JMP_JSET_K = 0x45
_BPF_RET_K = 0x06
_SECCOMP_RET_KILL_PROCESS = 0x80000000
_SECCOMP_RET_ERRNO = 0x00050000
_SECCOMP_RET_ALLOW = 0x7FFF0000
_X32_SYSCALL_BIT = 0x40000000
# Open flags requesting write access, creation, truncation, append, or
# anonymous temporary files (`__O_TMPFILE = 0x400000`, omitting `O_DIRECTORY`
# so read-only `O_RDONLY | O_DIRECTORY` opens remain permitted on both x86_64
# and aarch64).
_OPEN_WRITE_FLAGS = (
    0x000001  # O_WRONLY
    | 0x000002  # O_RDWR
    | 0x000040  # O_CREAT
    | 0x000200  # O_TRUNC
    | 0x000400  # O_APPEND
    | 0x400000  # __O_TMPFILE (without O_DIRECTORY)
)
_CONFINED_EXEC_FLAG = "--_confined-exec"
CONFINEMENT_MODES = frozenset({"eval", "capture"})

# Linux Landlock LSM syscall numbers (identical on x86_64 and aarch64) and
# ABI v1..v5 filesystem access bitmasks.
_SYS_LANDLOCK_CREATE_RULESET = 444
_SYS_LANDLOCK_ADD_RULE = 445
_SYS_LANDLOCK_RESTRICT_SELF = 446
_LANDLOCK_CREATE_RULESET_VERSION = 1
_LANDLOCK_RULE_PATH_BENEATH = 1
_LANDLOCK_ACCESS_FS_EXECUTE = 1 << 0
_LANDLOCK_ACCESS_FS_WRITE_FILE = 1 << 1
_LANDLOCK_ACCESS_FS_READ_FILE = 1 << 2
_LANDLOCK_ACCESS_FS_READ_DIR = 1 << 3
_LANDLOCK_ACCESS_FS_REMOVE_DIR = 1 << 4
_LANDLOCK_ACCESS_FS_REMOVE_FILE = 1 << 5
_LANDLOCK_ACCESS_FS_MAKE_DIR = 1 << 7
_LANDLOCK_ACCESS_FS_MAKE_REG = 1 << 8
_LANDLOCK_ACCESS_FS_ABI1_ALL = (1 << 13) - 1
_LANDLOCK_ACCESS_FS_REFER = 1 << 13
_LANDLOCK_ACCESS_FS_TRUNCATE = 1 << 14
_LANDLOCK_ACCESS_FS_IOCTL_DEV = 1 << 15
_LANDLOCK_DIR_RO_EXEC = (
    _LANDLOCK_ACCESS_FS_EXECUTE
    | _LANDLOCK_ACCESS_FS_READ_FILE
    | _LANDLOCK_ACCESS_FS_READ_DIR
)
_LANDLOCK_DIR_RO = (
    _LANDLOCK_ACCESS_FS_READ_FILE | _LANDLOCK_ACCESS_FS_READ_DIR
)
_LANDLOCK_DIR_RW_BASE = (
    _LANDLOCK_ACCESS_FS_READ_FILE
    | _LANDLOCK_ACCESS_FS_READ_DIR
    | _LANDLOCK_ACCESS_FS_WRITE_FILE
    | _LANDLOCK_ACCESS_FS_REMOVE_DIR
    | _LANDLOCK_ACCESS_FS_REMOVE_FILE
    | _LANDLOCK_ACCESS_FS_MAKE_REG
    | _LANDLOCK_ACCESS_FS_MAKE_DIR
)
_LANDLOCK_FILE_RO_EXEC = (
    _LANDLOCK_ACCESS_FS_EXECUTE | _LANDLOCK_ACCESS_FS_READ_FILE
)
_LANDLOCK_FILE_RO = _LANDLOCK_ACCESS_FS_READ_FILE
_LANDLOCK_FILE_RW_BASE = (
    _LANDLOCK_ACCESS_FS_READ_FILE | _LANDLOCK_ACCESS_FS_WRITE_FILE
)
_CLONE_NEWNS = 0x00020000
_CLONE_NEWUSER = 0x10000000
_CLONE_NEWPID = 0x20000000
_CLONE_NEWNET = 0x40000000
# All Linux namespace-creation `clone(2)` flags (identical on x86_64/aarch64):
# CLONE_NEWTIME | NEWNS | NEWCGROUP | NEWUTS | NEWIPC | NEWUSER | NEWPID |
# NEWNET.
_CLONE_FORBIDDEN_NS_FLAGS = 0x7E020080
_MS_RDONLY = 1
_MS_NOSUID = 2
_MS_NODEV = 4
_MS_NOEXEC = 8
_MS_REMOUNT = 32
_MS_NOATIME = 1024
_MS_NODIRATIME = 2048
_MS_BIND = 4096
_MS_REC = 16384
_MS_PRIVATE = 1 << 18
_MS_RELATIME = 1 << 21
_MNT_DETACH = 2
_ST_TO_MS_FLAGS = (
    (getattr(os, "ST_NOSUID", 0x2), _MS_NOSUID),
    (getattr(os, "ST_NODEV", 0x4), _MS_NODEV),
    (getattr(os, "ST_NOEXEC", 0x8), _MS_NOEXEC),
    (getattr(os, "ST_NOATIME", 0x400), _MS_NOATIME),
    (getattr(os, "ST_NODIRATIME", 0x800), _MS_NODIRATIME),
    (getattr(os, "ST_RELATIME", 0x1000), _MS_RELATIME),
)
_LANDLOCK_SYSTEM_RO_EXEC_DIRS = (
    "/usr",
    "/lib",
    "/lib64",
    "/nix/store",
    "/opt/anneal-nix/runtime-libs",
)
_LANDLOCK_SYSTEM_RO_PATHS = (
    "/etc/ld.so.cache",
    "/etc/ld.so.conf",
    "/etc/ld.so.conf.d",
    "/dev/null",
    "/dev/zero",
    "/dev/urandom",
)

# Strict default-deny seccomp allowlists for both `eval` and `capture` modes:
# every syscall outside the audited allowlist (including `socket`/`socketpair`,
# `eventfd*`, `epoll_*`, `inotify_*`, `timerfd_*`, `signalfd_*`, `memfd_*`,
# `io_uring_*`, SysV/POSIX IPC, `openat2`, `setsid`/`setpgid`, `unshare`/
# `setns`, `kill`, `ptrace`, `process_vm_*`, `pidfd_*`, `mount`/`umount2`)
# returns `EPERM`. `prlimit64` is admitted only for `pid == 0` (self) and
# `fcntl` only for `{F_DUPFD, F_GETFD, F_SETFD, F_GETFL, F_DUPFD_CLOEXEC}` plus
# `F_SETFL` with `O_ASYNC` clear (zero upper 32 bits). In `eval` mode,
# `open`/`openat` require `_OPEN_WRITE_FLAGS` clear and `ioctl` admits only
# `FIOCLEX`; all task/thread/pipe creation is denied. In `capture` mode,
# `clone3` returns `ENOSYS` so glibc falls back to `clone`, where any namespace
# flag in `_CLONE_FORBIDDEN_NS_FLAGS` (or non-zero upper 32 bits) returns
# `EPERM`; `ioctl` admits only `{FIOCLEX, FIONCLEX, FIONBIO}` and `prctl`
# admits only `{PR_SET_NAME, PR_GET_NAME}` (zero upper 32 bits).
_IOCTL_FIOCLEX = 0x5451  # identical on Linux x86_64 and aarch64
_IOCTL_CAPTURE_ALLOWED = (
    0x5451,  # FIOCLEX
    0x5450,  # FIONCLEX
    0x5421,  # FIONBIO
)
_PRCTL_CAPTURE_ALLOWED = (
    15,  # PR_SET_NAME
    16,  # PR_GET_NAME
)
_FCNTL_SAFE_CMDS = (
    0,     # F_DUPFD
    1,     # F_GETFD
    2,     # F_SETFD
    3,     # F_GETFL
    1030,  # F_DUPFD_CLOEXEC
)
_FCNTL_F_SETFL = 4
_FCNTL_O_ASYNC = 0x2000  # FASYNC on Linux x86_64 and aarch64
_X86_64_SECCOMP_SPEC: dict[str, object] = {
    "audit_arch": 0xC000003E,  # AUDIT_ARCH_X86_64
    "reject_x32": True,
    "open_nr": 2,  # open(pathname, flags, mode) -> args[1] at offset 24
    "openat_nr": 257,  # openat(dirfd, pathname, flags, mode) -> args[2] at 32
    "prlimit64_nr": 302,  # prlimit64(pid, resource, new, old) -> args[0] at 16
    "ioctl_nr": 16,  # ioctl(fd, request, ...) -> args[1] at offset 24
    "fcntl_nr": 72,  # fcntl(fd, cmd, arg) -> args[1] at 24, args[2] at 32
    "clone_nr": 56,  # clone(flags, ...) -> args[0] at offset 16
    "clone3_nr": 435,  # clone3(...) -> ENOSYS (glibc falls back to clone)
    "prctl_nr": 157,  # prctl(option, ...) -> args[0] at offset 16
    "eval_allow_nrs": (
        0,    # read
        1,    # write
        3,    # close
        4,    # stat
        5,    # fstat
        6,    # lstat
        7,    # poll
        8,    # lseek
        9,    # mmap
        10,   # mprotect
        11,   # munmap
        12,   # brk
        13,   # rt_sigaction
        14,   # rt_sigprocmask
        15,   # rt_sigreturn
        17,   # pread64
        20,   # writev
        21,   # access
        24,   # sched_yield
        25,   # mremap
        28,   # madvise
        35,   # nanosleep
        39,   # getpid
        59,   # execve
        60,   # exit
        63,   # uname
        79,   # getcwd
        89,   # readlink
        96,   # gettimeofday
        97,   # getrlimit
        99,   # sysinfo
        102,  # getuid
        104,  # getgid
        107,  # geteuid
        108,  # getegid
        110,  # getppid
        131,  # sigaltstack
        137,  # statfs
        138,  # fstatfs
        158,  # arch_prctl
        186,  # gettid
        202,  # futex
        204,  # sched_getaffinity
        217,  # getdents64
        218,  # set_tid_address
        228,  # clock_gettime
        230,  # clock_nanosleep
        231,  # exit_group
        262,  # newfstatat
        267,  # readlinkat
        269,  # faccessat
        271,  # ppoll
        273,  # set_robust_list
        318,  # getrandom
        332,  # statx
        334,  # rseq
        439,  # faccessat2
    ),
    "capture_extra_allow_nrs": (
        2,    # open (Landlock ABI >= 3 enforces RO vs RW work tmpfs)
        18,   # pwrite64
        19,   # readv
        22,   # pipe (bounded by RLIMIT_NOFILE)
        32,   # dup
        33,   # dup2
        61,   # wait4
        76,   # truncate (mediated by Landlock ABI >= 3)
        77,   # ftruncate (mediated by Landlock ABI >= 3)
        80,   # chdir
        81,   # fchdir
        82,   # rename
        83,   # mkdir
        84,   # rmdir
        87,   # unlink
        91,   # fchmod
        95,   # umask
        200,  # tkill (confined to isolated CLONE_NEWPID namespace)
        229,  # clock_getres
        234,  # tgkill (confined to isolated CLONE_NEWPID namespace)
        247,  # waitid
        257,  # openat (Landlock ABI >= 3 enforces RO vs RW work tmpfs)
        258,  # mkdirat
        263,  # unlinkat
        264,  # renameat
        292,  # dup3
        293,  # pipe2 (bounded by RLIMIT_NOFILE)
        295,  # preadv
        296,  # pwritev
        316,  # renameat2
        326,  # copy_file_range
    ),
}

_AARCH64_SECCOMP_SPEC: dict[str, object] = {
    "audit_arch": 0xC00000B7,  # AUDIT_ARCH_AARCH64
    "reject_x32": False,
    "open_nr": None,
    "openat_nr": 56,  # openat(dirfd, pathname, flags, mode) -> args[2] at 32
    "prlimit64_nr": 261,  # prlimit64(pid, resource, new, old) -> args[0] at 16
    "ioctl_nr": 29,  # ioctl(fd, request, ...) -> args[1] at offset 24
    "fcntl_nr": 25,  # fcntl(fd, cmd, arg) -> args[1] at 24, args[2] at 32
    "clone_nr": 220,  # clone(flags, ...) -> args[0] at offset 16
    "clone3_nr": 435,  # clone3(...) -> ENOSYS (glibc falls back to clone)
    "prctl_nr": 167,  # prctl(option, ...) -> args[0] at offset 16
    "eval_allow_nrs": (
        17,   # getcwd
        43,   # statfs
        44,   # fstatfs
        48,   # faccessat
        57,   # close
        61,   # getdents64
        62,   # lseek
        63,   # read
        64,   # write
        66,   # writev
        67,   # pread64
        73,   # ppoll
        78,   # readlinkat
        79,   # newfstatat
        80,   # fstat
        93,   # exit
        94,   # exit_group
        96,   # set_tid_address
        98,   # futex
        99,   # set_robust_list
        101,  # nanosleep
        113,  # clock_gettime
        115,  # clock_nanosleep
        123,  # sched_getaffinity
        124,  # sched_yield
        132,  # sigaltstack
        134,  # rt_sigaction
        135,  # rt_sigprocmask
        139,  # rt_sigreturn
        160,  # uname
        163,  # getrlimit
        169,  # gettimeofday
        172,  # getpid
        173,  # getppid
        174,  # getuid
        175,  # geteuid
        176,  # getgid
        177,  # getegid
        178,  # gettid
        179,  # sysinfo
        214,  # brk
        215,  # munmap
        216,  # mremap
        221,  # execve
        222,  # mmap
        226,  # mprotect
        233,  # madvise
        278,  # getrandom
        291,  # statx
        293,  # rseq
        439,  # faccessat2
    ),
    "capture_extra_allow_nrs": (
        23,   # dup
        24,   # dup3
        34,   # mkdirat
        35,   # unlinkat
        38,   # renameat
        45,   # truncate (mediated by Landlock ABI >= 3)
        46,   # ftruncate (mediated by Landlock ABI >= 3)
        49,   # chdir
        50,   # fchdir
        52,   # fchmod (RO bind-mounts block fchmod on sysroot/src with EROFS)
        56,   # openat (Landlock ABI >= 3 enforces RO vs RW work tmpfs)
        59,   # pipe2 (bounded by RLIMIT_NOFILE)
        65,   # readv
        68,   # pwrite64
        69,   # preadv
        70,   # pwritev
        95,   # waitid
        114,  # clock_getres
        130,  # tkill (confined to isolated CLONE_NEWPID namespace)
        131,  # tgkill (confined to isolated CLONE_NEWPID namespace)
        166,  # umask
        260,  # wait4
        276,  # renameat2
        285,  # copy_file_range
    ),
}

_SECCOMP_ARCH_TABLE: dict[str, dict[str, object]] = {
    "x86_64": _X86_64_SECCOMP_SPEC,
    "amd64": _X86_64_SECCOMP_SPEC,
    "aarch64": _AARCH64_SECCOMP_SPEC,
    "arm64": _AARCH64_SECCOMP_SPEC,
}


class _SockFprog(ctypes.Structure):
    _fields_ = [("len", ctypes.c_ushort), ("filter", ctypes.c_void_p)]


def _harden_parent_process() -> None:
    """Mark the parent harness non-dumpable so children cannot read `/proc/$PPID/environ`.

    Linux sets `/proc/<pid>/environ` (and `mem`/`maps`/`fd`) ownership to
    `root:root` mode `0400` when `PR_SET_DUMPABLE` is `0`, preventing same-UID
    subprocesses from reading stripped GitHub Actions tokens out of the parent.
    """
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(_PR_SET_DUMPABLE, 0, 0, 0, 0) != 0:
        err = ctypes.get_errno()
        raise OracleError(f"prctl(PR_SET_DUMPABLE, 0) failed: errno={err}")
    if libc.prctl(_PR_GET_DUMPABLE, 0, 0, 0, 0) != 0:
        raise OracleError(
            "parent process remained dumpable after prctl(PR_SET_DUMPABLE, 0)"
        )


def _probe_landlock_abi() -> int:
    """Return the active Linux Landlock ABI version (>= 1) or fail closed."""
    libc = ctypes.CDLL(None, use_errno=True)
    abi = int(
        libc.syscall(
            _SYS_LANDLOCK_CREATE_RULESET,
            0,
            0,
            _LANDLOCK_CREATE_RULESET_VERSION,
        )
    )
    if abi < 1:
        err = ctypes.get_errno()
        raise OracleError(
            f"Linux Landlock LSM is unavailable (abi={abi}, errno={err}); "
            "refusing to run evaluator without filesystem/proc isolation"
        )
    return abi


def _elf_pt_interp(exe_path: Path) -> Path | None:
    """Return the ELF64 `PT_INTERP` dynamic linker path for `exe_path`, if any."""
    try:
        with exe_path.open("rb") as fh:
            ehdr = fh.read(64)
            if len(ehdr) < 64 or ehdr[:4] != b"\x7fELF" or ehdr[4] != 2 or ehdr[5] != 1:
                return None
            e_phoff = struct.unpack_from("<Q", ehdr, 32)[0]
            e_phentsize, e_phnum = struct.unpack_from("<HH", ehdr, 54)
            if e_phentsize < 56 or e_phnum == 0 or e_phnum > 128:
                return None
            fh.seek(e_phoff)
            phdrs = fh.read(e_phentsize * e_phnum)
            for i in range(e_phnum):
                off = i * e_phentsize
                if off + 56 > len(phdrs):
                    break
                p_type = struct.unpack_from("<I", phdrs, off)[0]
                if p_type == 3:  # PT_INTERP
                    p_offset = struct.unpack_from("<Q", phdrs, off + 8)[0]
                    p_filesz = struct.unpack_from("<Q", phdrs, off + 32)[0]
                    if 0 < p_filesz <= 4096:
                        fh.seek(p_offset)
                        raw = fh.read(p_filesz).split(b"\x00", 1)[0]
                        if raw:
                            return Path(os.fsdecode(raw))
                    return None
    except OSError:
        return None
    return None


def _shebang_interpreter(exe_path: Path) -> Path | None:
    """Return the `#!` interpreter binary path for `exe_path`, if any."""
    try:
        with exe_path.open("rb") as fh:
            line = fh.readline(256)
        if not line.startswith(b"#!"):
            return None
        parts = line[2:].strip().split()
        if not parts:
            return None
        return Path(os.fsdecode(parts[0]))
    except OSError:
        return None


def _is_script_or_python(target_exe: Path) -> bool:
    """Return True if `target_exe` is the Python interpreter or a `#!` script."""
    try:
        if target_exe.resolve() == Path(sys.executable).resolve():
            return True
    except OSError:
        pass
    return _shebang_interpreter(target_exe) is not None


def _collect_landlock_read_paths(
    target_exe: Path,
    read_only_paths: list[Path],
    read_only_exec_paths: list[Path] = (),  # type: ignore[assignment]
) -> tuple[list[tuple[Path, bool]], list[tuple[Path, bool]]]:
    """Return `(ro_exec_entries, ro_entries)` of `(path, required)` pairs.

    Shared single source of truth between Landlock read-only rules and
    `capture`-mode read-only bind-mounts so every external readable path
    accessible under Landlock is also read-only at the VFS mount layer.
    """
    ro_exec_entries: list[tuple[Path, bool]] = [
        (Path(sys_dir), False) for sys_dir in _LANDLOCK_SYSTEM_RO_EXEC_DIRS
    ]
    ro_entries: list[tuple[Path, bool]] = [
        (Path(sys_ro), False) for sys_ro in _LANDLOCK_SYSTEM_RO_PATHS
    ]
    if _is_script_or_python(target_exe):
        for py_root in sorted(
            {
                Path(sys.executable),
                Path(sys.executable).resolve(),
                Path(sys.prefix),
                Path(sys.prefix).resolve(),
                Path(sys.base_prefix),
                Path(sys.base_prefix).resolve(),
            }
        ):
            ro_exec_entries.append((py_root, False))
        shebang = _shebang_interpreter(target_exe)
        if shebang is not None:
            ro_exec_entries.append((shebang, False))
            sb_interp = _elf_pt_interp(shebang)
            if sb_interp is not None:
                ro_exec_entries.append((sb_interp, False))
    interp = _elf_pt_interp(target_exe)
    if interp is not None:
        ro_exec_entries.append((interp, False))
    ro_exec_entries.append((target_exe, True))
    for ro_exec in read_only_exec_paths:
        ro_exec_entries.append((ro_exec, True))
    for ro_path in read_only_paths:
        ro_entries.append((ro_path, True))
    return ro_exec_entries, ro_entries


def _install_landlock(
    target_exe: Path,
    read_only_paths: list[Path],
    *,
    read_only_exec_paths: list[Path] = (),  # type: ignore[assignment]
    read_write_paths: list[Path] = (),  # type: ignore[assignment]
    allow_proc_self: bool = False,
    require_truncate_mediation: bool = False,
) -> None:
    """Confine children to a Landlock filesystem allowlist.

    Grants read-only/exec access strictly to standard dynamic-linker runtime
    paths, `target_exe`, and explicit `read_only_exec_paths`, read-only access
    to `read_only_paths`, and narrow read-write access (no `EXECUTE`, no device
    nodes, no symlinks/FIFOs/sockets) strictly to `read_write_paths`. Denies
    `/proc` enumeration and all other paths so children cannot inspect parent
    environments or mutate the checkout, home directory, or sibling workers.
    When `require_truncate_mediation=True` (used in `capture` mode where
    `truncate`/`ftruncate` are permitted inside the work tmpfs), fails closed
    unless Landlock ABI >= 3 is active so read-only paths cannot be truncated.
    """
    abi = _probe_landlock_abi()
    if require_truncate_mediation:
        _assert_capture_non_root_uid()
        if abi < 3:
            raise OracleError(
                "capture confinement requires Linux Landlock ABI >= 3 for "
                f"truncate mediation (got ABI {abi})"
            )
    handled = _LANDLOCK_ACCESS_FS_ABI1_ALL
    if abi >= 2:
        handled |= _LANDLOCK_ACCESS_FS_REFER
    if abi >= 3:
        handled |= _LANDLOCK_ACCESS_FS_TRUNCATE
    if abi >= 5:
        handled |= _LANDLOCK_ACCESS_FS_IOCTL_DEV

    dir_rw = _LANDLOCK_DIR_RW_BASE
    file_rw = _LANDLOCK_FILE_RW_BASE
    if abi >= 2:
        dir_rw |= _LANDLOCK_ACCESS_FS_REFER
    if abi >= 3:
        dir_rw |= _LANDLOCK_ACCESS_FS_TRUNCATE
        file_rw |= _LANDLOCK_ACCESS_FS_TRUNCATE

    libc = ctypes.CDLL(None, use_errno=True)
    attr = ctypes.create_string_buffer(struct.pack("<Q", handled))
    ruleset_fd = int(libc.syscall(_SYS_LANDLOCK_CREATE_RULESET, attr, 8, 0))
    if ruleset_fd < 0:
        err = ctypes.get_errno()
        raise OracleError(f"landlock_create_ruleset failed: errno={err}")

    def _add_rule(
        path: Path, *, allow_exec: bool, allow_write: bool, required: bool
    ) -> None:
        if not path.exists():
            if required:
                raise OracleError(f"Landlock allowed path does not exist: {path}")
            return
        o_path = getattr(os, "O_PATH", 0x200000)
        o_cloexec = getattr(os, "O_CLOEXEC", 0x80000)
        try:
            fd = os.open(path, o_path | o_cloexec)
        except OSError as exc:
            if not required:
                return
            raise OracleError(
                f"failed opening Landlock path '{path}': {exc}"
            ) from exc
        try:
            st = os.fstat(fd)
            if stat.S_ISDIR(st.st_mode):
                if allow_write:
                    access = dir_rw
                else:
                    access = (
                        _LANDLOCK_DIR_RO_EXEC if allow_exec else _LANDLOCK_DIR_RO
                    )
            else:
                if allow_write:
                    access = file_rw
                else:
                    access = (
                        _LANDLOCK_FILE_RO_EXEC if allow_exec else _LANDLOCK_FILE_RO
                    )
            pattr = ctypes.create_string_buffer(struct.pack("<Qi", access, fd))
            rc = int(
                libc.syscall(
                    _SYS_LANDLOCK_ADD_RULE,
                    ruleset_fd,
                    _LANDLOCK_RULE_PATH_BENEATH,
                    pattr,
                    0,
                )
            )
            if rc != 0:
                err = ctypes.get_errno()
                raise OracleError(
                    f"landlock_add_rule('{path}') failed: errno={err}"
                )
        finally:
            os.close(fd)

    ro_exec_entries, ro_entries = _collect_landlock_read_paths(
        target_exe, read_only_paths, read_only_exec_paths
    )
    try:
        for path, required in ro_exec_entries:
            _add_rule(path, allow_exec=True, allow_write=False, required=required)
        for path, required in ro_entries:
            _add_rule(path, allow_exec=False, allow_write=False, required=required)
        if allow_proc_self:
            _add_rule(Path("/proc/self"), allow_exec=False, allow_write=False, required=False)
        for rw_path in read_write_paths:
            _add_rule(rw_path, allow_exec=False, allow_write=True, required=True)
        if libc.prctl(_PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0:
            err = ctypes.get_errno()
            raise OracleError(f"prctl(PR_SET_NO_NEW_PRIVS) failed: errno={err}")
        if int(libc.syscall(_SYS_LANDLOCK_RESTRICT_SELF, ruleset_fd, 0)) != 0:
            err = ctypes.get_errno()
            raise OracleError(f"landlock_restrict_self failed: errno={err}")
    finally:
        os.close(ruleset_fd)


def _install_eval_landlock(
    target_exe: Path, read_only_paths: list[Path]
) -> None:
    """Confine `eval` children to a Landlock read-only allowlist (no `/proc`, no writes)."""
    _install_landlock(target_exe, read_only_paths)


def _assert_capture_non_root_uid() -> None:
    """Fail closed if launched as UID 0 (`root`).

    Linux `copy_process()` exempts `INIT_USER` (UID 0) and callers holding
    `CAP_SYS_RESOURCE`/`CAP_SYS_ADMIN` from `RLIMIT_NPROC`. Refuse to run
    `capture` confinement as UID 0 so the kernel task ceiling is always
    enforced.
    """
    if os.getuid() == 0 or os.geteuid() == 0:
        raise OracleError(
            "capture confinement refuses to run as UID 0 (root) because "
            "Linux exempts root/INIT_USER from RLIMIT_NPROC; re-run as an "
            "unprivileged user"
        )


def _drop_all_capabilities(
    libc: ctypes.CDLL, *, drop_bounding: bool = True
) -> None:
    """Drop Linux capabilities before `seccomp` and `execve`.

    Always clears ambient, effective, permitted, and inheritable capability
    sets. When `drop_bounding=True` (used in `capture` mode inside its private
    user namespace), also drops the capability bounding set via
    `PR_CAPBSET_DROP` and verifies via `PR_CAPBSET_READ` that any `EPERM`
    capability is already absent (failing closed otherwise). In `eval` mode
    (`drop_bounding=False`), `execve` stays in the seccomp allowlist so the
    `--_confined-exec` re-exec trampoline can launch `anneal-mir-eval` after
    installing the filter (while `execveat` and `clone`/`fork`/`vfork` are
    denied); setting `PR_SET_NO_NEW_PRIVS` before seccomp—together with
    clearing ambient, effective, permitted, and inheritable
    capabilities—prevents `CapBnd` from elevating privileges across any
    `execve`.
    """
    pr_capbset_read = 23
    pr_capbset_drop = 24
    pr_cap_ambient = 47
    pr_cap_ambient_clear_all = 4
    if drop_bounding:
        # Clear the bounding set while CAP_SETPCAP is held in the userns.
        for cap_num in range(64):
            rc = int(libc.prctl(pr_capbset_drop, cap_num, 0, 0, 0))
            if rc == 0:
                continue
            err = ctypes.get_errno()
            if err == errno.EINVAL:
                break
            if err == errno.EPERM:
                # Caller lacks CAP_SETPCAP; only accept EPERM if
                # PR_CAPBSET_READ confirms the cap is already absent.
                present = int(libc.prctl(pr_capbset_read, cap_num, 0, 0, 0))
                if present == 0:
                    continue
                if present < 0 and ctypes.get_errno() == errno.EINVAL:
                    break
                raise OracleError(
                    f"prctl(PR_CAPBSET_DROP, {cap_num}) failed with EPERM "
                    f"while capability remains in bounding set "
                    f"(PR_CAPBSET_READ={present})"
                )
            raise OracleError(
                f"prctl(PR_CAPBSET_DROP, {cap_num}) failed: errno={err}"
            )
    # Clear ambient capabilities (ignore EINVAL if kernel lacks ambient caps).
    if int(libc.prctl(pr_cap_ambient, pr_cap_ambient_clear_all, 0, 0, 0)) != 0:
        err = ctypes.get_errno()
        if err != errno.EINVAL:
            raise OracleError(
                f"prctl(PR_CAP_AMBIENT_CLEAR_ALL) failed: errno={err}"
            )
    machine = platform.machine().lower()
    if machine in ("x86_64", "amd64"):
        sys_capset = 126
    elif machine in ("aarch64", "arm64"):
        sys_capset = 91
    else:
        raise OracleError(f"unsupported architecture for capset: {machine!r}")
    # struct __user_cap_header_struct { __u32 version; int pid; }
    # struct __user_cap_data_struct[2] { effective, permitted, inheritable }
    cap_header = ctypes.create_string_buffer(struct.pack("<Ii", 0x20080522, 0))
    cap_data = ctypes.create_string_buffer(24)
    if int(libc.syscall(sys_capset, cap_header, cap_data)) != 0:
        err = ctypes.get_errno()
        raise OracleError(f"capset(clear all) failed: errno={err}")


def _enter_capture_namespaces(
    work_dir: Path | None,
    *,
    read_only_bind_paths: list[Path] = (),  # type: ignore[assignment]
    max_disk_bytes: int = CAPTURE_MAX_DISK_BYTES,
    max_inodes: int = CAPTURE_MAX_INODES,
) -> None:
    """Isolate the capture supervisor in private user, PID, mount, and net namespaces.

    Unshares `CLONE_NEWUSER | CLONE_NEWPID | CLONE_NEWNS | CLONE_NEWNET` with
    a 1:1 UID/GID mapping so:
    - The forked capture child runs as PID 1 in a private PID namespace: it
      cannot address or signal host/runner processes, and the kernel atomically
      kills and reaps all descendants when PID 1 exits.
    - The child receives a dedicated `ucounts` task budget (`RLIMIT_NPROC`)
      that cannot be escaped via nested namespaces (`clone`/`clone3`/`unshare`/
      `setns` namespace creation is denied by seccomp).
    - Every `read_only_bind_paths` entry (`src_dir`, `sysroot`, `target_exe`)
      is bind-mounted read-only (`MS_BIND | MS_REMOUNT | MS_RDONLY`) inside the
      private mount namespace so even non-Landlock metadata calls (`fchmod`)
      return `EROFS` on read-only inputs and toolchains.
    - If `work_dir` is provided, a private size- and inode-bounded `tmpfs`
      (`nosuid,nodev,noexec`) is mounted on `work_dir` so sequential file
      creation cannot fill the shared host filesystem.
    Fails closed with `OracleError` if namespaces, read-only bind-mounts, or
    the bounded `tmpfs` mount fail.
    """
    _assert_capture_non_root_uid()
    libc = ctypes.CDLL(None, use_errno=True)
    uid = os.getuid()
    gid = os.getgid()
    flags = _CLONE_NEWUSER | _CLONE_NEWPID | _CLONE_NEWNS | _CLONE_NEWNET
    if int(libc.unshare(flags)) != 0:
        err = ctypes.get_errno()
        raise OracleError(
            "capture confinement requires unprivileged Linux user/PID/mount/net "
            f"namespaces (unshare failed: errno={err})"
        )
    try:
        try:
            Path("/proc/self/setgroups").write_text("deny", encoding="ascii")
        except FileNotFoundError:
            pass
        Path("/proc/self/uid_map").write_text(f"{uid} {uid} 1\n", encoding="ascii")
        Path("/proc/self/gid_map").write_text(f"{gid} {gid} 1\n", encoding="ascii")
    except OSError as exc:
        raise OracleError(f"failed configuring capture user namespace maps: {exc}") from exc

    libc.mount.argtypes = [
        ctypes.c_char_p,
        ctypes.c_char_p,
        ctypes.c_char_p,
        ctypes.c_ulong,
        ctypes.c_char_p,
    ]
    libc.mount.restype = ctypes.c_int
    # Sever shared mount propagation from the host namespace before creating
    # bind-mounts or tmpfs mounts so SIGKILL cannot leak host-visible mounts.
    if int(libc.mount(None, b"/", None, _MS_REC | _MS_PRIVATE, None)) != 0:
        err = ctypes.get_errno()
        raise OracleError(
            f"failed marking capture mount namespace private: errno={err}"
        )

    def _remount_ro(target_p: Path, *, bind_first: bool) -> None:
        stv = os.statvfs(target_p)
        if stv.f_flag & getattr(os, "ST_RDONLY", 1):
            return
        preserved = 0
        for st_bit, ms_bit in _ST_TO_MS_FLAGS:
            if stv.f_flag & st_bit:
                preserved |= ms_bit
        p_bytes = os.fsencode(target_p)
        if bind_first:
            bind_flags = _MS_BIND | (_MS_REC if target_p.is_dir() else 0)
            if int(libc.mount(p_bytes, p_bytes, None, bind_flags, None)) != 0:
                err = ctypes.get_errno()
                raise OracleError(
                    f"failed read-only bind-mount on '{target_p}': errno={err}"
                )
        remount_flags = _MS_BIND | _MS_REMOUNT | _MS_RDONLY | preserved
        if int(libc.mount(None, p_bytes, None, remount_flags, None)) != 0:
            err = ctypes.get_errno()
            raise OracleError(
                f"failed read-only remount on '{target_p}': errno={err}"
            )

    def _unescape_mountinfo_path(raw_mp: str) -> str:
        return re.sub(
            r"\\([0-7]{3})", lambda m: chr(int(m.group(1), 8)), raw_mp
        )

    work_resolved = work_dir.resolve() if work_dir is not None else None
    seen_ro: set[Path] = set()
    for raw_p in read_only_bind_paths:
        if not raw_p.exists():
            continue
        p = raw_p.resolve()
        if p in seen_ro or p == Path("/"):
            continue
        if work_resolved is not None and (
            work_resolved == p or work_resolved.is_relative_to(p)
        ):
            raise OracleError(
                f"capture work_dir '{work_resolved}' must not reside under "
                f"read-only path '{p}'"
            )
        seen_ro.add(p)
        _remount_ro(p, bind_first=True)
        if p.is_dir():
            # `MS_REMOUNT | MS_RDONLY` applies per mountpoint; also remount
            # any submounts beneath `p/` so `fchmod` fails with `EROFS` across
            # nested mounts inside readable trees.
            prefix = str(p).rstrip("/") + "/"
            for line in Path("/proc/self/mountinfo").read_text(
                encoding="utf-8", errors="replace"
            ).splitlines():
                parts = line.split()
                if len(parts) < 5:
                    continue
                mp_str = _unescape_mountinfo_path(parts[4])
                if not mp_str.startswith(prefix):
                    continue
                mp_path = Path(mp_str)
                if work_resolved is not None and (
                    work_resolved == mp_path
                    or work_resolved.is_relative_to(mp_path)
                ):
                    continue
                if mp_path.exists():
                    _remount_ro(mp_path, bind_first=False)

    if work_dir is not None:
        if max_disk_bytes <= 0 or max_inodes <= 0:
            raise OracleError(
                f"invalid capture tmpfs quota: bytes={max_disk_bytes}, inodes={max_inodes}"
            )
        mount_opts = f"size={max_disk_bytes},nr_inodes={max_inodes},mode=0700".encode(
            "ascii"
        )
        rc = int(
            libc.mount(
                b"tmpfs",
                os.fsencode(work_dir),
                b"tmpfs",
                _MS_NOSUID | _MS_NODEV | _MS_NOEXEC,
                mount_opts,
            )
        )
        if rc != 0:
            err = ctypes.get_errno()
            raise OracleError(
                f"failed mounting bounded tmpfs on '{work_dir}': errno={err}"
            )
        (work_dir / "tmp").mkdir(mode=0o700, exist_ok=True)


def _export_capture_file(src_file: Path, dst_file: Path) -> None:
    """Copy one bounded regular non-symlink file from capture tmpfs `src_file` to `dst_file`.

    Silently returns if `src_file` or its parent directory was not produced
    (e.g. when capture exited with `unsupported` or `compiler_failed`). Ignores
    sibling files/directories such as sharded `Captured/` output so multi-shard
    captures (>20 bodies) export `capture.json` cleanly while rejecting symlinks,
    non-regular entries, or oversized payloads fail-closed.
    """
    o_nofollow = getattr(os, "O_NOFOLLOW", 0)
    o_directory = getattr(os, "O_DIRECTORY", 0)
    o_nonblock = getattr(os, "O_NONBLOCK", 0)
    try:
        src_dir_fd = os.open(
            src_file.parent, os.O_RDONLY | o_directory | o_nofollow
        )
    except FileNotFoundError:
        return
    try:
        try:
            in_fd = os.open(
                src_file.name,
                os.O_RDONLY | o_nofollow | o_nonblock,
                dir_fd=src_dir_fd,
            )
        except FileNotFoundError:
            return
        try:
            in_st = os.fstat(in_fd)
            if not stat.S_ISREG(in_st.st_mode):
                raise OracleError(
                    f"capture output entry '{src_file.name}' is not a regular file"
                )
            dst_file.parent.mkdir(parents=True, exist_ok=True)
            dst_dir_fd = os.open(
                dst_file.parent, os.O_RDONLY | o_directory | o_nofollow
            )
            try:
                out_fd = os.open(
                    dst_file.name,
                    os.O_WRONLY | os.O_CREAT | os.O_EXCL | o_nofollow,
                    0o600,
                    dir_fd=dst_dir_fd,
                )
                try:
                    total_bytes = 0
                    while True:
                        chunk = os.read(in_fd, 65536)
                        if not chunk:
                            break
                        total_bytes += len(chunk)
                        if total_bytes > CAPTURE_MAX_EXPORT_BYTES:
                            raise OracleError(
                                "capture exported output exceeds "
                                f"{CAPTURE_MAX_EXPORT_BYTES} bytes"
                            )
                        view = memoryview(chunk)
                        while view:
                            written = os.write(out_fd, view)
                            view = view[written:]
                finally:
                    os.close(out_fd)
            finally:
                os.close(dst_dir_fd)
        finally:
            os.close(in_fd)
    finally:
        os.close(src_dir_fd)


def _build_confinement_seccomp_bpf(
    machine: str, *, confinement: str = "eval"
) -> bytes:
    """Build a default-deny Linux seccomp-BPF filter for `eval` or `capture` confinement.

    Always kills non-native or x32 ABI syscalls and defaults every unlisted
    syscall to `EPERM`. Both modes share the base read/memory/signal/stat
    allowlist, `prlimit64` restricted to `pid == 0` (self), and `fcntl`
    restricted to safe descriptor/flag operations (denying `F_SETOWN`,
    `F_SETSIG`, `O_ASYNC`, pipe resizing, leases, locks, and seals).

    `eval` restricts `open`/`openat` to read-only flags and `ioctl` to
    `FIOCLEX`, denying all process/thread creation, pipes, and filesystem
    mutations. `capture` adds the audited subset required by
    `anneal-rustc-capture` and `rustc` inside its isolated `CLONE_NEWUSER |
    CLONE_NEWPID | CLONE_NEWNS | CLONE_NEWNET` sandbox: `clone3` returns
    `ENOSYS` (falling back to `clone`), `clone` denies every namespace flag in
    `_CLONE_FORBIDDEN_NS_FLAGS` and non-zero upper 32 bits, `ioctl` admits only
    `{FIOCLEX, FIONCLEX, FIONBIO}`, and `prctl` admits only `{PR_SET_NAME,
    PR_GET_NAME}`. Sockets, eventfds, memfds, io_uring, SysV/POSIX IPC,
    `setsid`/`setpgid`, `unshare`/`setns`, `kill`, `ptrace`, `process_vm_*`,
    and `mount` are denied by default.
    """
    if confinement not in CONFINEMENT_MODES:
        raise OracleError(f"unsupported confinement mode: {confinement!r}")
    spec = _SECCOMP_ARCH_TABLE.get(machine.lower())
    if spec is None:
        raise OracleError(
            f"unsupported architecture for Linux seccomp confinement: {machine!r}"
        )
    ir: list[tuple[object, ...]] = [
        ("op", _BPF_LD_W_ABS, 0, 0, 4),  # load seccomp_data.arch
        ("op", _BPF_JMP_JEQ_K, 0, "kill", spec["audit_arch"]),
        ("op", _BPF_LD_W_ABS, 0, 0, 0),  # load seccomp_data.nr
    ]
    if spec["reject_x32"]:
        ir.append(("op", _BPF_JMP_JSET_K, "kill", 0, _X32_SYSCALL_BIT))
    for nr in spec["eval_allow_nrs"]:  # type: ignore[union-attr]
        ir.append(("op", _BPF_JMP_JEQ_K, "allow", 0, nr))
    if confinement == "capture":
        for nr in spec["capture_extra_allow_nrs"]:  # type: ignore[union-attr]
            ir.append(("op", _BPF_JMP_JEQ_K, "allow", 0, nr))
        ir.append(("op", _BPF_JMP_JEQ_K, "enosys", 0, spec["clone3_nr"]))
        ir.extend([
            ("op", _BPF_JMP_JEQ_K, 0, "after_clone", spec["clone_nr"]),
            ("op", _BPF_LD_W_ABS, 0, 0, 20),  # args[0] high 32 bits (flags)
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", 0),
            ("op", _BPF_LD_W_ABS, 0, 0, 16),  # args[0] low 32 bits (flags)
            ("op", _BPF_JMP_JSET_K, "eperm", "allow", _CLONE_FORBIDDEN_NS_FLAGS),
            ("label", "after_clone"),
        ])
        ir.extend([
            ("op", _BPF_JMP_JEQ_K, 0, "after_prctl", spec["prctl_nr"]),
            ("op", _BPF_LD_W_ABS, 0, 0, 20),  # args[0] high 32 bits (option)
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", 0),
            ("op", _BPF_LD_W_ABS, 0, 0, 16),  # args[0] low 32 bits (option)
        ])
        for opt_val in _PRCTL_CAPTURE_ALLOWED:
            ir.append(("op", _BPF_JMP_JEQ_K, "allow", 0, opt_val))
        ir.extend([
            ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_ERRNO | errno.EPERM),
            ("label", "after_prctl"),
        ])
    else:
        openat_nr = spec["openat_nr"]
        if openat_nr is not None:
            ir.extend([
                ("op", _BPF_JMP_JEQ_K, 0, "after_openat", openat_nr),
                ("op", _BPF_LD_W_ABS, 0, 0, 32),  # args[2] low 32 bits (flags)
                ("op", _BPF_JMP_JSET_K, "eperm", "allow", _OPEN_WRITE_FLAGS),
                ("label", "after_openat"),
            ])
        open_nr = spec["open_nr"]
        if open_nr is not None:
            ir.extend([
                ("op", _BPF_JMP_JEQ_K, 0, "after_open", open_nr),
                ("op", _BPF_LD_W_ABS, 0, 0, 24),  # args[1] low 32 bits (flags)
                ("op", _BPF_JMP_JSET_K, "eperm", "allow", _OPEN_WRITE_FLAGS),
                ("label", "after_open"),
            ])
    prlimit64_nr = spec["prlimit64_nr"]
    if prlimit64_nr is not None:
        ir.extend([
            ("op", _BPF_JMP_JEQ_K, 0, "after_prlimit64", prlimit64_nr),
            ("op", _BPF_LD_W_ABS, 0, 0, 16),  # args[0] low 32 bits (pid)
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", 0),
            ("op", _BPF_LD_W_ABS, 0, 0, 20),  # args[0] high 32 bits (pid)
            ("op", _BPF_JMP_JEQ_K, "allow", "eperm", 0),
            ("label", "after_prlimit64"),
        ])
    ioctl_nr = spec["ioctl_nr"]
    if ioctl_nr is not None:
        allowed_ioctls = (
            _IOCTL_CAPTURE_ALLOWED if confinement == "capture" else (_IOCTL_FIOCLEX,)
        )
        ir.extend([
            ("op", _BPF_JMP_JEQ_K, 0, "after_ioctl", ioctl_nr),
            ("op", _BPF_LD_W_ABS, 0, 0, 28),  # args[1] high 32 bits (req)
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", 0),
            ("op", _BPF_LD_W_ABS, 0, 0, 24),  # args[1] low 32 bits (req)
        ])
        for req_val in allowed_ioctls:
            ir.append(("op", _BPF_JMP_JEQ_K, "allow", 0, req_val))
        ir.extend([
            ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_ERRNO | errno.EPERM),
            ("label", "after_ioctl"),
        ])
    fcntl_nr = spec["fcntl_nr"]
    if fcntl_nr is not None:
        ir.extend([
            ("op", _BPF_JMP_JEQ_K, 0, "after_fcntl", fcntl_nr),
            ("op", _BPF_LD_W_ABS, 0, 0, 28),  # args[1] high 32 bits (cmd)
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", 0),
            ("op", _BPF_LD_W_ABS, 0, 0, 24),  # args[1] low 32 bits (cmd)
        ])
        for cmd_val in _FCNTL_SAFE_CMDS:
            ir.append(("op", _BPF_JMP_JEQ_K, "allow", 0, cmd_val))
        ir.extend([
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", _FCNTL_F_SETFL),
            ("op", _BPF_LD_W_ABS, 0, 0, 36),  # args[2] high 32 bits (flags)
            ("op", _BPF_JMP_JEQ_K, 0, "eperm", 0),
            ("op", _BPF_LD_W_ABS, 0, 0, 32),  # args[2] low 32 bits (flags)
            ("op", _BPF_JMP_JSET_K, "eperm", "allow", _FCNTL_O_ASYNC),
            ("label", "after_fcntl"),
        ])
    ir.extend([
        ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_ERRNO | errno.EPERM),
        ("label", "kill"),
        ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_KILL_PROCESS),
        ("label", "eperm"),
        ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_ERRNO | errno.EPERM),
        ("label", "enosys"),
        ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_ERRNO | errno.ENOSYS),
        ("label", "allow"),
        ("op", _BPF_RET_K, 0, 0, _SECCOMP_RET_ALLOW),
    ])
    labels: dict[str, int] = {}
    ops: list[tuple[int, object, object, int]] = []
    for item in ir:
        if item[0] == "label":
            labels[str(item[1])] = len(ops)
        else:
            ops.append((int(item[1]), item[2], item[3], int(item[4])))
    out = bytearray()
    for idx, (code, jt_ref, jf_ref, k) in enumerate(ops):
        jt = (labels[jt_ref] - idx - 1) if isinstance(jt_ref, str) else int(jt_ref)
        jf = (labels[jf_ref] - idx - 1) if isinstance(jf_ref, str) else int(jf_ref)
        if not (0 <= jt <= 255 and 0 <= jf <= 255):
            raise OracleError(f"invalid BPF jump offset at {idx}: jt={jt}, jf={jf}")
        out.extend(struct.pack("HBBI", code, jt, jf, k))
    return bytes(out)


def _install_confinement_seccomp(*, confinement: str) -> None:
    """Install `PR_SET_NO_NEW_PRIVS` and the confinement seccomp filter."""
    bpf = _build_confinement_seccomp_bpf(
        platform.machine(), confinement=confinement
    )
    buf = ctypes.create_string_buffer(bpf)
    prog = _SockFprog(len(bpf) // 8, ctypes.addressof(buf))
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(_PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0:
        err = ctypes.get_errno()
        raise OracleError(f"prctl(PR_SET_NO_NEW_PRIVS) failed: errno={err}")
    if libc.prctl(_PR_SET_SECCOMP, _SECCOMP_MODE_FILTER, ctypes.byref(prog), 0, 0) != 0:
        err = ctypes.get_errno()
        raise OracleError(f"prctl(PR_SET_SECCOMP) failed: errno={err}")


def _apply_rlimit(limit_kind: int, requested: int) -> None:
    """Apply a hard+soft rlimit without attempting to raise an existing tighter cap."""
    _, cur_hard = resource.getrlimit(limit_kind)
    if cur_hard != resource.RLIM_INFINITY and cur_hard < requested:
        effective = cur_hard
    else:
        effective = requested
    resource.setrlimit(limit_kind, (effective, effective))


def _run_confined_exec(argv: list[str]) -> int:
    """Single-threaded exec trampoline: install Landlock + seccomp + rlimits, then `execv`."""
    try:
        if len(argv) < 7:
            raise OracleError("malformed --_confined-exec invocation")
        cpu_limit = int(argv[0])
        fsize_limit = int(argv[1])
        as_limit = int(argv[2])
        nofile_limit = int(argv[3])
        mode = argv[4]
        if mode not in CONFINEMENT_MODES:
            raise OracleError(f"invalid --_confined-exec mode: {mode!r}")
        idx = 5
        ro_paths: list[Path] = []
        ro_exec_paths: list[Path] = []
        rw_paths: list[Path] = []
        prepend_ld_paths: list[str] = []
        export_src: Path | None = None
        export_dst: Path | None = None
        max_tasks = CAPTURE_MAX_TASKS
        expected_parent_pid: int | None = None
        while idx < len(argv) and argv[idx] in (
            "--ro",
            "--ro-exec",
            "--rw",
            "--prepend-ld-library-path",
            "--export-src",
            "--export-dst",
            "--max-tasks",
            "--parent-pid",
        ):
            if idx + 1 >= len(argv):
                raise OracleError(f"malformed {argv[idx]} in --_confined-exec")
            if argv[idx] == "--ro":
                ro_paths.append(Path(argv[idx + 1]))
            elif argv[idx] == "--ro-exec":
                ro_exec_paths.append(Path(argv[idx + 1]))
            elif argv[idx] == "--rw":
                rw_paths.append(Path(argv[idx + 1]))
            elif argv[idx] == "--prepend-ld-library-path":
                if not argv[idx + 1]:
                    raise OracleError(
                        "empty --prepend-ld-library-path in --_confined-exec"
                    )
                prepend_ld_paths.append(argv[idx + 1])
            elif argv[idx] == "--export-src":
                export_src = Path(argv[idx + 1])
            elif argv[idx] == "--export-dst":
                export_dst = Path(argv[idx + 1])
            elif argv[idx] == "--max-tasks":
                max_tasks = int(argv[idx + 1])
                if max_tasks <= 0:
                    raise OracleError("invalid --max-tasks in --_confined-exec")
            else:
                expected_parent_pid = int(argv[idx + 1])
                if expected_parent_pid <= 0:
                    raise OracleError("invalid --parent-pid in --_confined-exec")
            idx += 2
        if idx >= len(argv) or argv[idx] != "--":
            raise OracleError("malformed --_confined-exec invocation")
        target_cmd = argv[idx + 1 :]
        if (
            cpu_limit <= 0
            or fsize_limit < 0
            or as_limit <= 0
            or nofile_limit <= 0
            or not target_cmd
        ):
            raise OracleError("invalid --_confined-exec limits or command")
        if mode == "capture" and fsize_limit == 0:
            raise OracleError("capture mode requires positive RLIMIT_FSIZE")
        if mode == "capture" and len(rw_paths) > 1:
            raise OracleError("capture mode supports at most one bounded work directory")
        if (export_src is None) != (export_dst is None):
            raise OracleError("--export-src and --export-dst must be paired")

        libc = ctypes.CDLL(None, use_errno=True)
        libc.prctl.argtypes = [
            ctypes.c_int,
            ctypes.c_ulong,
            ctypes.c_ulong,
            ctypes.c_ulong,
            ctypes.c_ulong,
        ]
        libc.prctl.restype = ctypes.c_int

        if mode == "capture":
            # Always supervise `capture` inside private user/PID/mount/network
            # namespaces. The forked capture child becomes PID 1 of the private
            # PID namespace (so it cannot see or signal peer runner processes,
            # and the Linux kernel atomically SIGKILLs + reaps all descendants
            # before `waitpid` returns on ANY child exit). Any writable work
            # directory is overlaid with a size- and inode-bounded `tmpfs` so
            # sequential file creation cannot fill the host disk, and regular
            # output files are exported only after PID-namespace teardown.
            child_pid_box: list[int] = []

            def _kill_capture_and_exit(
                _signum: int = 0, _frame: object = None
            ) -> None:
                if child_pid_box:
                    try:
                        os.kill(child_pid_box[0], signal.SIGKILL)
                    except OSError:
                        pass
                    try:
                        os.waitpid(child_pid_box[0], 0)
                    except OSError:
                        pass
                try:
                    os.killpg(0, signal.SIGKILL)
                except OSError:
                    pass
                os._exit(128 + int(signal.SIGKILL))

            if expected_parent_pid is not None:
                signal.signal(signal.SIGTERM, _kill_capture_and_exit)
                if libc.prctl(1, int(signal.SIGTERM), 0, 0, 0) != 0:
                    err = ctypes.get_errno()
                    raise OracleError(f"prctl(PR_SET_PDEATHSIG) failed: errno={err}")
                if os.getppid() != expected_parent_pid:
                    os._exit(128 + int(signal.SIGKILL))

            work_dir = rw_paths[0] if rw_paths else None
            cap_ro_exec, cap_ro = _collect_landlock_read_paths(
                Path(target_cmd[0]), ro_paths, ro_exec_paths
            )
            _enter_capture_namespaces(
                work_dir,
                read_only_bind_paths=[p for p, _ in (*cap_ro_exec, *cap_ro)],
            )
            if expected_parent_pid is not None:
                # Writing uid_map/gid_map can clear PR_SET_PDEATHSIG; re-arm.
                if libc.prctl(1, int(signal.SIGTERM), 0, 0, 0) != 0:
                    err = ctypes.get_errno()
                    raise OracleError(
                        f"post-userns prctl(PR_SET_PDEATHSIG) failed: errno={err}"
                    )
                if os.getppid() != expected_parent_pid:
                    os._exit(128 + int(signal.SIGKILL))

            sync_r, sync_w = os.pipe()
            child_pid = os.fork()
            if child_pid == 0:
                try:
                    os.close(sync_w)
                    signal.signal(signal.SIGTERM, signal.SIG_DFL)
                    if libc.prctl(1, int(signal.SIGKILL), 0, 0, 0) != 0:
                        err = ctypes.get_errno()
                        raise OracleError(
                            f"child prctl(PR_SET_PDEATHSIG) failed: errno={err}"
                        )
                    os.set_blocking(sync_r, False)
                    try:
                        if os.read(sync_r, 1) == b"":
                            os._exit(128 + int(signal.SIGKILL))
                    except BlockingIOError:
                        pass
                    os.close(sync_r)
                    _install_landlock(
                        Path(target_cmd[0]),
                        ro_paths,
                        read_only_exec_paths=ro_exec_paths,
                        read_write_paths=rw_paths,
                        allow_proc_self=True,
                        require_truncate_mediation=True,
                    )
                    # Supervisor occupies 1 task slot in shared userns ucounts.
                    _apply_rlimit(resource.RLIMIT_NPROC, max_tasks + 1)
                    _apply_rlimit(resource.RLIMIT_CPU, cpu_limit)
                    _apply_rlimit(resource.RLIMIT_FSIZE, fsize_limit)
                    _apply_rlimit(resource.RLIMIT_AS, as_limit)
                    _apply_rlimit(resource.RLIMIT_NOFILE, nofile_limit)
                    _drop_all_capabilities(libc, drop_bounding=True)
                    exec_env = dict(os.environ)
                    if prepend_ld_paths:
                        prefix = os.pathsep.join(prepend_ld_paths)
                        prev_ld = exec_env.get("LD_LIBRARY_PATH", "")
                        exec_env["LD_LIBRARY_PATH"] = (
                            f"{prefix}{os.pathsep}{prev_ld}"
                            if prev_ld
                            else prefix
                        )
                    _install_confinement_seccomp(confinement=mode)
                    os.execve(target_cmd[0], target_cmd, exec_env)
                except BaseException as exc:  # noqa: BLE001
                    sys.stderr.write(f"confined-exec failed closed: {exc}\n")
                    sys.stderr.flush()
                    os._exit(125)

            os.close(sync_r)
            child_pid_box.append(child_pid)
            try:
                while True:
                    if (
                        expected_parent_pid is not None
                        and os.getppid() != expected_parent_pid
                    ):
                        _kill_capture_and_exit()
                    try:
                        waited_pid, status = os.waitpid(child_pid, os.WNOHANG)
                    except ChildProcessError:
                        os._exit(1)
                    if waited_pid == child_pid:
                        # PID 1 of the private PID namespace has exited, so the
                        # kernel has atomically terminated and reaped every
                        # descendant inside that namespace.
                        if export_src is not None and export_dst is not None:
                            _export_capture_file(export_src, export_dst)
                        if work_dir is not None:
                            try:
                                libc.umount2(os.fsencode(work_dir), _MNT_DETACH)
                            except OSError:
                                pass
                        if os.WIFEXITED(status):
                            os._exit(os.WEXITSTATUS(status))
                        if os.WIFSIGNALED(status):
                            os._exit(128 + os.WTERMSIG(status))
                        os._exit(1)
                    time.sleep(0.02)
            finally:
                try:
                    os.close(sync_w)
                except OSError:
                    pass

        if expected_parent_pid is not None:
            # In `eval` mode, seccomp denies `fork`/`clone`, so direct
            # `PR_SET_PDEATHSIG(SIGKILL)` binds the sole process in the tree.
            if libc.prctl(1, int(signal.SIGKILL), 0, 0, 0) != 0:
                err = ctypes.get_errno()
                raise OracleError(f"prctl(PR_SET_PDEATHSIG) failed: errno={err}")
            if os.getppid() != expected_parent_pid:
                os._exit(128 + int(signal.SIGKILL))
        _install_eval_landlock(Path(target_cmd[0]), ro_paths)
        _apply_rlimit(resource.RLIMIT_CPU, cpu_limit)
        _apply_rlimit(resource.RLIMIT_FSIZE, fsize_limit)
        _apply_rlimit(resource.RLIMIT_AS, as_limit)
        _apply_rlimit(resource.RLIMIT_NOFILE, nofile_limit)
        _drop_all_capabilities(libc, drop_bounding=False)
        exec_env = dict(os.environ)
        if prepend_ld_paths:
            prefix = os.pathsep.join(prepend_ld_paths)
            prev_ld = exec_env.get("LD_LIBRARY_PATH", "")
            exec_env["LD_LIBRARY_PATH"] = (
                f"{prefix}{os.pathsep}{prev_ld}" if prev_ld else prefix
            )
        _install_confinement_seccomp(confinement=mode)
        os.execve(target_cmd[0], target_cmd, exec_env)
    except BaseException as exc:  # noqa: BLE001
        sys.stderr.write(f"confined-exec failed closed: {exc}\n")
        sys.stderr.flush()
        os._exit(125)
    return 125


def _require_confinement_support(
    max_memory_mb: int, *, require_truncate_mediation: bool = False
) -> None:
    """Fail closed unless Linux Landlock + seccomp + rlimit + non-dumpable works."""
    if (
        isinstance(max_memory_mb, bool)
        or not isinstance(max_memory_mb, int)
        or max_memory_mb <= 0
    ):
        raise OracleError(
            f"--max-memory-mb must be a positive integer MiB value, got {max_memory_mb!r}"
        )
    if sys.platform != "linux":
        raise OracleError(
            "Linux Landlock + seccomp + RLIMIT_AS confinement is required to bound child process trees"
        )
    _build_confinement_seccomp_bpf(platform.machine(), confinement="eval")
    _build_confinement_seccomp_bpf(platform.machine(), confinement="capture")
    try:
        status_text = Path("/proc/self/status").read_text(encoding="utf-8")
    except OSError as exc:
        raise OracleError(f"failed to probe /proc/self/status for seccomp: {exc}") from exc
    if "Seccomp:" not in status_text:
        raise OracleError(
            "Linux kernel seccomp support is unavailable; refusing to spawn unconfined children"
        )
    _assert_capture_non_root_uid()
    abi = _probe_landlock_abi()
    if require_truncate_mediation and abi < 3:
        raise OracleError(
            "capture confinement requires Linux Landlock ABI >= 3 for "
            f"truncate mediation (got ABI {abi})"
        )
    _harden_parent_process()


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


def _wrap_with_confinement(
    cmd: list[str],
    *,
    timeout_secs: int,
    max_memory_mb: int = DEFAULT_MAX_MEMORY_MB,
    confinement: str = "eval",
    read_only_paths: tuple[Path, ...] = (),
    read_only_exec_paths: tuple[Path, ...] = (),
    read_write_paths: tuple[Path, ...] = (),
    prepend_ld_library_path: Path | None = None,
    export_src: Path | None = None,
    export_dst: Path | None = None,
    max_tasks: int | None = None,
    parent_pid: int | None = None,
) -> list[str]:
    """Wrap child command in our single-threaded Landlock + seccomp + rlimit trampoline.

    Avoids unsafe `preexec_fn` in multi-threaded callers, isolates `capture`
    inside private user/PID/mount/network namespaces with a size- and
    inode-bounded `tmpfs` work dir, enforces Landlock filesystem isolation in
    both `eval` (strictly read-only, no `/proc`) and `capture` (ABI >= 3 with
    truncate mediation, read-only source/sysroot + bounded `tmpfs` work dir),
    enforces default-deny seccomp in both modes, and enforces `RLIMIT_CPU`,
    `RLIMIT_FSIZE`, `RLIMIT_AS`, and `RLIMIT_NOFILE`. Fails closed via
    `OracleError` if confinement is unavailable.
    """
    if confinement not in CONFINEMENT_MODES:
        raise OracleError(f"unsupported confinement mode: {confinement!r}")
    _require_confinement_support(
        max_memory_mb, require_truncate_mediation=(confinement == "capture")
    )
    cpu_limit = max(timeout_secs + 5, 10)
    fsize_limit = 0 if confinement == "eval" else MAX_SUBPROCESS_FSIZE_BYTES
    nofile_limit = EVAL_MAX_NOFILE if confinement == "eval" else CAPTURE_MAX_NOFILE
    extra_args: list[str] = []
    for p in read_only_paths:
        extra_args.extend(["--ro", str(p)])
    for p in read_only_exec_paths:
        extra_args.extend(["--ro-exec", str(p)])
    for p in read_write_paths:
        extra_args.extend(["--rw", str(p)])
    if prepend_ld_library_path is not None:
        extra_args.extend(
            ["--prepend-ld-library-path", str(prepend_ld_library_path)]
        )
    if export_src is not None or export_dst is not None:
        if export_src is None or export_dst is None:
            raise OracleError("export_src and export_dst must both be set")
        extra_args.extend(["--export-src", str(export_src), "--export-dst", str(export_dst)])
    if confinement == "capture":
        eff_tasks = CAPTURE_MAX_TASKS if max_tasks is None else max_tasks
        if isinstance(eff_tasks, bool) or not isinstance(eff_tasks, int) or eff_tasks <= 0:
            raise OracleError(f"invalid max_tasks: {eff_tasks!r}")
        extra_args.extend(["--max-tasks", str(eff_tasks)])
    if parent_pid is not None:
        extra_args.extend(["--parent-pid", str(parent_pid)])
    return [
        sys.executable,
        "-I",
        "-B",
        str(Path(__file__).resolve()),
        _CONFINED_EXEC_FLAG,
        str(cpu_limit),
        str(fsize_limit),
        str(max_memory_mb * 1024 * 1024),
        str(nofile_limit),
        confinement,
        *extra_args,
        "--",
        *cmd,
    ]


def _kill_process_group(proc: subprocess.Popen[bytes]) -> None:
    """Force-terminate a child process and its POSIX process group."""
    if os.name == "posix":
        try:
            os.killpg(proc.pid, signal.SIGKILL)
            return
        except ProcessLookupError:
            return
        except OSError:
            pass
    try:
        proc.kill()
    except OSError:
        pass


def _count_pgid_processes(pgid: int) -> int | None:
    """Count live non-zombie Linux processes in process group `pgid`.

    Returns `None` if `/proc` cannot be enumerated so callers fail closed.
    """
    count = 0
    try:
        entries = os.listdir("/proc")
    except OSError:
        return None
    for name in entries:
        if not name.isdigit():
            continue
        try:
            stat = Path(f"/proc/{name}/stat").read_text(encoding="ascii", errors="ignore")
        except OSError:
            continue
        rparen = stat.rfind(")")
        if rparen < 0:
            continue
        fields = stat[rparen + 2 :].split()
        if len(fields) < 3:
            continue
        state = fields[0]
        if state == "Z":
            continue
        try:
            if int(fields[2]) == pgid:
                count += 1
        except ValueError:
            continue
    return count


class _CancelToken:
    """Thread-safe atomic cancellation state and active-child killer registry.

    Serializing cancellation and child registration under one lock closes the
    race where Ctrl-C/SIGTERM arrives after a worker starts `Popen` and before
    it registers its PGID killer: a late `register()` observes `_cancelled`
    atomically, kills the child immediately, and raises `KeyboardInterrupt`.
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._cancelled = False
        self._killers: dict[int, Callable[[], None]] = {}
        self._next_id = 0

    def check_cancelled(self) -> None:
        with self._lock:
            if self._cancelled:
                raise KeyboardInterrupt("oracle run cancelled")

    def register(self, kill_fn: Callable[[], None]) -> int:
        with self._lock:
            if self._cancelled:
                cancelled_now = True
                tok = -1
            else:
                cancelled_now = False
                self._next_id += 1
                tok = self._next_id
                self._killers[tok] = kill_fn
        if cancelled_now:
            kill_fn()
            raise KeyboardInterrupt("oracle run cancelled")
        return tok

    def unregister(self, tok: int) -> None:
        if tok < 0:
            return
        with self._lock:
            self._killers.pop(tok, None)

    def cancel_and_kill_all(self) -> None:
        with self._lock:
            self._cancelled = True
            killers = list(self._killers.values())
        for killer in killers:
            try:
                killer()
            except Exception:  # noqa: BLE001
                pass


def _sanitize_detail(
    text: str, *tmp_paths: Path | None, max_len: int = 240
) -> str:
    """Normalize temporary paths out of diagnostic strings for determinism."""
    out = text
    for p in tmp_paths:
        if p is not None:
            out = out.replace(str(p), "<tmp>")
    out = re.sub(r"/[^\s:'\"]*anneal-miri-[^\s:'\"/]+", "<tmp>", out)
    return out[:max_len]


def run_bounded(
    cmd: list[str],
    *,
    env: dict[str, str],
    timeout_secs: int,
    max_memory_mb: int = DEFAULT_MAX_MEMORY_MB,
    max_output_bytes: int = MAX_CHILD_OUTPUT_BYTES,
    confinement: str = "eval",
    max_procs: int | None = None,
    max_tasks: int | None = None,
    read_only_paths: tuple[Path, ...] = (),
    read_only_exec_paths: tuple[Path, ...] = (),
    read_write_paths: tuple[Path, ...] = (),
    prepend_ld_library_path: Path | None = None,
    export_src: Path | None = None,
    export_dst: Path | None = None,
    cancel_token: _CancelToken | None = None,
) -> tuple[int | str, str, str, float]:
    """Run a child process with timeout, Landlock/seccomp/rlimit confinement, and bounded pipes.

    `RLIMIT_FSIZE` does not cap pipe writes, so stdout and stderr are drained
    incrementally into fixed-size buffers. Exceeding `max_output_bytes` on
    either stream kills the child process group immediately and returns
    `("output_limit", ...)` so callers classify overflow as `tool_error`.
    """
    if cancel_token is not None:
        cancel_token.check_cancelled()
    t0 = time.monotonic()
    bounded_cmd = _wrap_with_confinement(
        cmd,
        timeout_secs=timeout_secs,
        max_memory_mb=max_memory_mb,
        confinement=confinement,
        read_only_paths=read_only_paths,
        read_only_exec_paths=read_only_exec_paths,
        read_write_paths=read_write_paths,
        prepend_ld_library_path=prepend_ld_library_path,
        export_src=export_src,
        export_dst=export_dst,
        max_tasks=max_tasks,
        parent_pid=os.getpid(),
    )
    if cancel_token is not None:
        cancel_token.check_cancelled()
    try:
        proc = subprocess.Popen(
            bounded_cmd,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
            start_new_session=(os.name == "posix"),
        )
    except OSError as exc:
        return "os_error", "", str(exc), time.monotonic() - t0

    out_buf = bytearray()
    err_buf = bytearray()
    overflowed = threading.Event()
    done = threading.Event()
    kill_lock = threading.Lock()
    reaped = False

    def _kill_if_unreaped() -> None:
        with kill_lock:
            if not reaped:
                _kill_process_group(proc)

    cancel_reg: int | None = None
    if cancel_token is not None:
        try:
            cancel_reg = cancel_token.register(_kill_if_unreaped)
        except BaseException:
            with kill_lock:
                reaped = True
            try:
                proc.wait(timeout=5.0)
            except subprocess.TimeoutExpired:
                pass
            if proc.stdout is not None:
                proc.stdout.close()
            if proc.stderr is not None:
                proc.stderr.close()
            raise

    def _drain(stream, buf: bytearray) -> None:
        try:
            while True:
                chunk = stream.read(CHILD_READ_CHUNK_BYTES)
                if not chunk:
                    break
                remaining = max_output_bytes - len(buf)
                if len(chunk) > remaining:
                    if remaining > 0:
                        buf.extend(chunk[:remaining])
                    overflowed.set()
                    _kill_if_unreaped()
                    break
                buf.extend(chunk)
        except OSError:
            pass
        finally:
            try:
                stream.close()
            except OSError:
                pass

    def _wait_child() -> None:
        try:
            # Wait without reaping (`WNOWAIT`) so `proc.pid` stays pinned in the
            # kernel PID table until all synchronized `os.killpg` calls finish.
            if (
                os.name == "posix"
                and hasattr(os, "waitid")
                and hasattr(os, "P_PID")
                and hasattr(os, "WEXITED")
                and hasattr(os, "WNOWAIT")
            ):
                try:
                    os.waitid(os.P_PID, proc.pid, os.WEXITED | os.WNOWAIT)
                except ChildProcessError:
                    pass
            else:
                proc.wait()
        finally:
            done.set()

    assert proc.stdout is not None and proc.stderr is not None
    t_out = threading.Thread(target=_drain, args=(proc.stdout, out_buf), daemon=True)
    t_err = threading.Thread(target=_drain, args=(proc.stderr, err_buf), daemon=True)
    t_wait = threading.Thread(target=_wait_child, daemon=True)
    timed_out = False
    proc_limit_exceeded = False
    # In `capture` mode, `--_confined-exec` stays in the PGID as a lightweight
    # `PR_SET_PDEATHSIG` supervisor alongside up to `max_procs` capture tasks.
    pgid_cap = (
        max_procs + (1 if confinement == "capture" else 0)
        if max_procs is not None
        else None
    )
    try:
        t_out.start()
        t_err.start()
        t_wait.start()

        deadline = t0 + timeout_secs
        poll_secs = 0.02 if pgid_cap is not None else 0.05
        while not done.is_set():
            if overflowed.is_set():
                _kill_if_unreaped()
                break
            if pgid_cap is not None:
                proc_count = _count_pgid_processes(proc.pid)
                if proc_count is None or proc_count > pgid_cap:
                    proc_limit_exceeded = True
                    _kill_if_unreaped()
                    break
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                timed_out = True
                _kill_if_unreaped()
                break
            done.wait(timeout=min(poll_secs, remaining))
    finally:
        # Always terminate any lingering descendants (including on
        # KeyboardInterrupt or SIGTERM) while `proc.pid` is still pinned
        # (unreaped), then mark `reaped = True` under `kill_lock` before
        # calling `proc.wait()` so no `killpg` can race with PID recycling.
        _kill_if_unreaped()
        if t_wait.is_alive():
            t_wait.join(timeout=5.0)
        _kill_if_unreaped()
        with kill_lock:
            reaped = True
        if cancel_token is not None and cancel_reg is not None:
            cancel_token.unregister(cancel_reg)
        try:
            proc.wait(timeout=5.0)
        except subprocess.TimeoutExpired:
            pass
        if t_out.is_alive():
            t_out.join(timeout=5.0)
        if t_err.is_alive():
            t_err.join(timeout=5.0)

    out = bytes(out_buf).decode("utf-8", errors="replace")
    err = bytes(err_buf).decode("utf-8", errors="replace")
    elapsed = time.monotonic() - t0
    if proc_limit_exceeded:
        return "process_limit", out, err, elapsed
    if overflowed.is_set():
        return "output_limit", out, err, elapsed
    if timed_out:
        return "timeout", out, err, elapsed
    return proc.returncode, out, err, elapsed


def classify_eval_result(
    rc: int | str,
    stdout: str,
    stderr: str,
    *,
    expect_valid: bool,
) -> tuple[str, str | None, str | None]:
    """Cross-check `anneal-mir-eval --json` exit code and structured outcome.

    Recognizes the documented pre-evaluation refusal path where `cmd_eval`
    rejects a program during configuration (e.g., Profile v2 with a big-endian
    target) by exiting with status 3, empty stdout, and a single
    `unsupported program: <reason>` stderr line. Any other non-JSON output or
    exit-code/JSON mismatch fails closed as `tool_error`.
    """
    if not isinstance(rc, int):
        return "tool_error", str(rc), (stderr or stdout)[-300:] or None

    if rc == 3 and not stdout.strip():
        err_lines = [line.strip() for line in stderr.splitlines() if line.strip()]
        if (
            len(err_lines) == 1
            and err_lines[0].startswith("unsupported program:")
        ):
            reason = err_lines[0].removeprefix("unsupported program:").strip()
            if reason:
                return "eval_fail_closed", "pre_eval_unsupported", reason

    try:
        payload = json.loads(stdout)
    except json.JSONDecodeError as exc:
        return "tool_error", "invalid_eval_json", f"rc={rc}: {exc}"

    if not isinstance(payload, dict) or not isinstance(payload.get("outcome"), dict):
        return "tool_error", "missing_outcome", f"rc={rc}"

    outcome = payload["outcome"]
    kind = outcome.get("kind")
    val = outcome.get("value")

    if rc == 0 and kind == "returned" and isinstance(val, dict):
        term_kind = val.get("kind")
        if term_kind == "returned":
            if expect_valid:
                return "accepted_valid", None, None
            return "unsound_accept", "returned", None
        if term_kind == "unwound":
            if expect_valid:
                return "eval_fail_closed", "unexpected_unwind", "unwound (panic)"
            return "unsound_accept", "unwound", "unwound (panic)"
        return "tool_error", "unknown_terminal_kind", repr(term_kind)

    if rc == 2 and kind == "fault" and isinstance(val, dict):
        if val.get("kind") == "undefined":
            reason = str(val.get("reason", ""))
            return "caught_ub", None, reason
        return "tool_error", "rc2_non_undefined", repr(val)

    if rc == 3 and kind == "fault" and isinstance(val, dict):
        if val.get("kind") == "unsupported":
            reason = str(val.get("reason", ""))
            return "eval_fail_closed", "eval_unsupported", reason
        return "tool_error", "rc3_non_unsupported", repr(val)

    if rc == 3 and kind == "out_of_fuel":
        return "eval_fail_closed", "out_of_fuel", "out of fuel"

    if rc == 4 and kind == "aborted":
        if expect_valid:
            return (
                "eval_fail_closed",
                "unexpected_abort",
                "aborted (UnwindAction::Terminate)",
            )
        return (
            "unsound_accept",
            "aborted",
            "aborted (UnwindAction::Terminate)",
        )

    return (
        "tool_error",
        "eval_rc_outcome_mismatch",
        f"rc={rc}, outcome.kind={kind!r}, stderr={stderr[-200:]!r}",
    )


def sanitized_child_env() -> dict[str, str]:
    """Return a child environment with GitHub Actions credentials stripped.

    `anneal-mir-eval` lives under `tools/` (outside `trusted/`), so CI policy
    requires scrubbing Actions cache/runtime tokens before executing it.
    Applying the same scrubber to capture keeps both child paths uniform and
    leaves the `--_confined-exec` trampoline's loader environment clean (any
    caller-controlled sysroot library path is injected only inside confinement
    immediately before the final target `execve`).
    """
    return {
        key: value
        for key, value in os.environ.items()
        if key not in STRIPPED_CI_ENV_VARS
        and not key.startswith(STRIPPED_CI_ENV_PREFIXES)
    }


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


def _count_buckets(units: list[dict[str, object]]) -> dict[str, int]:
    ctr = Counter(str(u.get("bucket", "tool_error")) for u in units)
    counts = {b: ctr.get(b, 0) for b in BUCKETS}
    for key, val in sorted(ctr.items()):
        if key not in counts:
            counts[key] = val
    return counts


def evaluate_tier_a_gate(
    units: list[dict[str, object]],
    *,
    total_files: int,
    pin: dict[str, object],
) -> tuple[bool, list[str], dict[str, int]]:
    """Evaluate Tier A soundness and ratchet invariants fail-closed."""
    counts = _count_buckets(units)
    failures: list[str] = []

    expected_files = int(pin["expected_file_count"])  # type: ignore[arg-type]
    if total_files != expected_files:
        failures.append(
            f"file count mismatch: ran {total_files}, expected {expected_files}"
        )
    if not units:
        failures.append("no Tier A units executed")

    if "expected_unit_count" in pin:
        exp_units_cnt = int(pin["expected_unit_count"])  # type: ignore[arg-type]
        if len(units) != exp_units_cnt:
            failures.append(
                f"unit count mismatch: ran {len(units)}, expected {exp_units_cnt}"
            )

    if "max_harness_skips" in pin:
        max_skips = int(pin["max_harness_skips"])  # type: ignore[arg-type]
        skips = sum(
            1
            for u in units
            if u.get("sub_bucket")
            in ("harness_target", "harness_unforwarded_flags")
        )
        if skips > max_skips:
            failures.append(
                f"harness skips={skips} exceeded max_harness_skips={max_skips}"
            )

    if "max_rustc_or_harness_rejected" in pin:
        max_rejected = int(pin["max_rustc_or_harness_rejected"])  # type: ignore[arg-type]
        rejected = counts.get("rustc_or_harness_rejected", 0)
        if rejected > max_rejected:
            failures.append(
                f"rustc_or_harness_rejected={rejected} exceeded "
                f"max_rustc_or_harness_rejected={max_rejected}"
            )

    unsound = counts.get("unsound_accept", 0)
    if unsound != 0:
        offenders = [
            f"{u['file']}" + (f"[{u['revision']}]" if u.get("revision") else "")
            for u in units
            if u.get("bucket") == "unsound_accept"
        ][:10]
        failures.append(
            f"unsound_accept={unsound} (must be 0): {', '.join(offenders)}"
        )

    tool_errors = counts.get("tool_error", 0)
    if tool_errors != 0:
        offenders = [
            f"{u['file']}" + (f"[{u['revision']}]" if u.get("revision") else "")
            for u in units
            if u.get("bucket") == "tool_error"
        ][:10]
        failures.append(
            f"tool_error={tool_errors} (must be 0): {', '.join(offenders)}"
        )

    min_caught = int(pin["min_caught_ub"])  # type: ignore[arg-type]
    caught = counts.get("caught_ub", 0)
    if caught < min_caught:
        failures.append(
            f"caught_ub={caught} regressed below pinned ratchet "
            f"min_caught_ub={min_caught}"
        )

    if "expected_caught_ub_units" in pin:
        caught_labels = {
            f"{u['file']}" + (f"[{u['revision']}]" if u.get("revision") else "")
            for u in units
            if u.get("bucket") == "caught_ub"
        }
        required_units = [str(x) for x in pin["expected_caught_ub_units"]]  # type: ignore[union-attr]
        missing = sorted(u for u in required_units if u not in caught_labels)
        if missing:
            failures.append(
                f"pinned caught_ub units regressed: {', '.join(missing)}"
            )

    return len(failures) == 0, failures, counts


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


def load_tier_b_manifest(
    tier_b_dir: Path,
    *,
    expected_corpus_sha256: str | None = None,
    min_kind_counts: dict[str, int] | None = None,
    max_entries: int = MAX_TIER_B_DIR_ENTRIES,
    max_depth: int = MAX_CORPUS_DIR_DEPTH,
    snapshot_dir: Path | None = None,
) -> dict[str, object]:
    """Load and validate Tier B manifest, fixture digests, and zero orphans.

    Uses the shared bounded streaming directory walker (`_walk_corpus_tree`) to
    hash `manifest.json` and every `.rs`/`.json` fixture in one pass, enforcing
    symlink/FIFO/depth/entry/size bounds without calling `os.walk`.
    """
    actual_corpus_sha, walked_files = _walk_corpus_tree(
        tier_b_dir,
        [""],
        suffixes=(".rs", ".json"),
        max_entries=max_entries,
        max_depth=max_depth,
        snapshot_dir=snapshot_dir,
        label="Tier B corpus",
    )
    if expected_corpus_sha256 is not None:
        if not hmac.compare_digest(actual_corpus_sha, expected_corpus_sha256):
            raise OracleError(
                f"Tier B corpus SHA-256 mismatch for '{tier_b_dir}': "
                f"expected {expected_corpus_sha256}, got {actual_corpus_sha}"
            )

    active_root = (
        snapshot_dir.resolve() if snapshot_dir is not None else tier_b_dir.resolve()
    )
    manifest_path = active_root / "manifest.json"
    raw_bytes = _read_regular_file_bytes(
        manifest_path, max_bytes=MAX_PIN_BYTES, label="Tier B manifest"
    )
    try:
        data = json.loads(raw_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise OracleError(
            f"failed to load Tier B manifest '{manifest_path}': {exc}"
        ) from exc

    if not isinstance(data, dict):
        raise OracleError("Tier B manifest must be a JSON object")
    if data.get("schema_version") != TIER_B_SCHEMA_VERSION:
        raise OracleError(
            f"unsupported Tier B schema_version: {data.get('schema_version')!r}"
        )
    fixtures = data.get("fixtures")
    if not isinstance(fixtures, list) or not fixtures:
        raise OracleError("Tier B manifest must contain a non-empty fixtures list")

    walked_set = set(walked_files)
    listed_paths: set[str] = set()
    ids: set[str] = set()
    kind_counts: Counter[str] = Counter()
    has_ub_caught = False
    has_valid_control = False

    for entry in fixtures:
        if not isinstance(entry, dict):
            raise OracleError("Tier B fixture entry must be an object")
        fid = entry.get("id")
        rel = entry.get("path")
        kind = entry.get("kind")
        category = entry.get("category")
        if not isinstance(fid, str) or not fid or fid in ids:
            raise OracleError(f"invalid or duplicate Tier B fixture id: {fid!r}")
        ids.add(fid)
        if (
            not isinstance(rel, str)
            or not rel
            or rel.startswith("/")
            or "\\" in rel
            or any(seg in ("", ".", "..") for seg in rel.split("/"))
        ):
            raise OracleError(f"invalid Tier B fixture path: {rel!r}")
        if rel in listed_paths:
            raise OracleError(f"duplicate Tier B fixture path: {rel!r}")
        listed_paths.add(rel)
        if kind not in ALLOWED_TIER_B_KINDS:
            raise OracleError(f"unsupported Tier B fixture kind: {kind!r}")
        kind_counts[kind] += 1
        if not isinstance(category, str) or not category:
            raise OracleError(f"Tier B fixture '{fid}' missing non-empty category")

        cur = active_root
        for part in PurePosixPath(rel).parts:
            cur = cur / part
            if cur.is_symlink():
                raise OracleError(
                    f"Tier B fixture path traverses or is a symlink: {rel!r}"
                )
        if rel not in walked_set or not cur.is_file():
            raise OracleError(f"Tier B fixture missing: {rel!r}")
        fpath = cur.resolve()
        try:
            fpath.relative_to(active_root)
        except ValueError as exc:
            raise OracleError(f"Tier B fixture escapes root: {rel!r}") from exc

        if kind in ("rust_ub_caught", "mir_ub_caught"):
            exp_sub = entry.get("expected_fault_substring")
            if not isinstance(exp_sub, str) or not exp_sub.strip():
                raise OracleError(
                    f"Tier B fixture '{fid}' ({kind}) requires non-empty "
                    f"expected_fault_substring"
                )
            has_ub_caught = True
        if kind in ("rust_valid_control", "mir_valid_control"):
            has_valid_control = True

        if "profile" in entry and entry["profile"] not in ALLOWED_PROFILES:
            raise OracleError(
                f"Tier B fixture '{fid}' has invalid profile: {entry['profile']!r}"
            )
        if "args" in entry:
            raw_args = entry["args"]
            if not isinstance(raw_args, list) or not all(
                isinstance(a, str) for a in raw_args
            ):
                raise OracleError(
                    f"Tier B fixture '{fid}' args must be a list of strings"
                )
        if "fuel" in entry:
            raw_fuel = entry["fuel"]
            if isinstance(raw_fuel, bool) or not isinstance(raw_fuel, int) or raw_fuel < 1:
                raise OracleError(
                    f"Tier B fixture '{fid}' fuel must be a positive integer"
                )
        if "edition" in entry and entry["edition"] not in ("2015", "2018", "2021", "2024"):
            raise OracleError(
                f"Tier B fixture '{fid}' has invalid edition: {entry['edition']!r}"
            )
        if "panic" in entry and entry["panic"] not in ("unwind", "abort"):
            raise OracleError(
                f"Tier B fixture '{fid}' has invalid panic: {entry['panic']!r}"
            )
        if "body" in entry:
            raw_body = entry["body"]
            if not isinstance(raw_body, str) or not raw_body:
                raise OracleError(
                    f"Tier B fixture '{fid}' body must be a non-empty string"
                )

    if not has_ub_caught:
        raise OracleError("Tier B manifest must include at least one *_ub_caught fixture")
    if not has_valid_control:
        raise OracleError(
            "Tier B manifest must include at least one *_valid_control fixture"
        )
    if min_kind_counts is not None:
        for req_kind, floor in sorted(min_kind_counts.items()):
            actual_cnt = kind_counts.get(req_kind, 0)
            if actual_cnt < floor:
                raise OracleError(
                    f"Tier B fixture count for {req_kind!r} regressed "
                    f"({actual_cnt} < pinned {floor})"
                )

    # Reject orphan `.rs` / `.json` fixtures discovered during the single
    # bounded walk so new files cannot be silently ignored by CI.
    disk_fixtures = walked_set - {"manifest.json"}
    orphans = sorted(disk_fixtures - listed_paths)
    if orphans:
        raise OracleError(
            f"Tier B corpus contains unlisted orphan fixtures: {', '.join(orphans)}"
        )

    return data


def evaluate_tier_b_gate(
    results: list[dict[str, object]],
) -> tuple[bool, list[str], dict[str, int]]:
    """Enforce strict per-fixture expectations on Tier B corpus."""
    counts = _count_buckets(results)
    failures: list[str] = []

    if not results:
        failures.append("no Tier B fixtures executed")

    valid_controls_accepted = 0
    ub_caught_verified = 0

    for res in results:
        fid = str(res["id"])
        kind = str(res["kind"])
        bucket = str(res["bucket"])
        detail = str(res.get("detail") or "")
        expected_sub = res.get("expected_fault_substring")

        if kind in ("rust_ub_caught", "mir_ub_caught"):
            if bucket != "caught_ub":
                failures.append(
                    f"{fid} ({kind}): expected caught_ub, got {bucket} ({detail})"
                )
            else:
                if isinstance(expected_sub, str) and expected_sub:
                    if expected_sub.lower() not in detail.lower():
                        failures.append(
                            f"{fid} ({kind}): fault detail {detail!r} missing "
                            f"expected substring {expected_sub!r}"
                        )
                    else:
                        ub_caught_verified += 1
                else:
                    ub_caught_verified += 1
        elif kind == "rust_ub_fail_closed":
            if bucket not in ("caught_ub", "capture_refused", "eval_fail_closed"):
                failures.append(
                    f"{fid} ({kind}): expected caught_ub or fail-closed refusal, "
                    f"got {bucket} ({detail})"
                )
        elif kind in ("rust_valid_control", "mir_valid_control"):
            if bucket != "accepted_valid":
                failures.append(
                    f"{fid} ({kind}): valid control MUST be accepted_valid, "
                    f"got {bucket} ({detail})"
                )
            else:
                valid_controls_accepted += 1
        else:
            failures.append(f"{fid}: unknown kind {kind!r}")

    if ub_caught_verified < 1:
        failures.append("anti-vacuity: zero UB fixtures verified as caught_ub")
    if valid_controls_accepted < 1:
        failures.append("anti-vacuity: zero valid control fixtures accepted")

    return len(failures) == 0, failures, counts


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
