# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Paths, limits, schema versions, and shared validation helpers for the
Miri UB oracle."""

from __future__ import annotations

import errno
import os
from pathlib import Path
import re
import stat


CI_DIR = Path(__file__).resolve().parent.parent
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
