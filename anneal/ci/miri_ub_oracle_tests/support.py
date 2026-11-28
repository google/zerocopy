# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared imports, paths, and archive and pin helpers for the Miri UB
oracle tests."""

from __future__ import annotations

import hashlib
import io
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tarfile
import tempfile
import unittest

import run_miri_ub_oracle as oracle

# Tests that patch a module-level name patch it where the code under test reads
# it, which is the `miri_ub_oracle_lib` module that defines or imports it.
from miri_ub_oracle_lib import archive as oracle_archive
from miri_ub_oracle_lib import bounded as oracle_bounded
from miri_ub_oracle_lib import corpus as oracle_corpus
from miri_ub_oracle_lib import evaluate as oracle_evaluate
from miri_ub_oracle_lib import landlock as oracle_landlock
from miri_ub_oracle_lib import pins as oracle_pins
from miri_ub_oracle_lib import tiers as oracle_tiers


CI_DIR = Path(__file__).resolve().parent.parent
ANNEAL_DIR = CI_DIR.parent


def _make_tar_gz(dest: Path, entries: list[tuple[str, bytes | str, bytes]]) -> str:
    """Build a .tar.gz with explicit TarInfo types; return its SHA-256."""
    with tarfile.open(dest, "w:gz") as tf:
        for name, payload, mtype in entries:
            info = tarfile.TarInfo(name=name)
            info.type = mtype
            if mtype == tarfile.REGTYPE:
                raw = payload.encode("utf-8") if isinstance(payload, str) else payload
                info.size = len(raw)
                tf.addfile(info, io.BytesIO(raw))
            elif mtype in (tarfile.SYMTYPE, tarfile.LNKTYPE):
                info.linkname = payload if isinstance(payload, str) else payload.decode("utf-8")
                tf.addfile(info)
            else:
                tf.addfile(info)
    return hashlib.sha256(dest.read_bytes()).hexdigest()


def _write_executable(path: Path, content: str) -> None:
    path.write_text(content, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)


def _sample_pin(
    *,
    miri_commit: str = "a" * 40,
    archive_sha: str = "b" * 64,
    manifest_sha: str = "c" * 64,
    expected_file_count: int = 2,
    min_caught_ub: int = 1,
) -> dict[str, object]:
    return {
        "schema_version": 1,
        "upstream_repo": "rust-lang/miri",
        "miri_commit": miri_commit,
        "rustc_toolchain_channel": "nightly-2026-05-31",
        "rustc_commit": "f" * 40,
        "miri_tree_sha": "3" * 40,
        "fail_tree_sha": "1" * 40,
        "fail_dep_tree_sha": "2" * 40,
        "archive_url": f"https://github.com/rust-lang/miri/archive/{miri_commit}.tar.gz",
        "archive_sha256": archive_sha,
        "expected_top_dir": f"miri-{miri_commit}",
        "extract_subdirs": ["tests/fail", "tests/fail-dep"],
        "expected_file_count": expected_file_count,
        "corpus_manifest_sha256": manifest_sha,
        "target": "x86_64-unknown-linux-gnu",
        "capture_scope": "crate",
        "fuel": 2000000,
        "profile": "auto",
        "max_unsound_accepts": 0,
        "max_tool_errors": 0,
        "min_caught_ub": min_caught_ub,
    }
