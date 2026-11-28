# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Verification of the vendored MiniRust specification pin."""

from __future__ import annotations

import json
import os
from pathlib import Path
import stat
from typing import Any

from .common import (
    EXPECTED_UPSTREAM_REPO, FORBIDDEN_VENDOR_NAMES, HEX40_RE, HEX64_RE,
    LOCKED_MINIRUST_COMMIT, LOCKED_MINIRUST_FILE_COUNT,
    LOCKED_MINIRUST_MANIFEST_SHA256, LOCKED_MINIRUST_TARBALL_SHA256,
    PIN_FILENAME, VerificationError, _compute_manifest_sha256,
    _no_duplicate_json_keys, _require_regular_file, _resolve_regular_dir,
    _sha256_file, _validate_clean_rel_path, _walk_error, _walk_non_symlink_dirs,
)


def verify_vendor_pin(
    repo_root: Path, *, enforce_locked_pin: bool = True
) -> dict[str, Any]:
    """Verify `vendor/minirust/UPSTREAM_PIN.json` and every file on disk."""
    real_root = _resolve_regular_dir(repo_root, "repo root")
    vendor_dir = _walk_non_symlink_dirs(real_root, ("vendor", "minirust"))
    pin_path = _require_regular_file(
        vendor_dir / PIN_FILENAME, f"vendor/minirust/{PIN_FILENAME}"
    )

    try:
        raw_pin = json.loads(
            pin_path.read_text(encoding="utf-8"),
            object_pairs_hook=_no_duplicate_json_keys,
        )
    except (
        OSError,
        UnicodeDecodeError,
        json.JSONDecodeError,
        ValueError,
    ) as exc:
        raise VerificationError(f"cannot parse {pin_path}: {exc}") from exc

    if not isinstance(raw_pin, dict):
        raise VerificationError(f"{pin_path}: top-level JSON must be an object")

    schema_ver = raw_pin.get("schema_version")
    if isinstance(schema_ver, bool) or schema_ver != 1:
        raise VerificationError(
            f"{pin_path}: schema_version must be 1, got {schema_ver!r}"
        )

    upstream_repo = raw_pin.get("upstream_repo")
    if upstream_repo != EXPECTED_UPSTREAM_REPO:
        raise VerificationError(
            f"{pin_path}: upstream_repo must be {EXPECTED_UPSTREAM_REPO!r}, "
            f"got {upstream_repo!r}"
        )

    commit = raw_pin.get("commit")
    if not isinstance(commit, str) or not HEX40_RE.match(commit):
        raise VerificationError(
            f"{pin_path}: commit must be a 40-char lowercase hex SHA, "
            f"got {commit!r}"
        )
    if enforce_locked_pin and commit != LOCKED_MINIRUST_COMMIT:
        raise VerificationError(
            f"{pin_path}: commit {commit!r} does not match "
            f"LOCKED_MINIRUST_COMMIT {LOCKED_MINIRUST_COMMIT!r}"
        )

    tarball_sha = raw_pin.get("tarball_sha256")
    if not isinstance(tarball_sha, str) or not HEX64_RE.match(tarball_sha):
        raise VerificationError(
            f"{pin_path}: tarball_sha256 must be a 64-char lowercase hex SHA, "
            f"got {tarball_sha!r}"
        )
    if enforce_locked_pin and tarball_sha != LOCKED_MINIRUST_TARBALL_SHA256:
        raise VerificationError(
            f"{pin_path}: tarball_sha256 {tarball_sha!r} does not match "
            "LOCKED_MINIRUST_TARBALL_SHA256 "
            f"{LOCKED_MINIRUST_TARBALL_SHA256!r}"
        )

    raw_files = raw_pin.get("files")
    if not isinstance(raw_files, dict) or not raw_files:
        raise VerificationError(
            f"{pin_path}: files must be a non-empty JSON object"
        )

    file_keys = list(raw_files.keys())
    if file_keys != sorted(file_keys):
        raise VerificationError(
            f"{pin_path}: files map keys must be sorted lexicographically"
        )

    pinned_files: dict[str, str] = {}
    allowed_dirs: set[str] = set()
    for rel_key, digest in raw_files.items():
        rel_path = _validate_clean_rel_path(rel_key, str(pin_path))
        if not isinstance(digest, str) or not HEX64_RE.match(digest):
            raise VerificationError(
                f"{pin_path}: invalid SHA-256 digest for {rel_path!r}: "
                f"{digest!r}"
            )
        pinned_files[rel_path] = digest
        parts = rel_path.split("/")
        for depth in range(1, len(parts)):
            allowed_dirs.add("/".join(parts[:depth]))

    if "file_count" not in raw_pin:
        raise VerificationError(f"{pin_path}: missing required key 'file_count'")
    fc = raw_pin["file_count"]
    if isinstance(fc, bool) or not isinstance(fc, int) or fc != len(pinned_files):
        raise VerificationError(
            f"{pin_path}: file_count ({fc!r}) does not match "
            f"len(files) ({len(pinned_files)})"
        )

    if "manifest_sha256" not in raw_pin:
        raise VerificationError(
            f"{pin_path}: missing required key 'manifest_sha256'"
        )
    expected_manifest = _compute_manifest_sha256(pinned_files)
    actual_manifest = raw_pin["manifest_sha256"]
    if actual_manifest != expected_manifest:
        raise VerificationError(
            f"{pin_path}: manifest_sha256 mismatch: "
            f"recorded {actual_manifest!r}, computed {expected_manifest!r}"
        )

    disk_files: set[str] = set()
    disk_dirs: set[str] = set()
    for dirpath, dirnames, filenames in os.walk(
        vendor_dir, followlinks=False, onerror=_walk_error
    ):
        base = Path(dirpath)
        for name in sorted(dirnames) + sorted(filenames):
            entry = base / name
            mode = entry.lstat().st_mode
            rel = entry.relative_to(vendor_dir).as_posix()
            if stat.S_ISLNK(mode):
                raise VerificationError(
                    f"symlink forbidden in vendor/minirust: {rel}"
                )
            if name.lower() in FORBIDDEN_VENDOR_NAMES:
                raise VerificationError(
                    "forbidden ambient/build/toolchain name in "
                    f"vendor/minirust: {rel}"
                )
            if stat.S_ISDIR(mode):
                disk_dirs.add(rel)
            elif stat.S_ISREG(mode):
                if rel != PIN_FILENAME:
                    disk_files.add(rel)
            else:
                raise VerificationError(
                    f"unexpected special file in vendor/minirust: {rel}"
                )

    extra_files = sorted(disk_files - set(pinned_files))
    if extra_files:
        raise VerificationError(
            "extra unpinned file(s) in vendor/minirust: "
            + ", ".join(extra_files)
        )

    missing_files = sorted(set(pinned_files) - disk_files)
    if missing_files:
        raise VerificationError(
            "missing pinned file(s) in vendor/minirust: "
            + ", ".join(missing_files)
        )

    stray_dirs = sorted(disk_dirs - allowed_dirs)
    if stray_dirs:
        raise VerificationError(
            "unpinned directory(ies) in vendor/minirust: "
            + ", ".join(stray_dirs)
        )

    for rel_path, expected_sha in pinned_files.items():
        parts = tuple(rel_path.split("/"))
        parent = _walk_non_symlink_dirs(vendor_dir, parts[:-1])
        leaf = _require_regular_file(parent / parts[-1], rel_path)
        actual_sha = _sha256_file(leaf)
        if actual_sha != expected_sha:
            raise VerificationError(
                f"SHA-256 mismatch for vendor/minirust/{rel_path}: "
                f"expected {expected_sha}, got {actual_sha}"
            )

    if enforce_locked_pin:
        if len(pinned_files) != LOCKED_MINIRUST_FILE_COUNT:
            raise VerificationError(
                f"{pin_path}: pinned file count {len(pinned_files)} does not "
                f"match LOCKED_MINIRUST_FILE_COUNT {LOCKED_MINIRUST_FILE_COUNT}"
            )
        if actual_manifest != LOCKED_MINIRUST_MANIFEST_SHA256:
            raise VerificationError(
                f"{pin_path}: manifest_sha256 {actual_manifest!r} does not "
                "match LOCKED_MINIRUST_MANIFEST_SHA256 "
                f"{LOCKED_MINIRUST_MANIFEST_SHA256!r}"
            )

    return raw_pin
