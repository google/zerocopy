#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Explicitly refresh existing root-manifest hashes after reviewing changes.

Preserve the manifest's comments, file list, order, and two-space text-mode
checksum formatting (`<sha256>  <path>`), matching `anneal-audit`. Builds and
checks must verify the manifest without running this updater.
"""

import argparse
import hashlib
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys
import tempfile


class ManifestError(Exception):
    """The manifest cannot be refreshed while preserving its coverage."""


def is_bidi_or_invisible_control(ch):
    """Match `anneal-audit` (`is_bidi_or_invisible_control`)."""
    code = ord(ch)
    return (
        (code <= 0x001F and ch not in ("\n", "\r", "\t"))
        or 0x007F <= code <= 0x009F
        or code == 0x00AD
        or code == 0x034F
        or 0x0600 <= code <= 0x0605
        or code == 0x061C
        or code == 0x06DD
        or code == 0x070F
        or 0x0890 <= code <= 0x0891
        or code == 0x08E2
        or 0x115F <= code <= 0x1160
        or 0x17B4 <= code <= 0x17B5
        or 0x180B <= code <= 0x180F
        or 0x200B <= code <= 0x200F
        or 0x2028 <= code <= 0x202E
        or 0x2060 <= code <= 0x206F
        or code == 0x3164
        or 0xFE00 <= code <= 0xFE0F
        or code == 0xFEFF
        or code == 0xFFA0
        or 0xFFF0 <= code <= 0xFFFB
        or code == 0x110BD
        or code == 0x110CD
        or 0x13430 <= code <= 0x1343F
        or 0x1BCA0 <= code <= 0x1BCA3
        or 0x1D173 <= code <= 0x1D17A
        or 0xE0000 <= code <= 0xE0FFF
    )


def is_canonical_ascii_rel_path(rel):
    """Match `anneal-audit` (`is_canonical_ascii_rel_path`)."""
    return bool(rel) and all(
        seg
        and seg not in (".", "..")
        and not seg.endswith(".")
        and all(0x21 <= ord(ch) <= 0x7E and ch not in ("\\", ":", "~") for ch in seg)
        for seg in rel.split("/")
    )


def verify_exact_case_entry(directory, segment, label, missing_msg=None):
    """Require `segment` to match an on-disk directory entry with exact case."""
    try:
        entries = os.listdir(directory)
    except OSError as error:
        if missing_msg is not None:
            raise ManifestError(missing_msg) from error
        raise ManifestError(f"{label}: {error}") from error
    if segment in entries:
        return
    folded = next((entry for entry in entries if entry.lower() == segment.lower()), None)
    if folded is not None:
        raise ManifestError(
            f"{label}: case-folded path alias forbidden: requested '{segment}', found '{folded}'"
        )
    if missing_msg is not None:
        raise ManifestError(missing_msg)
    raise ManifestError(f"{label}: missing path entry: {directory / segment}")


def split_manifest_records(raw_bytes):
    """Split `raw_bytes` strictly on `LF`/`CRLF`, matching Rust `str::lines`."""
    records = []
    start = 0
    while start < len(raw_bytes):
        newline = raw_bytes.find(b"\n", start)
        if newline == -1:
            record = raw_bytes[start:]
            start = len(raw_bytes)
        else:
            record = raw_bytes[start : newline + 1]
            start = newline + 1
        if record.endswith(b"\r\n"):
            body = record[:-2]
        elif record.endswith(b"\n"):
            body = record[:-1]
        else:
            body = record
        if b"\r" in body:
            raise ManifestError(
                f"line {len(records) + 1}: bare carriage return forbidden in root manifest"
            )
        records.append((record, body))
    return records


def validate_real_file(root, rel_path, label, missing_msg=None):
    """Require every parent component under `root` to be a real directory and the
    leaf to be a single-link regular file inside `root` with exact path case.
    """
    if rel_path.is_absolute() or ".." in rel_path.parts or not rel_path.parts:
        raise ManifestError(f"{label}: expected a canonical relative path")
    cur = root
    try:
        for segment in rel_path.parts[:-1]:
            verify_exact_case_entry(cur, segment, label, missing_msg=missing_msg)
            cur = cur / segment
            parent_stat = cur.lstat()
            if not stat.S_ISDIR(parent_stat.st_mode):
                raise ManifestError(f"{label}: expected a regular directory: {cur}")
        verify_exact_case_entry(cur, rel_path.parts[-1], label, missing_msg=missing_msg)
        leaf = cur / rel_path.parts[-1]
        leaf_stat = leaf.lstat()
    except OSError as error:
        if missing_msg is not None:
            raise ManifestError(missing_msg) from error
        raise ManifestError(f"{label}: {error}") from error
    if not stat.S_ISREG(leaf_stat.st_mode) or leaf_stat.st_nlink != 1:
        if missing_msg is not None:
            raise ManifestError(missing_msg)
        raise ManifestError(f"{label}: expected a single-link regular file: {leaf}")
    resolved = leaf.resolve()
    if not resolved.is_relative_to(root):
        if missing_msg is not None:
            raise ManifestError(missing_msg)
        raise ManifestError(f"{label}: escapes repository root: {leaf}")
    return leaf, resolved


# The existing file list is the reviewed TCB coverage. Hash refreshes must
# preserve that decision rather than discover a different set of inputs.
def refreshed_manifest(root, manifest):
    raw_bytes = manifest.read_bytes()
    decoded = raw_bytes.decode("utf-8")
    if decoded.startswith("\ufeff"):
        raise ManifestError("UTF-8 BOM forbidden in root manifest")
    if any(is_bidi_or_invisible_control(ch) for ch in decoded):
        raise ManifestError("manifest contains disallowed bidi or invisible control characters")
    records = split_manifest_records(raw_bytes)
    output = []
    covered = set()
    manifest_resolved = manifest.resolve()
    for number, (line, body) in enumerate(records, 1):
        if body.startswith(b"#") or not body.strip(b" \t\n\r\x0c"):
            output.append(line)
            continue
        # Match `anneal-audit` (`verify_root_manifest_sha256`): require the
        # two-space text-mode separator (`  `) and reject binary-mode (` *`)
        # markers so refreshed manifests never diverge from standalone audits.
        match = re.fullmatch(rb"[0-9a-f]{64}  (\S+)(\r?\n)?", line)
        if match is None:
            raise ManifestError(f"line {number}: malformed checksum entry")
        name = match[1].decode("utf-8")
        if not is_canonical_ascii_rel_path(name):
            raise ManifestError(
                f"line {number}: expected a canonical printable-ASCII relative path: {name}"
            )
        path = PurePosixPath(name)
        if name in covered:
            raise ManifestError(f"line {number}: duplicate covered file: {name}")
        covered.add(name)
        source, source_resolved = validate_real_file(
            root, path, f"line {number}: missing or invalid covered file ({name})"
        )
        if source_resolved == manifest_resolved:
            raise ManifestError(f"line {number}: missing or invalid covered file: {name}")
        digest = hashlib.sha256(source.read_bytes()).hexdigest().encode("ascii")
        output.append(digest + line[64:])
    if not covered:
        raise ManifestError("manifest contains no checksum entries")
    return b"".join(output)


def update(root):
    manifest_rel = PurePosixPath("trusted/root-manifest.sha256")
    manifest, _ = validate_real_file(
        root,
        manifest_rel,
        "root manifest",
        missing_msg=f"expected an existing regular manifest: {root / manifest_rel}",
    )
    original = manifest.read_bytes()
    refreshed = refreshed_manifest(root, manifest)
    if original == refreshed:
        return False
    # Prepare every hash before replacing the manifest. A missing input must
    # leave both the coverage and the original checksum bytes intact.
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=manifest.parent, delete=False) as file:
            temporary = Path(file.name)
            file.write(refreshed)
            os.fchmod(file.fileno(), stat.S_IMODE(manifest.stat().st_mode))
        os.replace(temporary, manifest)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return True


def main():
    arguments = argparse.ArgumentParser(description=__doc__)
    arguments.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    root = arguments.parse_args().root.resolve()
    try:
        changed = update(root)
    except (OSError, UnicodeError, ManifestError) as error:
        print(f"cannot refresh root manifest: {error}", file=sys.stderr)
        return 1
    print("Updated root-manifest hashes." if changed else "Root-manifest hashes unchanged.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
