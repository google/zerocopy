#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Explicitly refresh existing root-manifest hashes after reviewing changes.

Preserve the manifest's comments, file list, order, and formatting.
Builds and checks must verify the manifest without running this updater.
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


# The existing file list is the reviewed TCB coverage. Hash refreshes must
# preserve that decision rather than discover a different set of inputs.
def refreshed_manifest(root, manifest):
    lines = manifest.read_bytes().splitlines(keepends=True)
    output = []
    covered = set()
    for number, line in enumerate(lines, 1):
        if line.startswith(b"#") or not line.strip():
            output.append(line)
            continue
        match = re.fullmatch(rb"[0-9a-f]{64}( [ *])([^\r\n]+)(\r?\n)?", line)
        if match is None:
            raise ManifestError(f"line {number}: malformed checksum entry")
        name = match[2].decode("utf-8")
        path = PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts or str(path) != name:
            raise ManifestError(f"line {number}: expected a canonical relative path")
        if name in covered:
            raise ManifestError(f"line {number}: duplicate covered file: {name}")
        covered.add(name)
        source = root / name
        if (source.is_symlink() or not source.is_file()
                or not source.resolve().is_relative_to(root)
                or source.resolve() == manifest.resolve()):
            raise ManifestError(f"line {number}: missing or invalid covered file: {name}")
        digest = hashlib.sha256(source.read_bytes()).hexdigest().encode("ascii")
        output.append(digest + line[64:])
    if not covered:
        raise ManifestError("manifest contains no checksum entries")
    return b"".join(output)


def update(root):
    manifest = root / "trusted/root-manifest.sha256"
    if (manifest.is_symlink() or not manifest.is_file()
            or not manifest.resolve().is_relative_to(root)):
        raise ManifestError(f"expected an existing regular manifest: {manifest}")
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
