# Copyright 2026 The Fuchsia Authors
# SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
"""Use the preserved, checksum-verified pointer export instead of comment text."""
import gzip
import hashlib
from pathlib import Path

import prepare


def preserved_patch(pr, comment_id, digest, length):
    if pr != 3677:
        raise RuntimeError("This retry is limited to the pointer PR")
    path = Path(__file__).resolve().parent / "3677-pointer-implementation.patch.gz"
    with gzip.open(path, "rb") as source:
        patch = source.read(length + 1)
    if len(patch) != length or hashlib.sha256(patch).hexdigest() != digest:
        raise RuntimeError("Preserved patch failed byte-count or SHA-256 verification")
    return patch


prepare.patch_from_comment = preserved_patch
prepare.main()
