#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Emit JSON metadata for one published Anneal toolchain archive."""

import argparse
import hashlib
import json
from pathlib import Path


def sha256_file(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--archive", required=True, type=Path)
    parser.add_argument("--target", required=True)
    parser.add_argument("--os", required=True)
    parser.add_argument("--arch", required=True)
    parser.add_argument("--url", required=True)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()

    archive = args.archive.resolve()
    if not archive.is_file():
        raise SystemExit(f"archive does not exist: {archive}")

    metadata = {
        "target": args.target,
        "os": args.os,
        "arch": args.arch,
        "filename": archive.name,
        "sha256": sha256_file(archive),
        "url": args.url,
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
