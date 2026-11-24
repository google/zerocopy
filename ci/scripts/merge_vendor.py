#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Merge multiple Cargo vendor trees without clobbering shared crate names."""

import os
from pathlib import Path
import shutil
import sys
import tomllib


def read_pkg_id(crate_dir: Path) -> tuple[str, str]:
    manifest = crate_dir / "Cargo.toml"
    with manifest.open("rb") as handle:
        data = tomllib.load(handle)
    pkg = data.get("package")
    if not isinstance(pkg, dict):
        raise SystemExit(f"{manifest}: missing [package] table")
    name = pkg.get("name")
    version = pkg.get("version")
    if not isinstance(name, str) or not isinstance(version, str):
        raise SystemExit(f"{manifest}: missing string package name/version")
    return name, version


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        raise SystemExit(
            f"usage: {argv[0]} <src-vendor-1> [<src-vendor-2> ...] <dest-dir>"
        )
    src_dirs = [Path(p) for p in argv[1:-1]]
    dest_dir = Path(argv[-1])

    if dest_dir.exists():
        shutil.rmtree(dest_dir)
    dest_dir.mkdir(parents=True, exist_ok=True)

    seen: dict[tuple[str, str], Path] = {}
    for src in src_dirs:
        if not src.is_dir():
            raise SystemExit(f"vendor directory does not exist: {src}")
        for entry in sorted(src.iterdir()):
            if not entry.is_dir():
                continue
            if not (entry / "Cargo.toml").is_file():
                continue
            pkg_id = read_pkg_id(entry)
            if pkg_id in seen:
                continue
            seen[pkg_id] = entry
            name, version = pkg_id
            link_path = dest_dir / f"{name}-{version}"
            if link_path.exists() or link_path.is_symlink():
                raise SystemExit(f"duplicate vendor entry path: {link_path}")
            os.symlink(entry.resolve(), link_path)

    if not seen:
        raise SystemExit("merged vendor directory is empty")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
