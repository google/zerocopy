#!/usr/bin/env python3
"""Inventory report-package files for exact offline v91 staging checks."""
import argparse
import hashlib
import json
from pathlib import Path

from build_delta import LEAN, RUST, SUPPORT


def inventory(root):
    files = {}
    for path in sorted(root.rglob("*")):
        if "__pycache__" in path.parts or path.name == ".DS_Store":
            continue
        if path.is_symlink():
            raise ValueError(f"unexpected symlink: {path}")
        if path.is_file():
            data = path.read_bytes()
            files[path.relative_to(root).as_posix()] = {
                "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
    assert "REPORT.md" in files and "REPORT.json" in files
    return files


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--lean-package-dir", required=True, type=Path)
    p.add_argument("--rust-package-dir", required=True, type=Path)
    a = p.parse_args()
    result = {
        LEAN.split("/")[1]: inventory(a.lean_package_dir),
        RUST.split("/")[1]: inventory(a.rust_package_dir),
    }
    (SUPPORT / "source-package-hashes.json").write_text(json.dumps(result, indent=2) + "\n")
    print("Frozen", *(f"{name}: {len(files)} files" for name, files in result.items()))


if __name__ == "__main__":
    main()
