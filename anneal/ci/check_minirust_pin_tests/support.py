# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared imports, paths, and fixture builders for the
`check_minirust_pin.py` tests."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import tomllib

import check_minirust_pin


SCRIPT = Path(__file__).resolve().parent.parent / "check_minirust_pin.py"
ANNEAL_ROOT = Path(__file__).resolve().parent.parent.parent


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _minimal_required_proof_lean() -> str:
    lines = [
        "import Trusted.MirSemantics",
        "namespace Anneal.MiniRustProof",
    ]
    for qual in check_minirust_pin.REQUIRED_EXPORTED_THEOREMS:
        short = qual.removeprefix("Anneal.MiniRustProof.")
        lines.append(f"theorem {short} : True := trivial")
    lines.append("end Anneal.MiniRustProof")
    return "\n".join(lines) + "\n"


def _make_tree_writable(root: Path) -> None:
    """Ensure copied fixture files and directories are owner-writable."""
    for dirpath, _, filenames in os.walk(root, topdown=True, followlinks=False):
        dp = Path(dirpath)
        dp.chmod(
            stat.S_IMODE(dp.stat().st_mode)
            | stat.S_IRUSR
            | stat.S_IWUSR
            | stat.S_IXUSR
        )
        for name in filenames:
            fp = dp / name
            if not fp.is_symlink():
                fp.chmod(
                    stat.S_IMODE(fp.stat().st_mode)
                    | stat.S_IRUSR
                    | stat.S_IWUSR
                )


def populate_valid_repo(
    root: Path,
    *,
    source_root: Path | None = None,
    spec_files: dict[str, str] | None = None,
    lean_files: dict[str, str] | None = None,
    proof_lean: str | None = None,
) -> dict[str, str]:
    """Create a valid Anneal fixture with pinned MiniRust files.

    When `spec_files` is `None`, copies the real locked 30-file
    `vendor/minirust/` tree so CLI invocations exercise the locked commit,
    file count, and manifest SHA-256 without any bypass flags.
    """
    vendor_dir = root / "vendor/minirust"
    if spec_files is None:
        src_root = ANNEAL_ROOT if source_root is None else source_root
        shutil.copytree(src_root / "vendor/minirust", vendor_dir)
        _make_tree_writable(vendor_dir)
        pin_data = json.loads(
            (vendor_dir / "UPSTREAM_PIN.json").read_text(encoding="utf-8")
        )
        files_map: dict[str, str] = dict(pin_data["files"])
    else:
        vendor_dir.mkdir(parents=True, exist_ok=True)
        files_map = {}
        for rel, content in sorted(spec_files.items()):
            target = vendor_dir / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            raw = content.encode("utf-8")
            target.write_bytes(raw)
            files_map[rel] = _sha256_bytes(raw)

        manifest_sha = check_minirust_pin._compute_manifest_sha256(files_map)
        pin = {
            "schema_version": 1,
            "upstream_repo": check_minirust_pin.EXPECTED_UPSTREAM_REPO,
            "commit": check_minirust_pin.LOCKED_MINIRUST_COMMIT,
            "tarball_sha256": check_minirust_pin.LOCKED_MINIRUST_TARBALL_SHA256,
            "file_count": len(files_map),
            "manifest_sha256": manifest_sha,
            "files": files_map,
        }
        (vendor_dir / "UPSTREAM_PIN.json").write_text(
            json.dumps(pin, indent=2) + "\n", encoding="utf-8"
        )

    if lean_files is not None or proof_lean is not None:
        minirust_corr = root / "correspondence/Anneal/MiniRust"
        minirust_corr.mkdir(parents=True, exist_ok=True)
        if lean_files is None:
            lean_files = {
                "Syntax.lean": (
                    "import Trusted.MirAst\n"
                    "namespace Anneal.MiniRust\n"
                    "def okDecl : Nat := 1\n"
                    "end Anneal.MiniRust\n"
                ),
            }
        for rel, content in lean_files.items():
            target = minirust_corr / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content, encoding="utf-8")

        if proof_lean is None:
            proof_lean = _minimal_required_proof_lean()
        (root / "correspondence/Anneal/MiniRustProof.lean").write_text(
            proof_lean, encoding="utf-8"
        )

    return files_map


def write_fake_lean(path: Path, body: str) -> Path:
    """Create an executable Python stub acting as `--lean`."""
    path.write_text(f"#!{sys.executable}\n{body}", encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path
