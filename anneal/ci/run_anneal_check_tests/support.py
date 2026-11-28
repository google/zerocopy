# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Paths, script-text helpers, and shared-library fixtures for the
`run_anneal_check.sh` and `pack_omnibus_archive.sh` tests."""

import ctypes
import functools
import hashlib
import os
from pathlib import Path
import re
import sys


ANNEAL_ROOT = Path(__file__).resolve().parent.parent.parent
REPO_ROOT = ANNEAL_ROOT.parent
SCRIPT = ANNEAL_ROOT / "ci" / "run_anneal_check.sh"
PACK_SCRIPT = ANNEAL_ROOT / "ci" / "pack_omnibus_archive.sh"
CHECK_BUNDLE_TREE = ANNEAL_ROOT / "ci" / "check_bundle_tree.py"
FLAKE = ANNEAL_ROOT / "flake.nix"
CHECKS_TOML = REPO_ROOT / "ci" / "checks.toml"
ANNEAL_TC_DOCKERFILE = REPO_ROOT / "ci" / "docker" / "anneal-tc.Dockerfile"


def shell_function(text: str, name: str) -> str:
    match = re.search(rf"^{name}\(\) \{{\n.*?^\}}\n", text, re.M | re.S)
    if match is None:
        raise AssertionError(f"function {name} not found")
    return match.group(0)


def case_branch(text: str, label: str) -> str:
    match = re.search(rf"^  {re.escape(label)}\)\n(.*?)^    ;;$", text, re.M | re.S)
    if match is None:
        raise AssertionError(f"case branch {label!r} not found")
    return match.group(1)


@functools.lru_cache(maxsize=None)
def _linux_shared_lib_bytes(soname: str) -> bytes:
    """Return valid host ELF shared-library bytes for `soname` on Linux."""
    if not sys.platform.startswith("linux"):
        return b""
    try:
        ctypes.CDLL(soname)
    except OSError:
        pass
    stem = soname.split(".so", 1)[0] + ".so"
    maps_path = Path("/proc/self/maps")
    if maps_path.is_file():
        for line in maps_path.read_text(encoding="utf-8", errors="replace").splitlines():
            parts = line.strip().split(None, 5)
            if len(parts) < 6 or not parts[5].startswith("/"):
                continue
            cand = Path(parts[5])
            if (cand.name == soname or cand.name.startswith(stem)) and cand.is_file():
                data = cand.read_bytes()
                if data.startswith(b"\x7fELF"):
                    return data
    for lib_dir in (
        "/lib/x86_64-linux-gnu",
        "/usr/lib/x86_64-linux-gnu",
        "/lib/aarch64-linux-gnu",
        "/usr/lib/aarch64-linux-gnu",
        "/lib64",
        "/usr/lib64",
        "/lib",
        "/usr/lib",
    ):
        cand = Path(lib_dir) / soname
        if cand.is_file():
            data = cand.read_bytes()
            if data.startswith(b"\x7fELF"):
                return data
    return b""


def _tagged_shared_lib_bytes(soname: str, tag: bytes, *, platform: str) -> bytes:
    prefix = _linux_shared_lib_bytes(soname) if platform == "linux" else b""
    return (prefix + b"\n" + tag) if prefix else tag


def tree_digest(tree_dir: Path) -> str:
    files = []
    for cur, _dirs, names in os.walk(tree_dir, followlinks=False):
        cur_p = Path(cur)
        for name in names:
            fp = cur_p / name
            files.append((fp.relative_to(tree_dir).as_posix(), fp))
    files.sort(key=lambda item: item[0].encode("utf-8"))
    h = hashlib.sha256()
    for rel, fp in files:
        fh = hashlib.sha256(fp.read_bytes())
        h.update(rel.encode("utf-8"))
        h.update(b"\0")
        h.update(fh.digest())
    return h.hexdigest()
