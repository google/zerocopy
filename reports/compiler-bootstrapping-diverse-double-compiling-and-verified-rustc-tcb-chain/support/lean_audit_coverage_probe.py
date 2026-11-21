#!/usr/bin/env python3
"""Which files of a Lean 4 toolchain do the digests checked by the Anneal
trusted audit actually cover?

Usage:
    python3 lean_audit_coverage_probe.py --prefix <lean toolchain prefix> \
        --audit-src <path to trusted/audit/src/lib.rs of joshlf/anneal>

The probe re-implements, in Python, the manifest computed by
`verify_sysroot_foundation_dir` in that Rust file (at revision
c131b320eeeb26ef692e5afd5ec8db49ee518613, lines 1647-1749):

  * for pkg in Init, Std, Lean: every existing `lib/lean/<pkg>.<ext>` and every
    regular file below `lib/lean/<pkg>/` whose relative path ends in `.<ext>`,
    with ext in `.olean`, `.olean.server`, `.olean.private`;
  * the manifest is the concatenation of `"<rel path>:<lowercase sha256>\n"`
    in byte-wise order of the relative path; its SHA-256 is compared with the
    constant `LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`.

Both pinned values (`LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256` and the four
`LOCKED_LEAN_SHA256` launcher digests) are read from `--audit-src`; none is
hardcoded here. The probe then lists every ELF file that `bin/lean` loads from
inside the prefix and reports whether either pinned value covers it, and counts
the GMP entry points (`__gmp*`) each of those files defines.

Linux/ELF only (uses `ldd` and `nm`). Everything printed is measured on the
given prefix.
"""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time

OLEAN_PARTS = ("olean", "olean.server", "olean.private")
PACKAGES = ("Init", "Std", "Lean")


def sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def is_elf(path: str) -> bool:
    with open(path, "rb") as f:
        return f.read(4) == b"\x7fELF"


def manifest(lib_dir: str) -> dict:
    entries = {}
    symlinks = []
    for pkg in PACKAGES:
        for ext in OLEAN_PARTS:
            rel = f"{pkg}.{ext}"
            path = os.path.join(lib_dir, rel)
            if os.path.lexists(path):
                entries[rel] = path
        for root, dirs, files in os.walk(os.path.join(lib_dir, pkg), followlinks=False):
            for name in dirs + files:
                if os.path.islink(os.path.join(root, name)):
                    symlinks.append(os.path.relpath(os.path.join(root, name), lib_dir))
            for name in files:
                path = os.path.join(root, name)
                rel = os.path.relpath(path, lib_dir).replace(os.sep, "/")
                if any(rel.endswith("." + ext) for ext in OLEAN_PARTS):
                    entries[rel] = path
    lines = []
    total = 0
    elf = 0
    for rel in sorted(entries, key=lambda s: s.encode("utf-8")):
        path = entries[rel]
        total += os.path.getsize(path)
        elf += is_elf(path)
        lines.append(f"{rel}:{sha256(path)}\n")
    text = "".join(lines).encode("utf-8")
    return {
        "files": len(entries),
        "bytes": total,
        "elf_files_in_manifest": elf,
        "symlinks_under_package_dirs": symlinks,
        "manifest_sha256": hashlib.sha256(text).hexdigest(),
        "paths": set(entries),
    }


def pinned(audit_src: str) -> dict:
    src = open(audit_src, encoding="utf-8").read()
    m = re.search(
        r"LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256: &str =\s*\"([0-9a-f]{64})\"", src
    )
    arr = re.search(r"LOCKED_LEAN_SHA256: \[&str; \d+\] = \[(.*?)\];", src, flags=re.S)
    return {
        "audit_src_sha256": hashlib.sha256(src.encode("utf-8")).hexdigest(),
        "sysroot_manifest": m.group(1) if m else None,
        "launcher_digests": re.findall(r"\"([0-9a-f]{64})\"", arr.group(1)) if arr else [],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--prefix", required=True)
    ap.add_argument("--audit-src", required=True)
    args = ap.parse_args()
    prefix = os.path.realpath(args.prefix)
    lean = os.path.join(prefix, "bin", "lean")
    lib_dir = os.path.join(prefix, "lib", "lean")
    pins = pinned(args.audit_src)

    t0 = time.perf_counter()
    man = manifest(lib_dir)
    manifest_seconds = round(time.perf_counter() - t0, 2)
    manifest_paths = man.pop("paths")

    loaded = [("bin/lean", lean)]
    ldd = subprocess.run(["ldd", lean], capture_output=True, text=True).stdout
    for line in ldd.splitlines():
        parts = line.split()
        if len(parts) >= 3 and parts[1] == "=>":
            path = os.path.realpath(parts[2])
            if path.startswith(prefix + os.sep):
                loaded.append((os.path.relpath(path, prefix), path))

    elf = []
    for rel, path in sorted(loaded):
        digest = sha256(path)
        syms = subprocess.run(
            ["nm", "-D", "--defined-only", path], capture_output=True, text=True
        ).stdout
        names = [l.split()[-1] for l in syms.splitlines() if l.strip()]
        rel_in_lib = os.path.relpath(path, lib_dir).replace(os.sep, "/")
        elf.append(
            {
                "path": rel,
                "bytes": os.path.getsize(path),
                "sha256": digest,
                "covered_by_launcher_digest": digest in pins["launcher_digests"],
                "covered_by_sysroot_manifest": rel_in_lib in manifest_paths,
                "gmp_symbols_defined": sum(1 for n in names if n.startswith("__gmp")),
            }
        )

    uncovered = [
        e for e in elf
        if not (e["covered_by_launcher_digest"] or e["covered_by_sysroot_manifest"])
    ]
    out = {
        "lean_version": subprocess.run(
            [lean, "--version"], capture_output=True, text=True
        ).stdout.strip(),
        "host": " ".join(os.uname()[i] for i in (0, 4)),
        "pinned_in_audit_source": pins,
        "recomputed_sysroot_manifest": man,
        "recomputed_manifest_equals_pinned": man["manifest_sha256"] == pins["sysroot_manifest"],
        "manifest_seconds": manifest_seconds,
        "elf_files_loaded_by_lean_inside_prefix": elf,
        "elf_loaded_total_bytes": sum(e["bytes"] for e in elf),
        "elf_loaded_bytes_covered_by_a_pinned_digest": sum(
            e["bytes"] for e in elf if e not in uncovered
        ),
        "elf_loaded_not_covered": [e["path"] for e in uncovered],
    }
    json.dump(out, sys.stdout, indent=2, sort_keys=True)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
