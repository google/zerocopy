#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Static ELF, loader, RPATH/RUNPATH, symbol-version, and string-reference audit."""

import json
import os
import re
import struct
import subprocess
import sys
from pathlib import Path

SCRATCH = Path("<scratch>/mvp-investigations/task4")
UNPACKED = SCRATCH / "unpacked_omnibus"
CARGO_ANNEAL = SCRATCH / "cargo-anneal"


def parse_elf_sections(path: Path):
    """Return list of (name, sh_type, sh_flags, sh_offset, sh_size) for 64-bit LSB ELF."""
    with open(path, "rb") as f:
        data = f.read(64)
        if len(data) < 64 or data[:4] != b"\x7fELF":
            return [], b""
        f.seek(0)
        full = f.read()
    ei_class = full[4]
    ei_data = full[5]
    if ei_class != 2 or ei_data != 1:
        return [], full
    e_shoff = struct.unpack_from("<Q", full, 40)[0]
    e_shentsize = struct.unpack_from("<H", full, 58)[0]
    e_shnum = struct.unpack_from("<H", full, 60)[0]
    e_shstrndx = struct.unpack_from("<H", full, 62)[0]
    if e_shoff == 0 or e_shnum == 0:
        return [], full

    raw_sections = []
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size = struct.unpack_from(
            "<IIQQQQ", full, off
        )
        raw_sections.append((sh_name, sh_type, sh_flags, sh_offset, sh_size))

    shstr_off, shstr_size = raw_sections[e_shstrndx][3], raw_sections[e_shstrndx][4]
    shstrtab = full[shstr_off : shstr_off + shstr_size]

    sections = []
    for sh_name, sh_type, sh_flags, sh_offset, sh_size in raw_sections:
        end = shstrtab.find(b"\x00", sh_name)
        name = shstrtab[sh_name:end].decode("utf-8", errors="replace") if end != -1 else ""
        sections.append((name, sh_type, sh_flags, sh_offset, sh_size))
    return sections, full


def find_section_for_offset(sections, offset):
    for name, sh_type, sh_flags, sh_offset, sh_size in sections:
        # SHT_NOBITS == 8
        if sh_type != 8 and sh_offset <= offset < sh_offset + sh_size:
            alloc = bool(sh_flags & 0x2)  # SHF_ALLOC
            return name, alloc
    return "<unmapped>", False


def parse_version_tuple(ver_str: str):
    parts = ver_str.split("_", 1)
    if len(parts) < 2:
        return (0,)
    nums = []
    for p in parts[1].split("."):
        try:
            nums.append(int(p))
        except ValueError:
            nums.append(0)
    return tuple(nums)


def audit_elf(path: Path, rel_name: str):
    sections, full = parse_elf_sections(path)
    # 1. readelf -lW (PT_INTERP)
    interp = None
    out_l = subprocess.run(
        ["readelf", "-lW", str(path)], capture_output=True, text=True, check=False
    ).stdout
    for line in out_l.splitlines():
        m = re.search(r"\[Requesting program interpreter:\s*(.+?)\]", line)
        if m:
            interp = m.group(1).strip()

    # 2. readelf -dW (DT_NEEDED, DT_RPATH, DT_RUNPATH, DT_SONAME)
    out_d = subprocess.run(
        ["readelf", "-dW", str(path)], capture_output=True, text=True, check=False
    ).stdout
    needed = []
    rpath = []
    runpath = []
    soname = None
    for line in out_d.splitlines():
        if "(NEEDED)" in line:
            m = re.search(r"Shared library:\s*\[(.+?)\]", line)
            if m:
                needed.append(m.group(1))
        elif "(RPATH)" in line:
            m = re.search(r"Library rpath:\s*\[(.+?)\]", line)
            if m:
                rpath.append(m.group(1))
        elif "(RUNPATH)" in line:
            m = re.search(r"Library runpath:\s*\[(.+?)\]", line)
            if m:
                runpath.append(m.group(1))
        elif "(SONAME)" in line:
            m = re.search(r"Library soname:\s*\[(.+?)\]", line)
            if m:
                soname = m.group(1)

    # 3. readelf -V (Version needs)
    out_v = subprocess.run(
        ["readelf", "-V", str(path)], capture_output=True, text=True, check=False
    ).stdout
    verneed = {}
    current_file = None
    for line in out_v.splitlines():
        m_file = re.search(r"File:\s*(\S+)", line)
        if m_file:
            current_file = m_file.group(1)
            verneed.setdefault(current_file, set())
        m_name = re.search(r"Name:\s*(\S+)", line)
        if m_name and current_file:
            verneed[current_file].add(m_name.group(1))

    verneed_sorted = {
        k: sorted(v, key=parse_version_tuple) for k, v in sorted(verneed.items())
    }

    # 4. Scan printable ASCII strings >= 4 bytes for sensitive path patterns
    patterns = {
        "nix_store": re.compile(rb"[^\x00-\x1f\x7f-\xff]*?/nix/store/[^\x00-\x1f\x7f-\xff]*"),
        "google_home": re.compile(rb"[^\x00-\x1f\x7f-\xff]*?/usr/local/google[^\x00-\x1f\x7f-\xff]*"),
        "rustup": re.compile(rb"[^\x00-\x1f\x7f-\xff]*?\.rustup[^\x00-\x1f\x7f-\xff]*"),
        "elan": re.compile(rb"[^\x00-\x1f\x7f-\xff]*?\.elan[^\x00-\x1f\x7f-\xff]*"),
    }
    string_hits = {}
    for pat_name, regex in patterns.items():
        hits_by_sec = {}
        for m in regex.finditer(full):
            sec_name, alloc = find_section_for_offset(sections, m.start())
            s = m.group(0).decode("utf-8", errors="replace")
            key = f"{sec_name} ({'ALLOC' if alloc else 'NON-ALLOC'})"
            hits_by_sec.setdefault(key, {"count": 0, "samples": []})
            hits_by_sec[key]["count"] += 1
            if len(hits_by_sec[key]["samples"]) < 5 and s not in hits_by_sec[key]["samples"]:
                hits_by_sec[key]["samples"].append(s[:200])
        if hits_by_sec:
            string_hits[pat_name] = hits_by_sec

    return {
        "path": rel_name,
        "size_bytes": path.stat().st_size,
        "interpreter": interp,
        "soname": soname,
        "dt_needed": needed,
        "dt_rpath": rpath,
        "dt_runpath": runpath,
        "version_needs": verneed_sorted,
        "string_hits": string_hits,
    }


def main():
    results = {
        "cargo_anneal": audit_elf(CARGO_ANNEAL, "cargo-anneal"),
        "omnibus_elfs": [],
        "omnibus_shebangs": [],
    }

    for root, dirs, files in os.walk(UNPACKED):
        dirs.sort()
        for fname in sorted(files):
            fpath = Path(root) / fname
            if fpath.is_symlink() or not fpath.is_file():
                continue
            rel = str(fpath.relative_to(UNPACKED))
            try:
                with open(fpath, "rb") as f:
                    head = f.read(128)
            except OSError:
                continue
            if head.startswith(b"\x7fELF"):
                e_type = struct.unpack_from("<H", head, 16)[0] if len(head) >= 18 else 0
                if e_type in (2, 3):  # ET_EXEC=2, ET_DYN=3
                    results["omnibus_elfs"].append(audit_elf(fpath, rel))
            elif head.startswith(b"#!"):
                first_line = head.splitlines()[0].decode("utf-8", errors="replace")
                results["omnibus_shebangs"].append({"path": rel, "shebang": first_line})

    out_path = SCRATCH / "elf_audit.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"Wrote {out_path} with {len(results['omnibus_elfs'])} omnibus ELF binaries/shared libs and {len(results['omnibus_shebangs'])} shebang scripts.")


if __name__ == "__main__":
    main()
