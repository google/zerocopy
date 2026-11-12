#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Track D probe for Q-D3: GLIBC symbol version floor and weak DT_VERNEED semantics in ld.so."""

import json
import shutil
import struct
import subprocess
from pathlib import Path

TRACK_D = Path(__file__).resolve().parent
TASK4_DIR = TRACK_D.parent.parent / "mvp-investigations" / "task4"
TC_HASH = "e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a"
TC_DIR = TRACK_D / "home_baseline" / ".cache" / "anneal" / "toolchain" / TC_HASH

STB_LOCAL = 0
STB_GLOBAL = 1
STB_WEAK = 2
VER_FLG_WEAK = 0x2

BIND_NAMES = {0: "LOCAL", 1: "GLOBAL", 2: "WEAK"}


def dl_elf_hash(name: bytes) -> int:
    """Standard SysV ELF hash used by .gnu.version_r (vna_hash) and .gnu.version_d (vd_hash)."""
    h = 0
    for b in name:
        h = ((h << 4) + b) & 0xFFFFFFFF
        g = h & 0xF0000000
        if g:
            h ^= g >> 24
        h &= ~g & 0xFFFFFFFF
    return h


def parse_version_tuple(ver_str: str):
    parts = ver_str.split("_", 1)
    if len(parts) < 2:
        return (0,)
    out = []
    for p in parts[1].split("."):
        try:
            out.append(int(p))
        except ValueError:
            out.append(0)
    return tuple(out)


def read_cstr(buf: bytes, offset: int) -> str:
    end = buf.find(b"\x00", offset)
    if end == -1:
        return ""
    return buf[offset:end].decode("utf-8", errors="replace")


def inspect_elf_versioning(path: Path, label: str):
    """Parse .dynsym, .dynstr, .gnu.version, .gnu.version_r, and .comment from an ELF64 LSB binary."""
    data = path.read_bytes()
    assert data[:4] == b"\x7fELF" and data[4] == 2 and data[5] == 1
    e_shoff = struct.unpack_from("<Q", data, 40)[0]
    e_shentsize = struct.unpack_from("<H", data, 58)[0]
    e_shnum = struct.unpack_from("<H", data, 60)[0]
    e_shstrndx = struct.unpack_from("<H", data, 62)[0]

    raw_secs = []
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size, sh_link, sh_info, sh_addralign, sh_entsize = (
            struct.unpack_from("<IIQQQQIIQQ", data, off)
        )
        raw_secs.append((sh_name, sh_type, sh_offset, sh_size, sh_entsize))

    shstr_off, shstr_size = raw_secs[e_shstrndx][2], raw_secs[e_shstrndx][3]
    shstr = data[shstr_off : shstr_off + shstr_size]

    sec_by_name = {}
    for sh_name, sh_type, sh_offset, sh_size, sh_entsize in raw_secs:
        name = read_cstr(shstr, sh_name)
        sec_by_name[name] = (sh_type, sh_offset, sh_size, sh_entsize)

    dynstr = b""
    if ".dynstr" in sec_by_name:
        _, off, sz, _ = sec_by_name[".dynstr"]
        dynstr = data[off : off + sz]

    # Parse .gnu.version (uint16 per dynsym)
    versym = []
    if ".gnu.version" in sec_by_name:
        _, off, sz, _ = sec_by_name[".gnu.version"]
        count = sz // 2
        versym = list(struct.unpack_from(f"<{count}H", data, off))

    # Parse .dynsym (Elf64_Sym = 24 bytes: st_name:I, st_info:B, st_other:B, st_shndx:H, st_value:Q, st_size:Q)
    dynsyms = []
    if ".dynsym" in sec_by_name:
        _, off, sz, _ = sec_by_name[".dynsym"]
        count = sz // 24
        for idx in range(count):
            st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from(
                "<IBBHQQ", data, off + idx * 24
            )
            sym_name = read_cstr(dynstr, st_name)
            st_bind = st_info >> 4
            ver_idx = versym[idx] & 0x7FFF if idx < len(versym) else 0
            dynsyms.append(
                {
                    "index": idx,
                    "name": sym_name,
                    "bind": BIND_NAMES.get(st_bind, str(st_bind)),
                    "shndx": st_shndx,
                    "ver_index": ver_idx,
                }
            )

    # Parse .gnu.version_r (Elf64_Verneed + Elf64_Vernaux)
    verneeds = []
    ver_index_to_info = {}
    if ".gnu.version_r" in sec_by_name:
        _, sec_off, sec_sz, _ = sec_by_name[".gnu.version_r"]
        vn_off = 0
        while vn_off < sec_sz:
            vn_version, vn_cnt, vn_file, vn_aux, vn_next = struct.unpack_from(
                "<HHIII", data, sec_off + vn_off
            )
            file_name = read_cstr(dynstr, vn_file)
            aux_list = []
            aux_off = vn_off + vn_aux
            for _ in range(vn_cnt):
                vna_hash, vna_flags, vna_other, vna_name, vna_next = struct.unpack_from(
                    "<IHHII", data, sec_off + aux_off
                )
                ver_name = read_cstr(dynstr, vna_name)
                ver_idx = vna_other & 0x7FFF
                syms_for_ver = [
                    s for s in dynsyms if s["ver_index"] == ver_idx and s["shndx"] == 0
                ]
                all_weak_syms = bool(syms_for_ver) and all(
                    s["bind"] == "WEAK" for s in syms_for_ver
                )
                entry = {
                    "version": ver_name,
                    "vna_hash": f"0x{vna_hash:08x}",
                    "vna_flags": vna_flags,
                    "vna_flags_str": "WEAK" if (vna_flags & VER_FLG_WEAK) else "none",
                    "vna_other": ver_idx,
                    "all_referencing_syms_weak": all_weak_syms,
                    "symbols": [
                        {"name": s["name"], "bind": s["bind"]} for s in syms_for_ver
                    ],
                }
                aux_list.append(entry)
                ver_index_to_info[ver_idx] = (file_name, ver_name)
                if vna_next == 0:
                    break
                aux_off += vna_next
            aux_list.sort(key=lambda x: parse_version_tuple(x["version"]))
            verneeds.append({"file": file_name, "versions": aux_list})
            if vn_next == 0:
                break
            vn_off += vn_next

    # Also collect unversioned weak undefined symbols (ver_index in (0, 1))
    unversioned_weak_und = [
        s["name"]
        for s in dynsyms
        if s["shndx"] == 0
        and s["bind"] == "WEAK"
        and s["ver_index"] in (0, 1)
        and s["name"]
    ]

    # Compute libc.so.6 floors
    libc_versions = []
    for vn in verneeds:
        if vn["file"] == "libc.so.6":
            libc_versions = vn["versions"]

    max_nonweak_verneed = None
    max_strong_sym_ver = None
    max_any_verneed = None
    if libc_versions:
        max_any_verneed = max(libc_versions, key=lambda x: parse_version_tuple(x["version"]))["version"]
        nonweak = [v for v in libc_versions if not (v["vna_flags"] & VER_FLG_WEAK)]
        if nonweak:
            max_nonweak_verneed = max(nonweak, key=lambda x: parse_version_tuple(x["version"]))["version"]
        strong_sym_vers = [v for v in libc_versions if not v["all_referencing_syms_weak"]]
        if strong_sym_vers:
            max_strong_sym_ver = max(
                strong_sym_vers, key=lambda x: parse_version_tuple(x["version"])
            )["version"]

    # Extract .comment strings
    comments = []
    if ".comment" in sec_by_name:
        _, off, sz, _ = sec_by_name[".comment"]
        for part in data[off : off + sz].split(b"\x00"):
            s = part.decode("utf-8", errors="replace").strip()
            if s and s not in comments:
                comments.append(s)

    return {
        "label": label,
        "comments": comments,
        "libc_max_verneed_any": max_any_verneed,
        "libc_effective_ld_so_floor_nonweak_verneed": max_nonweak_verneed,
        "libc_strong_symbol_floor": max_strong_sym_ver,
        "unversioned_weak_undefined_symbols": unversioned_weak_und,
        "verneeds": verneeds,
    }


def patch_vernaux_and_sym(
    elf_path: Path,
    target_ver_name: str,
    new_ver_name: str | None = None,
    new_vna_flags: int | None = None,
    sym_name_for_bind: str | None = None,
    new_sym_bind: int | None = None,
):
    """Patch Elf64_Vernaux (vna_flags and/or version name + hash) and optionally Elf64_Sym binding."""
    data = bytearray(elf_path.read_bytes())
    e_shoff = struct.unpack_from("<Q", data, 40)[0]
    e_shentsize = struct.unpack_from("<H", data, 58)[0]
    e_shnum = struct.unpack_from("<H", data, 60)[0]
    e_shstrndx = struct.unpack_from("<H", data, 62)[0]

    raw_secs = []
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size = struct.unpack_from(
            "<IIQQQQ", data, off
        )
        raw_secs.append((sh_name, sh_offset, sh_size))

    shstr_off, shstr_size = raw_secs[e_shstrndx][1], raw_secs[e_shstrndx][2]
    shstr = bytes(data[shstr_off : shstr_off + shstr_size])
    sec_by_name = {read_cstr(shstr, n): (o, s) for n, o, s in raw_secs}

    dynstr_off, dynstr_sz = sec_by_name[".dynstr"]
    dynstr = bytes(data[dynstr_off : dynstr_off + dynstr_sz])

    # Patch .gnu.version_r
    vr_off, vr_sz = sec_by_name[".gnu.version_r"]
    vn_off = 0
    while vn_off < vr_sz:
        vn_version, vn_cnt, vn_file, vn_aux, vn_next = struct.unpack_from(
            "<HHIII", data, vr_off + vn_off
        )
        aux_off = vn_off + vn_aux
        for _ in range(vn_cnt):
            vna_hash, vna_flags, vna_other, vna_name, vna_next = struct.unpack_from(
                "<IHHII", data, vr_off + aux_off
            )
            ver_str = read_cstr(dynstr, vna_name)
            if ver_str == target_ver_name:
                if new_ver_name is not None:
                    assert len(new_ver_name) == len(target_ver_name)
                    new_bytes = new_ver_name.encode("ascii")
                    data[dynstr_off + vna_name : dynstr_off + vna_name + len(new_bytes)] = new_bytes
                    vna_hash = dl_elf_hash(new_bytes)
                if new_vna_flags is not None:
                    vna_flags = new_vna_flags
                struct.pack_into(
                    "<IHHII",
                    data,
                    vr_off + aux_off,
                    vna_hash,
                    vna_flags,
                    vna_other,
                    vna_name,
                    vna_next,
                )
            if vna_next == 0:
                break
            aux_off += vna_next
        if vn_next == 0:
            break
        vn_off += vn_next

    # Optionally patch symbol binding in .dynsym
    if sym_name_for_bind is not None and new_sym_bind is not None:
        ds_off, ds_sz = sec_by_name[".dynsym"]
        for idx in range(ds_sz // 24):
            st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from(
                "<IBBHQQ", data, ds_off + idx * 24
            )
            if read_cstr(dynstr, st_name) == sym_name_for_bind:
                st_type = st_info & 0xF
                new_st_info = (new_sym_bind << 4) | st_type
                struct.pack_into("<B", data, ds_off + idx * 24 + 4, new_st_info)

    elf_path.write_bytes(data)


def run_reproducer_experiments():
    repro_dir = TRACK_D / "verneed_repro"
    if repro_dir.exists():
        shutil.rmtree(repro_dir)
    repro_dir.mkdir(parents=True)

    # --- Experiment 1: Custom shared library v2.0 (at link time) swapped with v1.0 (at runtime) ---
    # Build libprovider.so.1 v2.0 (exports base_fn@@PROV_1.0 and optional_fn@@PROV_2.0)
    (repro_dir / "provider_v2.c").write_text(
        "int base_fn(void) { return 10; }\n"
        "int optional_fn(void) { return 42; }\n"
    )
    (repro_dir / "provider_v2.map").write_text(
        "PROV_1.0 {\n  global: base_fn;\n  local: *;\n};\n"
        "PROV_2.0 {\n  global: optional_fn;\n} PROV_1.0;\n"
    )
    # Build libprovider.so.1 v1.0 (exports ONLY base_fn@@PROV_1.0; PROV_2.0 and optional_fn do not exist!)
    (repro_dir / "provider_v1.c").write_text(
        "int base_fn(void) { return 10; }\n"
    )
    (repro_dir / "provider_v1.map").write_text(
        "PROV_1.0 {\n  global: base_fn;\n  local: *;\n};\n"
    )
    # Client program: calls base_fn() and checks weak optional_fn()
    (repro_dir / "client.c").write_text(
        "#include <stdio.h>\n"
        "extern int base_fn(void);\n"
        "extern int optional_fn(void) __attribute__((weak));\n"
        "int main(void) {\n"
        "    int b = base_fn();\n"
        "    if (optional_fn) {\n"
        "        printf(\"base=%d optional=%d (present)\\n\", b, optional_fn());\n"
        "    } else {\n"
        "        printf(\"base=%d optional=NULL (graceful_fallback)\\n\", b);\n"
        "    }\n"
        "    return 0;\n"
        "}\n"
    )

    v2_dir = repro_dir / "lib_v2"
    v1_dir = repro_dir / "lib_v1"
    v2_dir.mkdir()
    v1_dir.mkdir()

    subprocess.run(
        [
            "gcc", "-shared", "-fPIC",
            "-Wl,-soname,libprovider.so.1",
            f"-Wl,--version-script={repro_dir / 'provider_v2.map'}",
            str(repro_dir / "provider_v2.c"),
            "-o", str(v2_dir / "libprovider.so.1"),
        ],
        check=True,
    )
    (v2_dir / "libprovider.so").symlink_to("libprovider.so.1")

    subprocess.run(
        [
            "gcc", "-shared", "-fPIC",
            "-Wl,-soname,libprovider.so.1",
            f"-Wl,--version-script={repro_dir / 'provider_v1.map'}",
            str(repro_dir / "provider_v1.c"),
            "-o", str(v1_dir / "libprovider.so.1"),
        ],
        check=True,
    )
    (v1_dir / "libprovider.so").symlink_to("libprovider.so.1")

    # Link client against v2.0 (using standard GNU ld.bfd, which sets vna_flags=0 on PROV_2.0!)
    bin_1a = repro_dir / "repro_1a_weak_sym_nonweak_verneed"
    subprocess.run(
        [
            "gcc", "-O2",
            str(repro_dir / "client.c"),
            f"-L{v2_dir}", "-lprovider",
            "-o", str(bin_1a),
        ],
        check=True,
    )

    # Variant 1B: same binary, but patch PROV_2.0's Elf64_Vernaux.vna_flags from 0x0 to VER_FLG_WEAK (0x2)
    bin_1b = repro_dir / "repro_1b_weak_sym_weak_verneed"
    shutil.copy2(bin_1a, bin_1b)
    patch_vernaux_and_sym(bin_1b, "PROV_2.0", new_vna_flags=VER_FLG_WEAK)

    # Variant 1C: vna_flags = VER_FLG_WEAK (0x2), but optional_fn is STB_GLOBAL (1) in .dynsym
    bin_1c = repro_dir / "repro_1c_strong_sym_weak_verneed"
    shutil.copy2(bin_1a, bin_1c)
    patch_vernaux_and_sym(
        bin_1c,
        "PROV_2.0",
        new_vna_flags=VER_FLG_WEAK,
        sym_name_for_bind="optional_fn",
        new_sym_bind=STB_GLOBAL,
    )

    # Variant 1D: Unversioned STB_WEAK symbol (linked against v1.0 sysroot where optional_fn is absent, matching rust/bin/cargo linked against glibc 2.17)
    bin_1d = repro_dir / "repro_1d_unversioned_weak_sym"
    subprocess.run(
        [
            "gcc", "-O2", "-Wl,--export-dynamic",
            str(repro_dir / "client.c"),
            f"-L{v1_dir}", "-lprovider",
            "-o", str(bin_1d),
        ],
        check=True,
    )

    def run_with_lib(bin_path: Path, lib_dir: Path, label: str):
        proc = subprocess.run(
            [str(bin_path)],
            env={"LD_LIBRARY_PATH": str(lib_dir), "PATH": "/usr/bin:/bin"},
            capture_output=True,
            text=True,
            check=False,
        )
        stderr_clean = proc.stderr.replace(str(repro_dir), "<repro_dir>")
        return {
            "label": label,
            "exit_code": proc.returncode,
            "stdout": proc.stdout.strip(),
            "stderr": stderr_clean.strip(),
        }

    # --- Experiment 2: Live host libc.so.6 with weak pidfd_spawnp bound to missing GLIBC_2.99 ---
    (repro_dir / "pidfd_repro.c").write_text(
        "#include <stdio.h>\n"
        "extern int pidfd_spawnp(int *pidfd, const char *file, const void *fa,\n"
        "                        const void *attr, char *const argv[], char *const envp[])\n"
        "    __attribute__((weak));\n"
        "int main(void) {\n"
        "    printf(\"pidfd_spawnp=%s\\n\", pidfd_spawnp ? \"resolved\" : \"NULL_fallback\");\n"
        "    return 0;\n"
        "}\n"
    )
    bin_2a = repro_dir / "repro_2a_libc_glibc299_nonweak"
    subprocess.run(
        ["gcc", "-O2", str(repro_dir / "pidfd_repro.c"), "-o", str(bin_2a)],
        check=True,
    )
    # Rewrite GLIBC_2.39 -> GLIBC_2.99 with vna_flags=0x0 (Flags: none)
    patch_vernaux_and_sym(bin_2a, "GLIBC_2.39", new_ver_name="GLIBC_2.99", new_vna_flags=0)

    # Variant 2B: Rewrite GLIBC_2.39 -> GLIBC_2.99 with vna_flags=VER_FLG_WEAK (0x2)
    bin_2b = repro_dir / "repro_2b_libc_glibc299_weak"
    shutil.copy2(bin_2a, bin_2b)
    patch_vernaux_and_sym(bin_2b, "GLIBC_2.99", new_vna_flags=VER_FLG_WEAK)

    return {
        "experiment_1_provider_v2_to_v1_downgrade": {
            "against_v2_baseline": run_with_lib(bin_1a, v2_dir, "1A against libprovider v2.0 (PROV_2.0 present)"),
            "case_1a_stb_weak_vna_flags_0": run_with_lib(
                bin_1a,
                v1_dir,
                "1A against libprovider v1.0: STB_WEAK in .dynsym, vna_flags=0 (none) in .gnu.version_r -> fails in _dl_check_map_versions",
            ),
            "case_1b_stb_weak_vna_flags_weak": run_with_lib(
                bin_1b,
                v1_dir,
                "1B against libprovider v1.0: STB_WEAK in .dynsym, vna_flags=VER_FLG_WEAK (0x2) in .gnu.version_r -> passes _dl_check_map_versions and resolves optional_fn to NULL",
            ),
            "case_1c_stb_global_vna_flags_weak": run_with_lib(
                bin_1c,
                v1_dir,
                "1C against libprovider v1.0: STB_GLOBAL in .dynsym, vna_flags=VER_FLG_WEAK (0x2) in .gnu.version_r -> passes _dl_check_map_versions, then fails in _dl_lookup_symbol_x",
            ),
            "case_1d_unversioned_stb_weak": run_with_lib(
                bin_1d,
                v1_dir,
                "1D against libprovider v1.0: unversioned STB_WEAK in .dynsym (no PROV_2.0 entry in .gnu.version_r, matching rust/bin/cargo) -> runs silently with stderr='' and resolves optional_fn to NULL",
            ),
        },
        "experiment_2_libc_missing_glibc_2_99": {
            "case_2a_pidfd_spawnp_vna_flags_0": run_with_lib(
                bin_2a,
                v1_dir,
                "2A: pidfd_spawnp@GLIBC_2.99 (STB_WEAK, vna_flags=0) -> ld.so rejects before main()",
            ),
            "case_2b_pidfd_spawnp_vna_flags_weak": run_with_lib(
                bin_2b,
                v1_dir,
                "2B: pidfd_spawnp@GLIBC_2.99 (STB_WEAK, vna_flags=VER_FLG_WEAK) -> ld.so succeeds and pidfd_spawnp resolves to NULL",
            ),
        },
    }


def main():
    binaries = [
        (TASK4_DIR / "cargo-anneal", "cargo-anneal (rustc 1.98.0-nightly + LLD 22.1.6)"),
        (
            TRACK_D / "mvp-patched" / "target-bfd" / "debug" / "cargo-anneal",
            "cargo-anneal (rustc 1.98.0-nightly + GNU ld.bfd 2.45)",
        ),
        (
            TRACK_D / "mvp-patched" / "target-101-bfd" / "debug" / "cargo-anneal",
            "cargo-anneal (rustc 1.101.0-nightly + GNU ld.bfd 2.45)",
        ),
        (TC_DIR / "bin" / "anneal-rustc-capture", "bin/anneal-rustc-capture (Nix build, dynamic librustc_driver)"),
        (TC_DIR / "rust" / "bin" / "rustc", "rust/bin/rustc (upstream Rust CI, glibc 2.17 sysroot)"),
        (TC_DIR / "rust" / "bin" / "cargo", "rust/bin/cargo (upstream Rust CI, glibc 2.17 sysroot)"),
        (
            TC_DIR / "rust" / "lib" / "librustc_driver-5d5a3c5207375ffc.so",
            "rust/lib/librustc_driver-5d5a3c5207375ffc.so (upstream Rust CI, glibc 2.17 sysroot)",
        ),
        (
            TC_DIR / "rust" / "lib" / "libLLVM.so.22.1-rust-1.98.0-nightly",
            "rust/lib/libLLVM.so.22.1-rust-1.98.0-nightly (upstream Rust CI, glibc 2.17 sysroot)",
        ),
        (TC_DIR / "lean" / "bin" / "lean", "lean/bin/lean (upstream Lean 4.34.1)"),
        (TC_DIR / "lean" / "lib" / "lean" / "libleanshared.so", "lean/lib/lean/libleanshared.so (upstream Lean 4.34.1)"),
        (TC_DIR / "lean" / "lib" / "libz.so.1.2.11", "lean/lib/libz.so.1.2.11 (bundled zlib)"),
        (TC_DIR / "lean" / "lib" / "libgcc_s.so.1", "lean/lib/libgcc_s.so.1 (bundled libgcc_s)"),
    ]

    # Also build one with rustc 1.101.0-nightly + LLD 23.1.4 so we have all 4 linker/compiler combinations
    target_101_lld = TRACK_D / "mvp-patched" / "target-101-lld" / "debug" / "cargo-anneal"
    if not target_101_lld.exists():
        subprocess.run(
            [
                "env", "-u", "RUSTFLAGS",
                "cargo", "build", "--locked", "--offline", "-p", "cargo-anneal",
                "--target-dir", str(TRACK_D / "mvp-patched" / "target-101-lld"),
            ],
            cwd=str(TRACK_D / "mvp-patched"),
            check=True,
        )
    binaries.insert(2, (target_101_lld, "cargo-anneal (rustc 1.101.0-nightly + LLD 23.1.4)"))

    inspected = [inspect_elf_versioning(p, label) for p, label in binaries]
    repro_results = run_reproducer_experiments()

    out = {
        "binary_version_audit": inspected,
        "ld_so_verneed_reproducer": repro_results,
    }
    out_path = TRACK_D / "track_d_q3_verneed_results.json"
    out_path.write_text(json.dumps(out, indent=2) + "\n")
    print(f"Q-D3 VERNEED AUDIT AND REPRODUCER SUCCEEDED. Wrote {out_path}")


if __name__ == "__main__":
    main()
