#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Standalone probe for in-process `rustc_driver` `override_queries` inline-asm injection,
`codegen-units = 16` multi-CGU / cross-crate `.rmeta` containment, `${:uid}` per-CGU reset,
and `.text` SHA-256 codegen-invariance across `x86_64`, `aarch64`, and `riscv64gc`."""

from __future__ import annotations

import argparse
import glob
import hashlib
import json
import os
import struct
import subprocess
import tempfile
from pathlib import Path
from typing import Any

SHF_ALLOC = 0x2
SHF_EXECINSTR = 0x4
SHF_EXCLUDE = 0x80000000


def parse_elf64_reloc(path: str | Path) -> dict[str, Any]:
    data = Path(path).read_bytes()
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise ValueError(f"Expected little-endian ELF64 object: {path}")
    e_shoff = struct.unpack_from("<Q", data, 40)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 58)

    shdrs: list[dict[str, Any]] = []
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        (
            sh_name,
            sh_type,
            sh_flags,
            sh_addr,
            sh_offset,
            sh_size,
            sh_link,
            sh_info,
            _sh_addralign,
            sh_entsize,
        ) = struct.unpack_from("<IIQQQQIIQQ", data, off)
        shdrs.append(
            {
                "idx": i,
                "sh_name": sh_name,
                "type": sh_type,
                "flags": sh_flags,
                "addr": sh_addr,
                "offset": sh_offset,
                "size": sh_size,
                "link": sh_link,
                "info": sh_info,
                "entsize": sh_entsize,
            }
        )
    shstr = data[shdrs[e_shstrndx]["offset"] : shdrs[e_shstrndx]["offset"] + shdrs[e_shstrndx]["size"]]
    for s in shdrs:
        end = shstr.find(b"\x00", s["sh_name"])
        s["name"] = shstr[s["sh_name"] : end].decode("utf-8", errors="replace")
        s["data"] = data[s["offset"] : s["offset"] + s["size"]] if s["type"] != 8 else b""

    syms: list[dict[str, Any]] = []
    for s in shdrs:
        if s["type"] == 2 and s["entsize"] > 0:
            strtab = shdrs[s["link"]]["data"]
            for off in range(0, s["size"], s["entsize"]):
                st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from(
                    "<IBBHQQ", s["data"], off
                )
                end = strtab.find(b"\x00", st_name)
                syms.append(
                    {
                        "name": strtab[st_name:end].decode("utf-8", errors="replace"),
                        "bind": st_info >> 4,
                        "type": st_info & 0xF,
                        "vis": st_other & 0x3,
                        "shndx": st_shndx,
                        "value": st_value,
                        "size": st_size,
                    }
                )
            break

    relas: dict[int, list[dict[str, Any]]] = {}
    for s in shdrs:
        if s["type"] == 4 and s["entsize"] > 0:
            entries: list[dict[str, Any]] = []
            for off in range(0, s["size"], s["entsize"]):
                r_offset, r_info, r_addend = struct.unpack_from("<QQq", s["data"], off)
                r_sym = r_info >> 32
                r_type = r_info & 0xFFFFFFFF
                sym = syms[r_sym]
                sec_name = shdrs[sym["shndx"]]["name"] if 0 < sym["shndx"] < len(shdrs) else None
                entries.append(
                    {
                        "r_offset": r_offset,
                        "r_sym": r_sym,
                        "r_type": r_type,
                        "r_addend": r_addend,
                        "sym_name": sym["name"],
                        "sym_shndx": sym["shndx"],
                        "sym_sec": sec_name,
                        "sym_value": sym["value"],
                    }
                )
            relas[s["info"]] = entries
    return {"shdrs": shdrs, "syms": syms, "relas": relas}


def extract_attested_sites(elf_path: str | Path) -> list[dict[str, Any]]:
    elf = parse_elf64_reloc(elf_path)
    sec_by_name = {s["name"]: s for s in elf["shdrs"]}
    if ".anneal.asm_sites" not in sec_by_name or ".anneal.asm_descs" not in sec_by_name:
        return []
    sites_sec = sec_by_name[".anneal.asm_sites"]
    descs_sec = sec_by_name[".anneal.asm_descs"]
    rela_by_off = {r["r_offset"]: r for r in elf["relas"].get(sites_sec["idx"], [])}

    data = sites_sec["data"]
    pos = 0
    out: list[dict[str, Any]] = []
    while pos + 48 <= len(data):
        _s_raw, _e_raw, site_id, _d_raw, desc_len, n_rel = struct.unpack_from("<6Q", data, pos)
        r_start = rela_by_off[pos]
        r_end = rela_by_off[pos + 8]
        r_desc = rela_by_off[pos + 24]

        start_off = r_start["sym_value"] + r_start["r_addend"]
        end_off = r_end["sym_value"] + r_end["r_addend"]
        desc_off = r_desc["sym_value"] + r_desc["r_addend"]
        text_sec = elf["shdrs"][r_start["sym_shndx"]]
        slice_bytes = text_sec["data"][start_off:end_off]
        # Strip trailing NUL from `.asciz`.
        raw_desc = descs_sec["data"][desc_off : desc_off + desc_len]
        desc_text = raw_desc.rstrip(b"\x00").decode("utf-8", errors="replace")

        extra_relocs = []
        for k in range(n_rel):
            rk = rela_by_off[pos + 48 + 8 * k]
            extra_relocs.append(
                {
                    "sym_name": rk["sym_name"],
                    "sym_sec": rk["sym_sec"],
                    "target_off": rk["sym_value"] + rk["r_addend"],
                }
            )
        out.append(
            {
                "site_id": site_id,
                "section": text_sec["name"],
                "same_section": r_start["sym_shndx"] == r_end["sym_shndx"],
                "start_off": start_off,
                "end_off": end_off,
                "slice_hex": slice_bytes.hex(),
                "desc": desc_text,
                "sites_shf_exclude": bool(sites_sec["flags"] & SHF_EXCLUDE),
                "descs_shf_exclude": bool(descs_sec["flags"] & SHF_EXCLUDE),
                "relocs": extra_relocs,
            }
        )
        pos += 48 + 8 * n_rel
    return out


def text_sections_digest(elf_path: str | Path) -> dict[str, Any]:
    elf = parse_elf64_reloc(elf_path)
    h = hashlib.sha256()
    total_bytes = 0
    sec_Count = 0
    for s in sorted(elf["shdrs"], key=lambda x: x["name"]):
        if (s["flags"] & SHF_EXECINSTR) and s["name"].startswith(".text"):
            h.update(s["name"].encode("utf-8") + b"\x00")
            h.update(s["data"])
            total_bytes += len(s["data"])
            sec_Count += 1
    return {
        "text_bytes": total_bytes,
        "text_sections": sec_Count,
        "sha256_16": h.hexdigest()[:16],
        "sha256": h.hexdigest(),
    }


def build_driver(tc: str, driver_src: Path, out_dir: Path) -> tuple[Path, str]:
    sysroot = subprocess.check_output(
        ["rustup", "run", tc, "rustc", "--print", "sysroot"], text=True
    ).strip()
    version_line = (
        subprocess.check_output(["rustup", "run", tc, "rustc", "-vV"], text=True)
        .strip()
        .splitlines()[0]
    )
    extra_cfgs: list[str] = []
    if "1.98." in version_line:
        extra_cfgs = ["--cfg", "anneal_rustc_1_98"]
    elif "1.102." in version_line:
        extra_cfgs = ["--cfg", "anneal_rustc_1_102"]

    drv_bin = out_dir / f"anneal_driver_{tc.replace('/', '_')}"
    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"
    subprocess.run(
        [
            "rustup",
            "run",
            tc,
            "rustc",
            "--edition=2021",
            "-O",
            f"-Clink-arg=-Wl,-rpath,{sysroot}/lib",
            *extra_cfgs,
            str(driver_src),
            "-o",
            str(drv_bin),
        ],
        env=env,
        check=True,
        capture_output=True,
        text=True,
    )
    return drv_bin, sysroot


def test_global_asm_cgu16_failure_and_uid_reset(tc: str, work: Path) -> dict[str, Any]:
    # 1. `global_asm!(".macro __aw ...")` under `-C codegen-units=16 -C lto=off`:
    cgu_src = work / "cgu16_crash.rs"
    mods = []
    for i in range(16):
        mods.append(
            f"""pub mod m{i} {{
    #[inline(never)]
    pub unsafe fn f{i}(mut x: u64, y: u64) -> u64 {{
        core::arch::asm!("__aw {{0:r}}, {{1:r}}", inout(reg) x, in(reg) y, options(nomem, nostack));
        x
    }}
}}"""
        )
    cgu_src.write_text(
        'core::arch::global_asm!(".macro __aw a, b\\nsub \\\\a, \\\\b\\n.endm");\n'
        + "\n".join(mods)
        + "\n"
    )
    out_dir = work / "cgu16_out"
    out_dir.mkdir(exist_ok=True)
    proc = subprocess.run(
        [
            "rustup",
            "run",
            tc,
            "rustc",
            "--crate-type=rlib",
            "-C",
            "opt-level=3",
            "-C",
            "codegen-units=16",
            "-C",
            "lto=off",
            "--emit=obj",
            str(cgu_src),
            "--out-dir",
            str(out_dir),
        ],
        capture_output=True,
        text=True,
    )
    invalid_mnem_count = proc.stderr.count("invalid instruction mnemonic '__aw'")

    # 2. Cross-crate `.rmeta` consumer crash when upstream defines `.macro __aw` in `global_asm!`:
    up_src = work / "up_macro.rs"
    up_src.write_text(
        """core::arch::global_asm!(".macro __aw_up a, b\\nsub \\\\a, \\\\b\\n.endm");
#[inline]
pub unsafe fn inl_sub(mut a: u64, b: u64) -> u64 {
    core::arch::asm!("__aw_up {0:r}, {1:r}", inout(reg) a, in(reg) b, options(nomem, nostack));
    a
}
"""
    )
    up_rlib = work / "libup_macro.rlib"
    subprocess.run(
        [
            "rustup",
            "run",
            tc,
            "rustc",
            "--crate-type=rlib",
            "-C",
            "opt-level=3",
            "-C",
            "codegen-units=1",
            str(up_src),
            "-o",
            str(up_rlib),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    down_src = work / "down_macro.rs"
    down_src.write_text(
        """extern crate up_macro;
#[no_mangle]
pub unsafe extern "C" fn call_it(x: u64, y: u64) -> u64 { up_macro::inl_sub(x, y) }
"""
    )
    down_proc = subprocess.run(
        [
            "rustup",
            "run",
            tc,
            "rustc",
            "--crate-type=rlib",
            "-C",
            "opt-level=3",
            str(down_src),
            "--extern",
            f"up_macro={up_rlib}",
            "-o",
            str(work / "libdown.rlib"),
        ],
        capture_output=True,
        text=True,
    )

    # 3. Verify `rustc_codegen_llvm/src/asm.rs:192` `$` -> `$$` escaping AND `${:uid}` per-CGU reset:
    # Emit two LLVM `.ll` modules (`cgu0.ll`, `cgu1.ll`) compiled independently to `.o` via `clang`
    # to prove `${:uid}` resets to `0` in every CGU's `AsmPrinter`!
    uid_cgu_vals: list[str] = []
    for idx in (0, 1):
        ll_p = work / f"uid_cgu{idx}.ll"
        o_p = work / f"uid_cgu{idx}.o"
        ll_p.write_text(
            f"""target triple = "x86_64-unknown-linux-gnu"
define i64 @f{idx}(i64 %x) {{
  %r = call i64 asm "addq $$1, $0\\0A.pushsection .anneal.uid_test,\\22e\\22,@progbits\\0A.asciz \\22cgu={idx}:uid=${{:uid}}\\22\\0A.popsection", "=r,0"(i64 %x)
  ret i64 %r
}}
"""
        )
        subprocess.run(["llc", "-filetype=obj", "-O2", str(ll_p), "-o", str(o_p)], check=True)
        elf = parse_elf64_reloc(o_p)
        sec = [s for s in elf["shdrs"] if s["name"] == ".anneal.uid_test"][0]
        uid_cgu_vals.append(sec["data"].rstrip(b"\x00").decode("utf-8"))

    return {
        "cgu16_global_asm_rc": proc.returncode,
        "cgu16_invalid_mnemonic_errors": invalid_mnem_count,
        "rmeta_consumer_global_asm_rc": down_proc.returncode,
        "rmeta_consumer_failed_mnemonic": "invalid instruction mnemonic '__aw_up'" in down_proc.stderr,
        "per_cgu_uid_strings": uid_cgu_vals,
        "uid_resets_to_zero_across_cgus": uid_cgu_vals == ["cgu=0:uid=0", "cgu=1:uid=0"],
    }


def test_driver_multi_cgu_and_rmeta(
    drv_bin: Path, sysroot: str, work: Path
) -> dict[str, Any]:
    # Upstream rlib compiled with `-C codegen-units=16 -C opt-level=3`, `#[deny(named_asm_labels, binary_asm_labels)]`,
    # containing 16 modules, generic `asm!`, `#[inline]` `asm!`, `#[inline(never)]` 4x-unrolled `asm!`,
    # `#[unsafe(naked)]`, `sym` operand, and a numeric-label collision probe (`200000000:`).
    up_dir = work / "drv_up"
    up_dir.mkdir(exist_ok=True)
    mods = []
    for i in range(16):
        mods.append(
            f"""pub mod cgu_mod_{i} {{
    #[inline(never)]
    pub unsafe fn step_{i}(mut a: u64, b: u64) -> u64 {{
        core::arch::asm!(
            "sub {{0:r}}, {{1:r}}",
            inout(reg) a,
            in(reg) b,
            options(pure, nomem, nostack),
        );
        a
    }}
}}"""
        )

    up_rs = up_dir / "lib.rs"
    up_rs.write_text(
        """#![deny(named_asm_labels, binary_asm_labels)]

#[inline(never)]
pub extern "C" fn sym_target(x: u64) -> u64 {
    x.wrapping_add(7)
}

pub unsafe fn generic_add_const<const C: usize>(mut x: u64) -> u64 {
    core::arch::asm!(
        "add {0:r}, {c}",
        inout(reg) x,
        c = const C,
        options(pure, nomem, nostack),
    );
    x
}

#[inline]
pub unsafe fn inlined_sub_with_sym(mut a: u64, b: u64) -> (u64, usize) {
    let fn_addr: usize;
    core::arch::asm!(
        "200000000:",
        "sub {0:r}, {1:r}",
        "lea {2:r}, [rip + {s}]",
        inout(reg) a,
        in(reg) b,
        out(reg) fn_addr,
        s = sym sym_target,
        options(pure, nomem, nostack),
    );
    (a, fn_addr)
}

#[inline(never)]
pub unsafe fn unrolled_loop_4(arr: &[u64; 4], mut acc: u64) -> u64 {
    let mut i = 0;
    while i < 4 {
        core::arch::asm!(
            "sub {0:r}, {1:r}",
            inout(reg) acc,
            in(reg) arr[i],
            options(pure, nomem, nostack),
        );
        i += 1;
    }
    acc
}

#[unsafe(naked)]
pub unsafe extern "C" fn naked_inc(x: u64) -> u64 {
    core::arch::naked_asm!(
        "lea rax, [rdi + 1]",
        "ret",
    )
}
"""
        + "\n".join(mods)
        + "\n"
    )

    nonce_up = "aa11bb22cc33dd44ee55ff6677889900"
    env_up = os.environ.copy()
    env_up["RUSTC_BOOTSTRAP"] = "1"
    env_up["ANNEAL_SYSROOT"] = sysroot
    env_up["ANNEAL_ASM_WRAP_MODE"] = "cr_zero_drift"
    env_up["ANNEAL_SESSION_NONCE"] = nonce_up

    up_proc = subprocess.run(
        [
            str(drv_bin),
            "--edition=2021",
            "--crate-name=up_verified",
            "--crate-type=rlib",
            "-C",
            "opt-level=3",
            "-C",
            "codegen-units=16",
            "-C",
            "lto=off",
            "-C",
            "save-temps",
            "--emit=obj,link",
            str(up_rs),
            "--out-dir",
            str(up_dir),
        ],
        env=env_up,
        capture_output=True,
        text=True,
    )
    if up_proc.returncode != 0:
        raise RuntimeError(f"up_verified build failed:\n{up_proc.stderr}")

    up_objs = sorted(glob.glob(str(up_dir / "*.rcgu.o")))
    up_sites_all: list[dict[str, Any]] = []
    objs_with_sites = 0
    for o in up_objs:
        s = extract_attested_sites(o)
        if s:
            objs_with_sites += 1
            up_sites_all.extend(s)

    # Also test `mir_built_cr` hook on the exact same 16-CGU crate:
    mir_built_dir = work / "drv_mir_built"
    mir_built_dir.mkdir(exist_ok=True)
    env_mb = env_up.copy()
    env_mb["ANNEAL_ASM_WRAP_MODE"] = "mir_built_cr"
    mb_proc = subprocess.run(
        [
            str(drv_bin),
            "--edition=2021",
            "--crate-name=up_mb",
            "--crate-type=rlib",
            "-C",
            "opt-level=3",
            "-C",
            "codegen-units=16",
            "-C",
            "lto=off",
            "--emit=obj",
            str(up_rs),
            "--out-dir",
            str(mir_built_dir),
        ],
        env=env_mb,
        capture_output=True,
        text=True,
    )
    mb_sites = []
    for o in sorted(glob.glob(str(mir_built_dir / "*.rcgu.o"))):
        mb_sites.extend(extract_attested_sites(o))

    # Downstream executable compiled with `-C codegen-units=16` and a DIFFERENT session nonce!
    down_dir = work / "drv_down"
    down_dir.mkdir(exist_ok=True)
    down_rs = down_dir / "main.rs"
    mod_calls = "+ ".join(f"up_verified::cgu_mod_{i}::step_{i}(20, 5)" for i in range(16))
    down_rs.write_text(
        f"""#![deny(named_asm_labels, binary_asm_labels)]
extern crate up_verified;

fn main() {{
    unsafe {{
        let g = up_verified::generic_add_const::<9>(33);
        let (s, fp) = up_verified::inlined_sub_with_sym(50, 8);
        let u = up_verified::unrolled_loop_4(&[1, 2, 3, 4], 20);
        let nk = up_verified::naked_inc(41);
        let cgu_sum = {mod_calls};
        let mut local_val: u64 = 100;
        core::arch::asm!(
            "sub {{0:r}}, {{1:r}}",
            inout(reg) local_val,
            in(reg) 58u64,
            options(pure, nomem, nostack),
        );
        assert_eq!(g, 42);
        assert_eq!(s, 42);
        assert_eq!(fp, up_verified::sym_target as usize);
        assert_eq!(u, 10);
        assert_eq!(nk, 42);
        assert_eq!(cgu_sum, 16 * 15);
        assert_eq!(local_val, 42);
    }}
}}
"""
    )

    nonce_down = "11223344556677889900aabbccddeeff"
    env_down = env_up.copy()
    env_down["ANNEAL_SESSION_NONCE"] = nonce_down
    rlib_path = up_dir / "libup_verified.rlib"
    down_proc = subprocess.run(
        [
            str(drv_bin),
            "--edition=2021",
            "--crate-name=down_app",
            "--crate-type=bin",
            "-C",
            "opt-level=3",
            "-C",
            "codegen-units=16",
            "-C",
            "lto=off",
            "-C",
            "save-temps",
            "--emit=obj,link",
            str(down_rs),
            "--extern",
            f"up_verified={rlib_path}",
            "--out-dir",
            str(down_dir),
        ],
        env=env_down,
        capture_output=True,
        text=True,
    )
    if down_proc.returncode != 0:
        raise RuntimeError(f"down_app build failed:\n{down_proc.stderr}")

    run_bin = subprocess.run([str(down_dir / "down_app")], capture_output=True, text=True)
    down_objs = sorted(glob.glob(str(down_dir / "*.rcgu.o")))
    down_sites: list[dict[str, Any]] = []
    for o in down_objs:
        down_sites.extend(extract_attested_sites(o))

    nonces_seen_in_down = sorted({s["desc"].split("|", 1)[0] for s in down_sites})

    # Verify directive rejection (`.macro` inside user `asm!` rejected by driver):
    bad_rs = work / "bad_macro_in_asm.rs"
    bad_rs.write_text(
        """pub unsafe fn bad(mut x: u64) -> u64 {
    core::arch::asm!(".macro foo\\n.endm\\nadd {0:r}, 1", inout(reg) x);
    x
}
"""
    )
    bad_proc = subprocess.run(
        [
            str(drv_bin),
            "--edition=2021",
            "--crate-type=rlib",
            str(bad_rs),
            "-o",
            str(work / "libbad.rlib"),
        ],
        env=env_up,
        capture_output=True,
        text=True,
    )

    # Verifylinked binary stripped `.anneal.asm_sites` (`SHF_EXCLUDE`):
    bin_elf = parse_elf64_reloc(down_dir / "down_app")
    bin_has_anneal_sec = any(s["name"].startswith(".anneal.") for s in bin_elf["shdrs"])

    return {
        "upstream_cgu_objects": len(up_objs),
        "upstream_objs_with_sites": objs_with_sites,
        "upstream_attested_records": len(up_sites_all),
        "upstream_lint_warnings": len(up_proc.stderr.strip()),
        "all_same_section_and_nonempty": all(
            s["same_section"] and len(s["slice_hex"]) >= 4 and s["sites_shf_exclude"]
            for s in up_sites_all
        ),
        "mir_built_hook_rc": mb_proc.returncode,
        "mir_built_attested_records": len(mb_sites),
        "downstream_cgu_objects": len(down_objs),
        "downstream_attested_records": len(down_sites),
        "downstream_nonces_preserved": nonces_seen_in_down,
        "both_up_and_down_nonces_present": (
            nonce_up in nonces_seen_in_down and nonce_down in nonces_seen_in_down
        ),
        "downstream_exec_rc": run_bin.returncode,
        "linked_elf_stripped_shf_exclude": not bin_has_anneal_sec,
        "forbidden_macro_directive_rejected": (
            bad_proc.returncode != 0 and "forbidden in verified asm" in bad_proc.stderr
        ),
    }


def make_no_core_header() -> str:
    return """#![feature(no_core, lang_items, rustc_attrs)]
#![allow(internal_features)]
#![no_core]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
impl Copy for u64 {}
impl Copy for u32 {}
impl Copy for bool {}
#[rustc_builtin_macro] macro_rules! asm { () => {} }
"""


def test_cross_arch_text_invariance(
    drv_bin: Path, sysroot: str, work: Path
) -> dict[str, Any]:
    modes = ["off", "multiline_pushsection", "ifndef_macro", "cr_zero_drift"]
    arch_results: dict[str, Any] = {}

    # 1. x86_64: `je rel8` 35-site forward branch (~105 B < 127 B rel8 limit)
    x86_body = "\n            ".join(
        'asm!("add {0:r}, 1", inout(reg) acc, options(nomem, nostack));' for _ in range(35)
    )
    x86_src = work / "inv_x86.rs"
    x86_src.write_text(
        make_no_core_header()
        + f"""
#[no_mangle]
pub unsafe fn x86_rel8_span(flag: u64, mut acc: u64) -> u64 {{
    match flag {{
        0 => {{
            {x86_body}
        }}
        _ => {{}}
    }}
    acc
}}
"""
    )

    # 2. aarch64: `N = 5,000` `add {0:x}, {0:x}, #1` (`20,000 B < 32 KiB` `tbz` limit!)
    a64_body = "\n            ".join(
        'asm!("add {0:x}, {0:x}, #1", inout(reg) acc, options(nomem, nostack, preserves_flags));'
        for _ in range(5000)
    )
    a64_src = work / "inv_a64_5000.rs"
    a64_src.write_text(
        make_no_core_header()
        + f"""
#[no_mangle]
pub unsafe fn a64_tbz_5000(flag: bool, mut acc: u64) -> u64 {{
    match flag {{
        false => {{}}
        true => {{
            {a64_body}
        }}
    }}
    acc
}}
"""
    )

    # 3. riscv64gc: `N = 900` `addi {0}, {0}, 1` (`3,600 B < 4,096 B` `beqz` B-type ±4 KiB limit!)
    rv_body = "\n            ".join(
        'asm!("addi {0}, {0}, 1", inout(reg) acc, options(nomem, nostack, preserves_flags));'
        for _ in range(900)
    )
    rv_src = work / "inv_rv64_900.rs"
    rv_src.write_text(
        make_no_core_header()
        + f"""
#[no_mangle]
pub unsafe fn rv64_beqz_900(flag: u64, mut acc: u64) -> u64 {{
    match flag {{
        0 => {{}}
        _ => {{
            {rv_body}
        }}
    }}
    acc
}}
"""
    )

    specs = [
        ("x86_64", "x86_64-unknown-linux-gnu", x86_src, 35),
        ("aarch64_N5000", "aarch64-unknown-linux-gnu", a64_src, 5000),
        ("riscv64gc_N900", "riscv64gc-unknown-linux-gnu", rv_src, 900),
    ]

    for label, target, src_path, expected_sites in specs:
        per_mode: dict[str, Any] = {}
        for mode in modes:
            obj_path = work / f"{label}_{mode}.o"
            env = os.environ.copy()
            env["RUSTC_BOOTSTRAP"] = "1"
            env["ANNEAL_SYSROOT"] = sysroot
            env["ANNEAL_ASM_WRAP_MODE"] = mode
            env["ANNEAL_SESSION_NONCE"] = "cafebabe0123456789abcdef01234567"
            proc = subprocess.run(
                [
                    str(drv_bin),
                    "--edition=2021",
                    "--crate-type=lib",
                    "-C",
                    "opt-level=3",
                    "-C",
                    "codegen-units=1",
                    "--target",
                    target,
                    "--emit=obj",
                    str(src_path),
                    "-o",
                    str(obj_path),
                ],
                env=env,
                capture_output=True,
                text=True,
            )
            if proc.returncode != 0:
                raise RuntimeError(f"{label}/{mode} failed:\n{proc.stderr}")
            dig = text_sections_digest(obj_path)
            sites = extract_attested_sites(obj_path)
            elf_obj = parse_elf64_reloc(obj_path)
            head_hex = ""
            for s in elf_obj["shdrs"]:
                if (s["flags"] & SHF_EXECINSTR) and len(s["data"]) > 0:
                    head_hex = s["data"][:16].hex()
                    break
            per_mode[mode] = {
                "text_bytes": dig["text_bytes"],
                "sha256_16": dig["sha256_16"],
                "head16_hex": head_hex,
                "attested_sites": len(sites),
            }
        base_sha = per_mode["off"]["sha256_16"]
        base_len = per_mode["off"]["text_bytes"]
        arch_results[label] = {
            "modes": per_mode,
            "cr_zero_drift_exact_sha256_parity": (
                per_mode["cr_zero_drift"]["sha256_16"] == base_sha
                and per_mode["cr_zero_drift"]["text_bytes"] == base_len
                and per_mode["cr_zero_drift"]["attested_sites"] == expected_sites
            ),
            "multiline_byte_delta": per_mode["multiline_pushsection"]["text_bytes"] - base_len,
            "ifndef_macro_byte_delta": per_mode["ifndef_macro"]["text_bytes"] - base_len,
            "cr_zero_drift_byte_delta": per_mode["cr_zero_drift"]["text_bytes"] - base_len,
        }

    return arch_results


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--toolchains",
        nargs="+",
        default=["nightly-2026-06-01", "1.99.1", "nightly"],
    )
    parser.add_argument("--out", type=str, default="")
    args = parser.parse_args()

    here = Path(__file__).resolve().parent
    driver_src = here / "anneal_driver_prototype.rs"

    results: dict[str, Any] = {"toolchains": {}}
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        for tc in args.toolchains:
            tc_work = work / tc.replace("/", "_")
            tc_work.mkdir(exist_ok=True)
            drv_bin, sysroot = build_driver(tc, driver_src, tc_work)
            ver = (
                subprocess.check_output(["rustup", "run", tc, "rustc", "-vV"], text=True)
                .strip()
                .splitlines()[0]
            )
            cgu_fail = test_global_asm_cgu16_failure_and_uid_reset(tc, tc_work)
            multi_cgu = test_driver_multi_cgu_and_rmeta(drv_bin, sysroot, tc_work)
            arch_inv = test_cross_arch_text_invariance(drv_bin, sysroot, tc_work)
            results["toolchains"][tc] = {
                "rustc_version": ver,
                "baseline_fractures": cgu_fail,
                "driver_multi_cgu_and_rmeta": multi_cgu,
                "cross_arch_invariance": arch_inv,
            }

    out_json = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(out_json)
    print(out_json)


if __name__ == "__main__":
    main()
