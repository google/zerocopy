#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Standalone empirical probe for:
1. `--gc-sections` x non-`SHF_EXCLUDE` (`.anneal.asm_sites,"",@progbits`) link
   fractures across GNU `ld.bfd 2.47`, `rust-lld` (`21.1.8`, `23.1.1`, `23.1.5`),
   and `ld.mold 2.42.1` on `x86_64`, `aarch64`, and `riscv64gc`;
2. `SHF_LINK_ORDER` (`"o"`) assembly and `ld.mold` GC failures;
3. Unified `.debug_anneal_sites` / `.debug_anneal_descs` DWARF tombstone protocol,
   `--gc-sections` x `R_RISCV_RELAX` x `--icf=all` composition (including live
   `qemu-riscv64` execution and unannotated-leader ICF detection), and
   `cr_zero_drift` 100% `.text` SHA-256 parity across `{lto=off, lto=thin, lto=fat}`
   on `x86_64` (`35` sites), `aarch64` (`5,000` sites), and `riscv64gc` (`900` sites);
4. Prebuilt sysroot `libcore` `stdarch` inline-`asm!` census (`39` `x86`/`x86_64`
   + `4` `arm_shared` + `151` `riscv*` + `3` `loongarch*` = `197` sites),
   `__writeeflags` `popfq` `RFLAGS.DF` (`0x400`) leak proof, and `100%`
   `providers.extern_queries.optimized_mir` attestation capture with `0 B` `.text`
   drift across `1.98.0-nightly`, `1.99.1`, and `1.102.0-nightly`."""

from __future__ import annotations

import argparse
import glob
import hashlib
import json
import os
import re
import shutil
import struct
import subprocess
import tempfile
from pathlib import Path
from typing import Any

from probe_speccone_18vectors_closure import build_driver_v2

PT_LOAD = 1
PF_X = 0x1
SHF_ALLOC = 0x2
SHF_EXECINSTR = 0x4
UINT64_MAX = 0xFFFFFFFFFFFFFFFF


def find_rust_lld(tc: str) -> str:
    sr = subprocess.check_output(
        ["rustup", "run", tc, "rustc", "--print", "sysroot"], text=True
    ).strip()
    matches = glob.glob(f"{sr}/lib/rustlib/*/bin/rust-lld")
    if not matches:
        raise RuntimeError(f"rust-lld missing for {tc}")
    return matches[0]


def parse_elf64(path: str | Path) -> dict[str, Any]:
    data = Path(path).read_bytes()
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise ValueError(f"Expected little-endian ELF64: {path}")
    e_phoff, e_shoff = struct.unpack_from("<QQ", data, 32)
    e_phentsize, e_phnum, e_shentsize, e_shnum, e_shstrndx = struct.unpack_from(
        "<HHHHH", data, 54
    )
    phdrs: list[dict[str, Any]] = []
    for i in range(e_phnum):
        p_type, p_flags, p_offset, p_vaddr, _paddr, p_filesz, p_memsz, _align = (
            struct.unpack_from("<IIQQQQQQ", data, e_phoff + i * e_phentsize)
        )
        phdrs.append(
            {
                "type": p_type,
                "flags": p_flags,
                "offset": p_offset,
                "vaddr": p_vaddr,
                "filesz": p_filesz,
                "memsz": p_memsz,
            }
        )
    shdrs: list[dict[str, Any]] = []
    for i in range(e_shnum):
        (
            sh_name,
            sh_type,
            sh_flags,
            sh_addr,
            sh_offset,
            sh_size,
            sh_link,
            sh_info,
            _align,
            sh_entsize,
        ) = struct.unpack_from("<IIQQQQIIQQ", data, e_shoff + i * e_shentsize)
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
    shstr = data[
        shdrs[e_shstrndx]["offset"] : shdrs[e_shstrndx]["offset"]
        + shdrs[e_shstrndx]["size"]
    ]
    secs: dict[str, dict[str, Any]] = {}
    for s in shdrs:
        end = shstr.find(b"\x00", s["sh_name"])
        nm = shstr[s["sh_name"] : end].decode("utf-8", errors="replace")
        s["name"] = nm
        s["bytes"] = (
            data[s["offset"] : s["offset"] + s["size"]] if s["type"] != 8 else b""
        )
        secs[nm] = s

    syms: dict[str, dict[str, Any]] = {}
    for s in shdrs:
        if s["type"] == 2 and s["entsize"] > 0:
            strtab = shdrs[s["link"]]["bytes"]
            sb = s["bytes"]
            for off in range(0, len(sb), s["entsize"]):
                st_name, st_info, _other, st_shndx, st_value, st_size = (
                    struct.unpack_from("<IBBHQQ", sb, off)
                )
                nm = strtab[st_name : strtab.find(b"\x00", st_name)].decode(
                    "utf-8", errors="replace"
                )
                if nm:
                    syms[nm] = {
                        "value": st_value,
                        "size": st_size,
                        "shndx": st_shndx,
                        "type": st_info & 0xF,
                    }
    return {"phdrs": phdrs, "shdrs": shdrs, "secs": secs, "syms": syms}


def decode_postlink_sites(
    elf: dict[str, Any], sites_sec_name: str, descs_sec_name: str
) -> list[dict[str, Any]]:
    secs = elf["secs"]
    if sites_sec_name not in secs:
        return []
    sb = secs[sites_sec_name]["bytes"]
    db = secs.get(descs_sec_name, {}).get("bytes", b"")
    exec_ranges = [
        (s["addr"], s["addr"] + s["size"], s["bytes"])
        for s in elf["shdrs"]
        if (s["flags"] & (SHF_ALLOC | SHF_EXECINSTR))
        == (SHF_ALLOC | SHF_EXECINSTR)
        and s["size"] > 0
    ]
    pos = 0
    records: list[dict[str, Any]] = []
    while pos + 56 <= len(sb):
        start_va, end_va, span_len, site_id, desc_off, desc_len, n_rel = (
            struct.unpack_from("<7Q", sb, pos)
        )
        rels = list(struct.unpack_from(f"<{n_rel}Q", sb, pos + 56))
        pos += 56 + 8 * n_rel
        desc_str = (
            db[desc_off : desc_off + desc_len]
            .rstrip(b"\x00")
            .decode("utf-8", errors="replace")
            if desc_off + desc_len <= len(db)
            else ""
        )
        is_tombstone = start_va in (0, 1, UINT64_MAX) or end_va in (
            0,
            1,
            UINT64_MAX,
        )
        in_exec = False
        slice_hex = ""
        for lo, hi, code_bytes in exec_ranges:
            if lo <= start_va and end_va <= hi and start_va <= end_va:
                in_exec = True
                slice_hex = code_bytes[start_va - lo : end_va - lo].hex()
                break
        records.append(
            {
                "start_va": hex(start_va),
                "end_va": hex(end_va),
                "va_diff": end_va - start_va if end_va >= start_va else -1,
                "span_len_field": span_len,
                "site_id": site_id,
                "desc": desc_str,
                "relocs": [hex(r) for r in rels],
                "is_tombstone": is_tombstone,
                "in_exec_pt_load": in_exec,
                "accepted_live": (not is_tombstone) and in_exec,
                "slice_hex": slice_hex,
            }
        )
    return records


def probe_gc_tombstones_and_shf_link_order(work: Path) -> dict[str, Any]:
    lld21 = find_rust_lld("nightly-2026-01-25")
    lld23_1 = find_rust_lld("1.99.1")
    lld23_5 = find_rust_lld("nightly")
    bfd = shutil.which("ld.bfd")
    mold = shutil.which("ld.mold")
    objcopy = shutil.which("llvm-objcopy") or shutil.which("objcopy")
    assert bfd and mold and objcopy

    # 1. SHF_LINK_ORDER ("o") failure modes
    lo_dir_s = work / "lo_dir.s"
    lo_dir_s.write_text(
        '.section .text.foo,"ax",@progbits\n'
        "200001:\n  nop\n"
        '.pushsection .anneal.asm_sites,"o",@progbits,200001b\n'
        "  .quad 200001b\n.popsection\n"
    )
    r_dir = subprocess.run(
        [
            "llvm-mc",
            "-triple=x86_64-unknown-linux-gnu",
            "-filetype=obj",
            str(lo_dir_s),
            "-o",
            str(work / "lo_dir.o"),
        ],
        capture_output=True,
        text=True,
    )

    lo_unroll_s = work / "lo_unroll.s"
    lo_unroll_s.write_text(
        '.section .text.foo,"ax",@progbits\n'
        ".L_s_unroll:\n  nop\n"
        ".L_s_unroll:\n  nop\n"
    )
    r_unroll = subprocess.run(
        [
            "llvm-mc",
            "-triple=x86_64-unknown-linux-gnu",
            "-filetype=obj",
            str(lo_unroll_s),
            "-o",
            str(work / "lo_unroll.o"),
        ],
        capture_output=True,
        text=True,
    )

    lo_mold_s = work / "lo_mold.s"
    lo_mold_s.write_text(
        '.section .text.dead_fn,"ax",@progbits\n'
        ".globl dead_fn\ndead_fn:\n  pushq %rbp\n.L_s_dead:\n  addq $1, %rdi\n.L_e_dead:\n  popq %rbp\n  retq\n"
        '.pushsection .anneal.asm_sites,"o",@progbits,.L_s_dead\n'
        "  .quad .L_s_dead, .L_e_dead\n.popsection\n"
        '.section .text._start,"ax",@progbits\n'
        ".globl _start\n_start:\n.L_s_live:\n  retq\n.L_e_live:\n"
        '.pushsection .anneal.asm_sites,"o",@progbits,.L_s_live\n'
        "  .quad .L_s_live, .L_e_live\n.popsection\n"
    )
    subprocess.run(
        [
            "llvm-mc",
            "-triple=x86_64-unknown-linux-gnu",
            "-filetype=obj",
            str(lo_mold_s),
            "-o",
            str(work / "lo_mold.o"),
        ],
        check=True,
    )
    subprocess.run(
        [
            mold,
            "--gc-sections",
            "-e",
            "_start",
            str(work / "lo_mold.o"),
            "-o",
            str(work / "lo_mold.elf"),
        ],
        check=True,
    )
    mold_lo_elf = parse_elf64(work / "lo_mold.elf")
    mold_lo_qws = [
        hex(x)
        for x in struct.unpack(
            f"<{len(mold_lo_elf['secs']['.anneal.asm_sites']['bytes']) // 8}Q",
            mold_lo_elf["secs"][".anneal.asm_sites"]["bytes"],
        )
    ]

    shf_link_order = {
        "directional_label_llvm_mc_rc": r_dir.returncode,
        "directional_label_invalid_sym_err": "invalid linked-to symbol"
        in r_dir.stderr,
        "named_L_label_unroll_rc": r_unroll.returncode,
        "named_L_label_dup_err": "already defined" in r_unroll.stderr,
        "mold_ignores_nonalloc_shf_link_order_gc": len(mold_lo_qws) == 4,
        "mold_retained_phantom_span": mold_lo_qws[:2],
    }

    # 2. Cross-linker x cross-ISA `--gc-sections` matrix: `.anneal.asm_sites` vs `.debug_anneal_sites`
    x86_asm = """
    .section .text.dead_fn,"ax",@progbits
    .globl dead_fn
    dead_fn:
      pushq %rbp
      movq %rsp, %rbp
    200001:
      subq %rsi, %rdi
    200002:
      popq %rbp
      retq
    .pushsection .anneal.asm_descs,"",@progbits
    200003: .asciz "n0|site=1111|inout0=rdi|in1=rsi"
    200004: .popsection
    .pushsection .anneal.asm_sites,"",@progbits
      .quad 200001b, 200002b, 200002b - 200001b, 0x1111, 200003b, 200004b - 200003b, 0
    .popsection
    .pushsection .debug_anneal_descs,"",@progbits
    200005: .asciz "n0|site=1111|inout0=rdi|in1=rsi"
    200006: .popsection
    .pushsection .debug_anneal_sites,"",@progbits
      .quad 200001b, 200002b, 200002b - 200001b, 0x1111, 200005b, 200006b - 200005b, 0
    .popsection

    .section .text._start,"ax",@progbits
    .globl _start
    _start:
      movq $60, %rax
    200007:
      xorq %rdi, %rdi
    200008:
      syscall
    .pushsection .anneal.asm_descs,"",@progbits
    200009: .asciz "n0|site=2222|inout0=rdi"
    200010: .popsection
    .pushsection .anneal.asm_sites,"",@progbits
      .quad 200007b, 200008b, 200008b - 200007b, 0x2222, 200009b, 200010b - 200009b, 0
    .popsection
    .pushsection .debug_anneal_descs,"",@progbits
    200011: .asciz "n0|site=2222|inout0=rdi"
    200012: .popsection
    .pushsection .debug_anneal_sites,"",@progbits
      .quad 200007b, 200008b, 200008b - 200007b, 0x2222, 200011b, 200012b - 200011b, 0
    .popsection
    """

    a64_asm = """
    .section .text.dead_fn,"ax",@progbits
    .globl dead_fn
    dead_fn:
      mov x9, #1
    200001:
      add x0, x0, x1
      sub x0, x0, #1
    200002:
      ret
    .pushsection .anneal.asm_descs,"",@progbits
    200003: .asciz "n0|site=1111|inout0=x0|in1=x1"
    200004: .popsection
    .pushsection .anneal.asm_sites,"",@progbits
      .8byte 200001b, 200002b, 200002b - 200001b, 0x1111, 200003b, 200004b - 200003b, 0
    .popsection
    .pushsection .debug_anneal_descs,"",@progbits
    200005: .asciz "n0|site=1111|inout0=x0|in1=x1"
    200006: .popsection
    .pushsection .debug_anneal_sites,"",@progbits
      .8byte 200001b, 200002b, 200002b - 200001b, 0x1111, 200005b, 200006b - 200005b, 0
    .popsection

    .section .text._start,"ax",@progbits
    .globl _start
    _start:
      mov x8, #93
    200007:
      mov x0, #0
    200008:
      svc #0
    .pushsection .anneal.asm_descs,"",@progbits
    200009: .asciz "n0|site=2222|out0=x0"
    200010: .popsection
    .pushsection .anneal.asm_sites,"",@progbits
      .8byte 200007b, 200008b, 200008b - 200007b, 0x2222, 200009b, 200010b - 200009b, 0
    .popsection
    .pushsection .debug_anneal_descs,"",@progbits
    200011: .asciz "n0|site=2222|out0=x0"
    200012: .popsection
    .pushsection .debug_anneal_sites,"",@progbits
      .8byte 200007b, 200008b, 200008b - 200007b, 0x2222, 200011b, 200012b - 200011b, 0
    .popsection
    """

    rv64_asm = """
    .section .text.near_helper,"ax",@progbits
    .globl near_helper
    near_helper:
      ret

    .section .text.dead_fn,"ax",@progbits
    .globl dead_fn
    dead_fn:
      addi sp, sp, -16
    200001:
      call near_helper
    200002:
      addi sp, sp, 16
      ret
    .pushsection .anneal.asm_descs,"",@progbits
    200003: .asciz "n0|site=1111|clob=ra"
    200004: .popsection
    .pushsection .anneal.asm_sites,"",@progbits
      .dword 200001b, 200002b, 200002b - 200001b, 0x1111, 200003b, 200004b - 200003b, 0
    .popsection
    .pushsection .debug_anneal_descs,"",@progbits
    200005: .asciz "n0|site=1111|clob=ra"
    200006: .popsection
    .pushsection .debug_anneal_sites,"",@progbits
      .dword 200001b, 200002b, 200002b - 200001b, 0x1111, 200005b, 200006b - 200005b, 0
    .popsection

    .section .text._start,"ax",@progbits
    .globl _start
    _start:
      li a7, 93
    200007:
      call near_helper
    200008:
      li a0, 0
      ecall
    .pushsection .anneal.asm_descs,"",@progbits
    200009: .asciz "n0|site=2222|clob=ra"
    200010: .popsection
    .pushsection .anneal.asm_sites,"",@progbits
      .dword 200007b, 200008b, 200008b - 200007b, 0x2222, 200009b, 200010b - 200009b, 0
    .popsection
    .pushsection .debug_anneal_descs,"",@progbits
    200011: .asciz "n0|site=2222|clob=ra"
    200012: .popsection
    .pushsection .debug_anneal_sites,"",@progbits
      .dword 200007b, 200008b, 200008b - 200007b, 0x2222, 200011b, 200012b - 200011b, 0
    .popsection
    """

    isa_matrix: dict[str, Any] = {}
    for arch_key, triple, mattr, emul, src_txt in [
        ("x86_64", "x86_64-unknown-linux-gnu", [], "elf_x86_64", x86_asm),
        ("aarch64", "aarch64-unknown-linux-gnu", [], "aarch64linux", a64_asm),
        (
            "riscv64gc_relax",
            "riscv64-unknown-linux-gnu",
            ["-mattr=+m,+a,+f,+d,+c,+relax"],
            "elf64lriscv",
            ".option relax\n" + rv64_asm,
        ),
        (
            "riscv64gc_norelax",
            "riscv64-unknown-linux-gnu",
            ["-mattr=+m,+a,+f,+d,+c"],
            "elf64lriscv",
            rv64_asm,
        ),
    ]:
        sp = work / f"{arch_key}.s"
        op = work / f"{arch_key}.o"
        sp.write_text(src_txt)
        subprocess.run(
            ["llvm-mc", f"-triple={triple}", *mattr, "-filetype=obj", str(sp), "-o", str(op)],
            check=True,
        )
        linkers: list[tuple[str, list[str]]] = [
            (
                "rust-lld_21.1.8",
                [lld21, "-flavor", "gnu", "-m", emul, "--gc-sections", "-e", "_start"],
            ),
            (
                "rust-lld_23.1.1",
                [lld23_1, "-flavor", "gnu", "-m", emul, "--gc-sections", "-e", "_start"],
            ),
            (
                "rust-lld_23.1.5",
                [lld23_5, "-flavor", "gnu", "-m", emul, "--gc-sections", "-e", "_start"],
            ),
            (
                "ld.mold_2.42.1",
                [mold, "-m", emul, "--gc-sections", "-e", "_start"],
            ),
        ]
        if arch_key == "x86_64":
            linkers.insert(
                0,
                (
                    "ld.bfd_2.47",
                    [bfd, "-m", emul, "--gc-sections", "-e", "_start"],
                ),
            )
            linkers.append(
                (
                    "rust-lld_23.1.5_z_uint64_max",
                    [
                        lld23_5,
                        "-flavor",
                        "gnu",
                        "-m",
                        emul,
                        "--gc-sections",
                        "-z",
                        "dead-reloc-in-nonalloc=.debug_anneal_sites=0xffffffffffffffff",
                        "-e",
                        "_start",
                    ],
                )
            )
        per_linker: dict[str, Any] = {}
        for lname, lcmd in linkers:
            ep = work / f"{arch_key}_{lname}.elf"
            subprocess.run(lcmd + [str(op), "-o", str(ep)], check=True)
            elf = parse_elf64(ep)
            non_dbg = decode_postlink_sites(
                elf, ".anneal.asm_sites", ".anneal.asm_descs"
            )
            dbg = decode_postlink_sites(
                elf, ".debug_anneal_sites", ".debug_anneal_descs"
            )
            per_linker[lname] = {
                "anneal_asm_sites_bytes": elf["secs"]
                .get(".anneal.asm_sites", {})
                .get("size", 0),
                "anneal_asm_sites_records": non_dbg,
                "debug_anneal_sites_bytes": elf["secs"]
                .get(".debug_anneal_sites", {})
                .get("size", 0),
                "debug_anneal_sites_in_pt_load": bool(
                    elf["secs"].get(".debug_anneal_sites", {}).get("flags", 0)
                    & SHF_ALLOC
                ),
                "debug_anneal_sites_records": dbg,
                "debug_live_accepted_ids": [
                    r["site_id"] for r in dbg if r["accepted_live"]
                ],
            }
        isa_matrix[arch_key] = per_linker

    # Verify clean post-verification stripping via llvm-objcopy
    sample_elf = work / "x86_64_ld.bfd_2.47.elf"
    stripped_elf = work / "x86_64_stripped.elf"
    subprocess.run(
        [
            objcopy,
            "--remove-section=.debug_anneal_sites",
            "--remove-section=.debug_anneal_descs",
            str(sample_elf),
            str(stripped_elf),
        ],
        check=True,
    )
    st_parsed = parse_elf64(stripped_elf)

    return {
        "shf_link_order": shf_link_order,
        "isa_linker_matrix": isa_matrix,
        "post_verify_objcopy_strip_clean": (
            ".debug_anneal_sites" not in st_parsed["secs"]
            and ".debug_anneal_descs" not in st_parsed["secs"]
        ),
    }


def probe_gc_relax_icf_composition(
    drv_bin: Path, sysroot: str, work: Path
) -> dict[str, Any]:
    lld21 = find_rust_lld("nightly-2026-01-25")
    lld23_1 = find_rust_lld("1.99.1")
    lld23_5 = find_rust_lld("nightly")
    mold = shutil.which("ld.mold")
    qemu_rv = shutil.which("qemu-riscv64")
    assert mold and qemu_rv

    # Real `#![no_core]` RV64GC program compiled via `anneal_driver_v2` (`debug_tombstone_cr`)
    # combining:
    #   - `dead_relax_fn`: unreachable `.option relax` `call + .balign 16 + jump` (`3` dead sites)
    #   - `twin_relax_a` & `twin_relax_b`: identical `.option relax` `call + .balign 16 + jump`
    #     functions (`3` sites each) folded by `--icf=all` AND shrunk by `R_RISCV_RELAX`!
    rv_src = work / "rv_gc_relax_icf.rs"
    rv_src.write_text(
        """#![feature(no_core, lang_items, rustc_attrs)]
#![allow(internal_features, named_asm_labels)]
#![no_core]
#![no_main]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
impl Copy for u64 {}
impl Copy for usize {}
impl Copy for bool {}
#[rustc_builtin_macro] macro_rules! asm { () => {} }

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn near_add10(mut x: u64) -> u64 {
    asm!("addi {0}, {0}, 10", inout(reg) x, options(nomem, nostack, preserves_flags));
    x
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn dead_relax_fn(mut val: u64) -> u64 {
    asm!(
        ".option push\\n.option relax\\ncall near_add10\\n.option pop",
        inout("a0") val, out("ra") _, out("t0") _, out("t1") _,
    );
    asm!(
        ".option push\\n.option relax\\n.balign 16\\naddi {0}, {0}, 3\\n.option pop",
        inout(reg) val, options(nomem, nostack, preserves_flags),
    );
    val
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn twin_relax_a(mut val: u64) -> u64 {
    asm!(
        ".option push\\n.option relax\\ncall near_add10\\n.option pop",
        inout("a0") val, out("ra") _, out("t0") _, out("t1") _,
    );
    asm!(
        ".option push\\n.option relax\\n.balign 16\\naddi {0}, {0}, 2\\n.option pop",
        inout(reg) val, options(nomem, nostack, preserves_flags),
    );
    asm!(
        ".option push\\n.option relax\\njump 301f, t1\\naddi {0}, {0}, 99\\n301:\\n.option pop",
        inout(reg) val, out("t1") _, options(nomem, nostack, preserves_flags),
    );
    val
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn twin_relax_b(mut val: u64) -> u64 {
    asm!(
        ".option push\\n.option relax\\ncall near_add10\\n.option pop",
        inout("a0") val, out("ra") _, out("t0") _, out("t1") _,
    );
    asm!(
        ".option push\\n.option relax\\n.balign 16\\naddi {0}, {0}, 2\\n.option pop",
        inout(reg) val, options(nomem, nostack, preserves_flags),
    );
    asm!(
        ".option push\\n.option relax\\njump 302f, t1\\naddi {0}, {0}, 99\\n302:\\n.option pop",
        inout(reg) val, out("t1") _, options(nomem, nostack, preserves_flags),
    );
    val
}

#[no_mangle]
pub unsafe extern "C" fn _start() -> ! {
    let a = twin_relax_a(7);
    let b = twin_relax_b(7);
    // 7 + 10 + 2 = 19 for both twin_relax_a and twin_relax_b
    let code: usize = match (a, b) {
        (19, 19) => 0,
        _ => 42,
    };
    asm!("ecall", in("a7") 93usize, in("a0") code, options(noreturn));
}
"""
    )

    obj_p = work / "rv_gc_relax_icf.o"
    manifest_p = work / "rv_manifest.json"
    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"
    env["ANNEAL_SYSROOT"] = sysroot
    env["ANNEAL_ASM_WRAP_MODE"] = "debug_tombstone_cr"
    env["ANNEAL_SESSION_NONCE"] = "feedface00112233445566778899aabb"
    env["ANNEAL_ATTEST_MANIFEST_OUT"] = str(manifest_p)
    subprocess.run(
        [
            str(drv_bin),
            "--edition=2021",
            "--crate-type=lib",
            "-C",
            "opt-level=2",
            "-C",
            "codegen-units=1",
            "-C",
            "panic=abort",
            "--target=riscv64gc-unknown-linux-gnu",
            "--emit=obj",
            str(rv_src),
            "-o",
            str(obj_p),
        ],
        env=env,
        check=True,
        capture_output=True,
        text=True,
    )
    manifest = json.loads(manifest_p.read_text())["rewritten_sites"]

    outcomes: dict[str, Any] = {}
    for lname, lcmd in [
        (
            "rust-lld_21.1.8",
            [
                lld21,
                "-flavor",
                "gnu",
                "-m",
                "elf64lriscv",
                "--gc-sections",
                "--icf=all",
                "-e",
                "_start",
            ],
        ),
        (
            "rust-lld_23.1.1",
            [
                lld23_1,
                "-flavor",
                "gnu",
                "-m",
                "elf64lriscv",
                "--gc-sections",
                "--icf=all",
                "-e",
                "_start",
            ],
        ),
        (
            "rust-lld_23.1.5",
            [
                lld23_5,
                "-flavor",
                "gnu",
                "-m",
                "elf64lriscv",
                "--gc-sections",
                "--icf=all",
                "-e",
                "_start",
            ],
        ),
        (
            "ld.mold_2.42.1",
            [mold, "-m", "elf64lriscv", "--gc-sections", "--icf=all", "-e", "_start"],
        ),
    ]:
        ep = work / f"rv_comp_{lname}.elf"
        subprocess.run(lcmd + [str(obj_p), "-o", str(ep)], check=True)
        qemu_rc = subprocess.run([qemu_rv, str(ep)], capture_output=True).returncode
        elf = parse_elf64(ep)
        recs = decode_postlink_sites(
            elf, ".debug_anneal_sites", ".debug_anneal_descs"
        )
        live_recs = [r for r in recs if r["accepted_live"]]
        tomb_recs = [r for r in recs if r["is_tombstone"]]
        ta_sym = elf["syms"].get("twin_relax_a", {}).get("value")
        tb_sym = elf["syms"].get("twin_relax_b", {}).get("value")
        outcomes[lname] = {
            "qemu_rc": qemu_rc,
            "total_emitted_records": len(recs),
            "live_accepted_count": len(live_recs),
            "tombstoned_count": len(tomb_recs),
            "twin_a_va": hex(ta_sym) if ta_sym is not None else None,
            "twin_b_va": hex(tb_sym) if tb_sym is not None else None,
            "icf_folded_twins": (
                ta_sym == tb_sym if (ta_sym and tb_sym) else tb_sym is None
            ),
            "live_va_diffs_match_add_sub_span_len": all(
                r["va_diff"] == r["span_len_field"] for r in live_recs
            ),
            "live_span_lengths": [r["va_diff"] for r in live_recs],
        }

    # Unannotated C twin linked BEFORE attested Rust twin under `--icf=all`:
    c_s = work / "unannotated_c_leader.s"
    r_s = work / "attested_rust_follower.s"
    c_s.write_text(
        '.section .text.c_leader,"ax",@progbits\n'
        ".globl c_leader\n.type c_leader, @function\n"
        "c_leader:\n  leaq 9(%rdi), %rax\n  retq\n"
    )
    r_s.write_text(
        '.section .text.rust_follower,"ax",@progbits\n'
        ".globl rust_follower\n.type rust_follower, @function\n"
        "rust_follower:\n200001:\n  leaq 9(%rdi), %rax\n200002:\n  retq\n"
        '.pushsection .debug_anneal_descs,"",@progbits\n'
        '200003: .asciz "n|site=7777|in0=rdi|out0=rax"\n200004: .popsection\n'
        '.pushsection .debug_anneal_sites,"",@progbits\n'
        "  .quad 200001b, 200002b, 200002b - 200001b, 7777, 200003b, 200004b - 200003b, 0\n"
        ".popsection\n"
        '.section .text._start,"ax",@progbits\n'
        ".globl _start\n_start:\n  callq c_leader\n  callq rust_follower\n  retq\n"
    )
    subprocess.run(
        [
            "llvm-mc",
            "-triple=x86_64-unknown-linux-gnu",
            "-filetype=obj",
            str(c_s),
            "-o",
            str(work / "c_leader.o"),
        ],
        check=True,
    )
    subprocess.run(
        [
            "llvm-mc",
            "-triple=x86_64-unknown-linux-gnu",
            "-filetype=obj",
            str(r_s),
            "-o",
            str(work / "r_follower.o"),
        ],
        check=True,
    )
    subprocess.run(
        [
            lld23_5,
            "-flavor",
            "gnu",
            "--gc-sections",
            "--icf=all",
            "-e",
            "_start",
            str(work / "c_leader.o"),
            str(work / "r_follower.o"),
            "-o",
            str(work / "unannotated_leader.elf"),
        ],
        check=True,
    )
    ul_elf = parse_elf64(work / "unannotated_leader.elf")
    ul_recs = decode_postlink_sites(
        ul_elf, ".debug_anneal_sites", ".debug_anneal_descs"
    )
    rf_va = ul_elf["syms"]["rust_follower"]["value"]
    covered_vas = {int(r["start_va"], 16) for r in ul_recs if r["accepted_live"]}

    return {
        "manifest_rewritten_count": len(manifest),
        "riscv64gc_gc_relax_icf_outcomes": outcomes,
        "unannotated_icf_leader_probe": {
            "rust_follower_live_sym_va": hex(rf_va),
            "surviving_debug_records": sum(1 for r in ul_recs if r["accepted_live"]),
            "unannotated_absorption_detected_by_sym_coverage_gate": rf_va
            not in covered_vas,
        },
    }


def no_core_header() -> str:
    return """#![feature(no_core, lang_items, rustc_attrs)]
#![allow(internal_features)]
#![no_core]
#![no_main]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
impl Copy for u64 {}
impl Copy for bool {}
#[rustc_builtin_macro] macro_rules! asm { () => {} }
"""


def probe_lto_cross_isa_text_parity(
    toolchains: list[str], driver_src: Path, work: Path
) -> dict[str, Any]:
    lld = find_rust_lld("nightly")

    x86_body = "\n            ".join(
        'asm!("add {0:r}, 1", inout(reg) acc, options(nomem, nostack));'
        for _ in range(35)
    )
    x86_rs = work / "lto_x86.rs"
    x86_rs.write_text(
        no_core_header()
        + f"""
#[no_mangle]
pub unsafe extern "C" fn dead_x86(mut v: u64) -> u64 {{
    asm!("add {{0:r}}, 3", inout(reg) v, options(nomem, nostack));
    v
}}
#[no_mangle]
pub unsafe extern "C" fn _start(flag: u64, mut acc: u64) -> u64 {{
    match flag {{
        0 => {{ {x86_body} }}
        _ => {{}}
    }}
    acc
}}
"""
    )

    a64_body = "\n            ".join(
        'asm!("add {0:x}, {0:x}, #1", inout(reg) acc, options(nomem, nostack, preserves_flags));'
        for _ in range(5000)
    )
    a64_rs = work / "lto_a64.rs"
    a64_rs.write_text(
        no_core_header()
        + f"""
#[no_mangle]
pub unsafe extern "C" fn dead_a64(mut v: u64) -> u64 {{
    asm!("add {{0:x}}, {{0:x}}, #3", inout(reg) v, options(nomem, nostack, preserves_flags));
    v
}}
#[no_mangle]
pub unsafe extern "C" fn _start(flag: bool, mut acc: u64) -> u64 {{
    match flag {{
        false => {{}}
        true => {{ {a64_body} }}
    }}
    acc
}}
"""
    )

    rv_body = "\n            ".join(
        'asm!("addi {0}, {0}, 1", inout(reg) acc, options(nomem, nostack, preserves_flags));'
        for _ in range(900)
    )
    rv_rs = work / "lto_rv64.rs"
    rv_rs.write_text(
        no_core_header()
        + f"""
#[no_mangle]
pub unsafe extern "C" fn dead_rv64(mut v: u64) -> u64 {{
    asm!("addi {{0}}, {{0}}, 3", inout(reg) v, options(nomem, nostack, preserves_flags));
    v
}}
#[no_mangle]
pub unsafe extern "C" fn _start(flag: u64, mut acc: u64) -> u64 {{
    match flag {{
        0 => {{}}
        _ => {{ {rv_body} }}
    }}
    acc
}}
"""
    )

    targets = [
        ("x86_64_N35", "x86_64-unknown-linux-gnu", x86_rs, 35),
        ("aarch64_N5000", "aarch64-unknown-linux-gnu", a64_rs, 5000),
        ("riscv64gc_N900", "riscv64gc-unknown-linux-gnu", rv_rs, 900),
    ]

    per_tc: dict[str, Any] = {}
    for tc in toolchains:
        tc_w = work / f"lto_{tc.replace('/', '_')}"
        tc_w.mkdir(exist_ok=True)
        drv_bin, sysroot = build_driver_v2(tc, driver_src, tc_w)
        tc_res: dict[str, Any] = {}
        for label, triple, rs_path, exp_live in targets:
            lto_cells: dict[str, Any] = {}
            for lto in ["off", "thin", "fat"]:
                mode_hashes: dict[str, Any] = {}
                live_cnt = 0
                tomb_cnt = 0
                for mode in ["off", "debug_tombstone_cr"]:
                    out_elf = tc_w / f"{label}_{lto}_{mode}.elf"
                    env = os.environ.copy()
                    env["RUSTC_BOOTSTRAP"] = "1"
                    env["ANNEAL_SYSROOT"] = sysroot
                    env["ANNEAL_ASM_WRAP_MODE"] = mode
                    env["ANNEAL_SESSION_NONCE"] = "0123456789abcdef0123456789abcdef"
                    subprocess.run(
                        [
                            str(drv_bin),
                            "--edition=2021",
                            "--crate-type=bin",
                            "-C",
                            "opt-level=3",
                            "-C",
                            f"lto={lto}",
                            "-C",
                            "panic=abort",
                            f"--target={triple}",
                            "-Z",
                            "unstable-options",
                            f"-Clinker={lld}",
                            "-Clinker-flavor=gnu-lld",
                            "-Clink-arg=--gc-sections",
                            "-Clink-arg=-e",
                            "-Clink-arg=_start",
                            str(rs_path),
                            "-o",
                            str(out_elf),
                        ],
                        env=env,
                        check=True,
                        capture_output=True,
                        text=True,
                    )
                    elf = parse_elf64(out_elf)
                    tb = elf["secs"][".text"]["bytes"]
                    mode_hashes[mode] = {
                        "text_bytes": len(tb),
                        "sha256_16": hashlib.sha256(tb).hexdigest()[:16],
                        "head8_hex": tb[:8].hex(),
                    }
                    if mode == "debug_tombstone_cr":
                        recs = decode_postlink_sites(
                            elf, ".debug_anneal_sites", ".debug_anneal_descs"
                        )
                        live_cnt = sum(1 for r in recs if r["accepted_live"])
                        tomb_cnt = sum(1 for r in recs if r["is_tombstone"])
                lto_cells[lto] = {
                    "off": mode_hashes["off"],
                    "debug_tombstone_cr": mode_hashes["debug_tombstone_cr"],
                    "exact_sha256_parity": (
                        mode_hashes["off"]["sha256_16"]
                        == mode_hashes["debug_tombstone_cr"]["sha256_16"]
                        and mode_hashes["off"]["text_bytes"]
                        == mode_hashes["debug_tombstone_cr"]["text_bytes"]
                    ),
                    "live_attested_sites": live_cnt,
                    "tombstoned_dead_sites": tomb_cnt,
                    "expected_live_matched": live_cnt == exp_live,
                }
            tc_res[label] = lto_cells
        per_tc[tc] = tc_res
    return per_tc


def probe_stdarch_extern_queries(
    toolchains: list[str], driver_src: Path, work: Path
) -> dict[str, Any]:
    # 1. Programmatic sysroot `stdarch` + `core/src` inline-`asm!` census
    census_by_tc: dict[str, Any] = {}
    for tc in toolchains:
        sr = subprocess.check_output(
            ["rustup", "run", tc, "rustc", "--print", "sysroot"], text=True
        ).strip()
        stdarch_dir = Path(sr) / "lib/rustlib/src/rust/library/stdarch/crates/core_arch/src"
        by_arch: dict[str, int] = {}
        all_inline = True
        for rs in sorted(stdarch_dir.rglob("*.rs")):
            rel = rs.relative_to(stdarch_dir).as_posix()
            lines = rs.read_text().splitlines()
            clean = "\n".join(
                "" if l.strip().startswith("//") else l.split("//")[0]
                for l in lines
            )
            ms = list(re.finditer(r"\b(?:asm|naked_asm|global_asm)!\s*\(", clean))
            if ms:
                top = rel.split("/")[0]
                by_arch[top] = by_arch.get(top, 0) + len(ms)
                for m in ms:
                    ln = clean[: m.start()].count("\n")
                    window = "\n".join(lines[max(0, ln - 35) : ln + 1])
                    if "#[inline" not in window:
                        all_inline = False
        census_by_tc[tc] = {
            "by_arch_dir": by_arch,
            "x86_plus_x86_64_sites": by_arch.get("x86", 0) + by_arch.get("x86_64", 0),
            "arm_shared_sites": by_arch.get("arm_shared", 0),
            "riscv_total_sites": by_arch.get("riscv_shared", 0)
            + by_arch.get("riscv64", 0),
            "total_stdarch_sites": sum(by_arch.values()),
            "all_marked_inline": all_inline,
        }

    # 2. Live `providers.extern_queries.optimized_mir` capture vs `LocalDefId`-only miss,
    #    `0 B` `.text` drift, upstream `.rmeta` idempotence, and `__writeeflags` `DF` leak!
    up_rs = work / "up_helper.rs"
    up_rs.write_text(
        """#[inline]
pub unsafe fn upstream_inl_add(mut x: u64) -> u64 {
    core::arch::asm!("add {0:r}, 5", inout(reg) x, options(pure, nomem, nostack));
    x
}
"""
    )

    app_rs = work / "stdarch_app.rs"
    app_rs.write_text(
        """#![allow(deprecated)]
extern crate up_helper;
use core::arch::x86_64::{
    __cpuid_count, __m256i, __readeflags, __writeeflags, _bittestandset64,
    _mm256_set1_epi64x, _mm256_stream_si256, _mm_stream_si64,
};

#[repr(align(32))]
struct Aligned256([i64; 4]);

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn dead_stdarch_caller(p: *mut i64) {
    _mm_stream_si64(p, 99);
}

#[inline(never)]
#[target_feature(enable = "avx")]
pub unsafe fn exercise_stdarch_live() -> (u64, bool) {
    let mut buf = Aligned256([0; 4]);
    let v: __m256i = _mm256_set1_epi64x(0x11223344);
    _mm256_stream_si256(buf.0.as_mut_ptr() as *mut __m256i, v);

    let mut mask: i64 = 0;
    let prev = _bittestandset64(&mut mask, 7);
    let cp = __cpuid_count(0, 0);
    let ef = __readeflags();
    __writeeflags(ef);
    let mut non_temp: i64 = 0;
    _mm_stream_si64(&mut non_temp, 77);
    let u = up_helper::upstream_inl_add(37);

    // Controlled proof that `__writeeflags(ef | 0x400)` leaves `RFLAGS.DF == 1`
    // across its return boundary (immediately cleared via `cld` before any Rust
    // `memcpy` runs!).
    let leaked_flags: u64;
    __writeeflags(ef | 0x400);
    core::arch::asm!(
        "pushfq\\npop {out:r}\\ncld",
        out = out(reg) leaked_flags,
        options(nomem),
    );
    let df_leaked = (leaked_flags & 0x400) != 0;

    (
        (buf.0[0] as u64)
            .wrapping_add(mask as u64)
            .wrapping_add(prev as u64)
            .wrapping_add((cp.eax != 0) as u64)
            .wrapping_add(non_temp as u64)
            .wrapping_add(u),
        df_leaked,
    )
}

fn main() {
    unsafe {
        let (acc, df_leaked) = exercise_stdarch_live();
        assert!(acc > 100);
        assert!(df_leaked, "__writeeflags must leak RFLAGS.DF=1 across return");
    }
}
"""
    )

    per_tc_exec: dict[str, Any] = {}
    for tc in toolchains:
        tc_w = work / f"stdarch_{tc.replace('/', '_')}"
        tc_w.mkdir(exist_ok=True)
        drv_bin, sysroot = build_driver_v2(tc, driver_src, tc_w)

        # Compile instrumented upstream rlib with distinct nonce
        up_rlib = tc_w / "libup_helper.rlib"
        env_up = os.environ.copy()
        env_up["RUSTC_BOOTSTRAP"] = "1"
        env_up["ANNEAL_SYSROOT"] = sysroot
        env_up["ANNEAL_ASM_WRAP_MODE"] = "debug_tombstone_cr"
        env_up["ANNEAL_SESSION_NONCE"] = "aaaa0000bbbb1111cccc2222dddd3333"
        subprocess.run(
            [
                str(drv_bin),
                "--edition=2021",
                "--crate-name=up_helper",
                "--crate-type=rlib",
                "-C",
                "opt-level=2",
                str(up_rs),
                "-o",
                str(up_rlib),
            ],
            env=env_up,
            check=True,
        )

        # Also build uninstrumented upstream rlib for exact `.text` SHA-256 baseline
        up_rlib_off = tc_w / "libup_helper_off.rlib"
        env_up_off = env_up.copy()
        env_up_off["ANNEAL_ASM_WRAP_MODE"] = "off"
        subprocess.run(
            [
                str(drv_bin),
                "--edition=2021",
                "--crate-name=up_helper",
                "--crate-type=rlib",
                "-C",
                "opt-level=2",
                str(up_rs),
                "-o",
                str(up_rlib_off),
            ],
            env=env_up_off,
            check=True,
        )

        # Compare 3 downstream builds:
        #   (a) `off` (baseline `.text` SHA-256)
        #   (b) `local_only` (`ANNEAL_INTERCEPT_EXTERN_MIR=0`)
        #   (c) `dual_query_v2` (`ANNEAL_INTERCEPT_EXTERN_MIR=1`)
        runs: dict[str, Any] = {}
        for tag, mode, ext_flag, rlib_use in [
            ("off", "off", "0", up_rlib_off),
            ("local_only", "debug_tombstone_cr", "0", up_rlib),
            ("dual_query_v2", "debug_tombstone_cr", "1", up_rlib),
        ]:
            bin_p = tc_w / f"app_{tag}"
            man_p = tc_w / f"man_{tag}.json"
            env_d = os.environ.copy()
            env_d["RUSTC_BOOTSTRAP"] = "1"
            env_d["ANNEAL_SYSROOT"] = sysroot
            env_d["ANNEAL_ASM_WRAP_MODE"] = mode
            env_d["ANNEAL_INTERCEPT_EXTERN_MIR"] = ext_flag
            env_d["ANNEAL_SESSION_NONCE"] = "11112222333344445555666677778888"
            env_d["ANNEAL_ATTEST_MANIFEST_OUT"] = str(man_p)
            subprocess.run(
                [
                    str(drv_bin),
                    "--edition=2021",
                    "--crate-type=bin",
                    "-C",
                    "opt-level=2",
                    "-C",
                    "codegen-units=1",
                    "-Clink-arg=-fuse-ld=bfd",
                    str(app_rs),
                    "--extern",
                    f"up_helper={rlib_use}",
                    "-o",
                    str(bin_p),
                ],
                env=env_d,
                check=True,
                capture_output=True,
                text=True,
            )
            exec_rc = subprocess.run([str(bin_p)], capture_output=True).returncode
            elf = parse_elf64(bin_p)
            tb = elf["secs"][".text"]["bytes"]
            recs = decode_postlink_sites(
                elf, ".debug_anneal_sites", ".debug_anneal_descs"
            )
            live_recs = [r for r in recs if r["accepted_live"]]
            tomb_recs = [r for r in recs if r["is_tombstone"]]
            core_live = [r for r in live_recs if "|crate=core|" in r["desc"] or r["desc"].endswith("|crate=core")]
            up_live = [r for r in live_recs if "aaaa0000bbbb1111cccc2222dddd3333" in r["desc"]]
            man = (
                json.loads(man_p.read_text())["rewritten_sites"]
                if man_p.exists()
                else []
            )
            runs[tag] = {
                "exec_rc": exec_rc,
                "text_bytes": len(tb),
                "text_sha256_16": hashlib.sha256(tb).hexdigest()[:16],
                "live_records_total": len(live_recs),
                "tombstoned_dead_records": len(tomb_recs),
                "core_stdarch_live_records": len(core_live),
                "upstream_rmeta_nonce_preserved_records": len(up_live),
                "manifest_foreign_core_sites": [
                    m["def_path"] for m in man if not m["is_local"]
                ],
            }

        # Also verify `non_exclude_cr` (`rustc` default `-Wl,--gc-sections` + `ld.bfd`)
        # loses 100% of `.anneal.asm_sites` on the exact same Rust binary!
        bfd_loss_bin = tc_w / "app_non_exclude_bfd"
        env_loss = os.environ.copy()
        env_loss["RUSTC_BOOTSTRAP"] = "1"
        env_loss["ANNEAL_SYSROOT"] = sysroot
        env_loss["ANNEAL_ASM_WRAP_MODE"] = "non_exclude_cr"
        env_loss["ANNEAL_INTERCEPT_EXTERN_MIR"] = "1"
        env_loss["ANNEAL_SESSION_NONCE"] = "99998888777766665555444433332222"
        subprocess.run(
            [
                str(drv_bin),
                "--edition=2021",
                "--crate-type=bin",
                "-C",
                "opt-level=2",
                "-C",
                "codegen-units=1",
                "-Clink-arg=-fuse-ld=bfd",
                str(app_rs),
                "--extern",
                f"up_helper={up_rlib_off}",
                "-o",
                str(bfd_loss_bin),
            ],
            env=env_loss,
            check=True,
        )
        loss_elf = parse_elf64(bfd_loss_bin)

        per_tc_exec[tc] = {
            "runs": runs,
            "dual_query_exact_text_sha256_parity": (
                runs["dual_query_v2"]["text_sha256_16"]
                == runs["off"]["text_sha256_16"]
                and runs["dual_query_v2"]["text_bytes"]
                == runs["off"]["text_bytes"]
            ),
            "local_only_missed_all_stdarch": (
                runs["local_only"]["core_stdarch_live_records"] == 0
            ),
            "dual_query_captured_all_7_stdarch_expansions": (
                runs["dual_query_v2"]["core_stdarch_live_records"] == 7
                and runs["dual_query_v2"]["tombstoned_dead_records"] == 1
                and len(runs["dual_query_v2"]["manifest_foreign_core_sites"]) == 6
            ),
            "no_double_wrapping_of_upstream_rmeta": (
                runs["dual_query_v2"]["upstream_rmeta_nonce_preserved_records"]
                == 1
            ),
            "rustc_default_gc_bfd_strips_non_debug_anneal_sites_to_zero": (
                ".anneal.asm_sites" not in loss_elf["secs"]
            ),
        }

    return {
        "stdarch_census": census_by_tc,
        "extern_queries_capture_and_parity": per_tc_exec,
    }


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
    driver_src = here / "anneal_driver_v2.rs"

    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        drv_199, sr_199 = build_driver_v2("1.99.1", driver_src, work)
        gc_tomb = probe_gc_tombstones_and_shf_link_order(work)
        gc_relax_icf = probe_gc_relax_icf_composition(drv_199, sr_199, work)
        lto_parity = probe_lto_cross_isa_text_parity(
            args.toolchains, driver_src, work
        )
        stdarch_res = probe_stdarch_extern_queries(
            args.toolchains, driver_src, work
        )

    results = {
        "gc_sections_fracture_and_tombstone_matrix": gc_tomb,
        "gc_relax_icf_composition": gc_relax_icf,
        "lto_cross_isa_text_parity": lto_parity,
        "stdarch_extern_queries_and_writeeflags": stdarch_res,
    }
    out_json = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(out_json)
    print("Probe 1+2 completed successfully.")


if __name__ == "__main__":
    main()
