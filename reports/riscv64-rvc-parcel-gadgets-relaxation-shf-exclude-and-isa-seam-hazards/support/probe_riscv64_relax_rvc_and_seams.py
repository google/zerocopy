#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Standalone revalidation harness for RISC-V RVC parcel gadgets, R_RISCV_RELAX x SHF_EXCLUDE,
CGU .option/.attribute/.half/.byte hazards, fcsr/RVV clobbers, and STT_TLS mislinking.

Uses Python 3.10+ standard library only and executes all builds inside
`tempfile.TemporaryDirectory()` without leaving artifacts outside `support/`.
"""

from __future__ import annotations

import glob
import hashlib
import json
import os
import shutil
import struct
import subprocess
import tempfile
from collections import Counter
from pathlib import Path
from typing import Any


def _sysroot(tc: str) -> str:
    return subprocess.run(
        ["rustc", tc, "--print", "sysroot"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()


def _rust_lld(tc: str) -> str:
    sr = _sysroot(tc)
    matches = glob.glob(f"{sr}/lib/rustlib/*/bin/rust-lld")
    if not matches:
        raise RuntimeError(f"rust-lld not found in sysroot for {tc}")
    return matches[0]


def _parse_elf_sections(path: str) -> dict[str, dict[str, Any]]:
    data = Path(path).read_bytes()
    e_shoff = struct.unpack_from("<Q", data, 0x28)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 0x3A)
    shdrs = [
        struct.unpack_from("<IIQQQQIIQQ", data, e_shoff + i * e_shentsize)
        for i in range(e_shnum)
    ]
    shstr = data[shdrs[e_shstrndx][4] : shdrs[e_shstrndx][4] + shdrs[e_shstrndx][5]]
    out: dict[str, dict[str, Any]] = {}
    for s in shdrs:
        end = shstr.find(b"\x00", s[0])
        name = shstr[s[0] : end].decode("utf-8", errors="replace")
        out[name] = {
            "type": s[1],
            "flags": s[2],
            "addr": s[3],
            "offset": s[4],
            "size": s[5],
            "bytes": data[s[4] : s[4] + s[5]] if s[1] != 8 else b"",
        }
    return out


def probe_sysroot_and_relax_shf_exclude(
    tc_rv: str, lld_21: str, lld_23: str, mold: str | None, qemu: str
) -> dict[str, Any]:
    sr = _sysroot(tc_rv)
    rlibs = sorted(glob.glob(f"{sr}/lib/rustlib/riscv64gc-unknown-linux-gnu/lib/*.rlib"))
    reloc_totals: Counter[str] = Counter()
    relax_crates: dict[str, dict[str, int]] = {}

    with tempfile.TemporaryDirectory() as td:
        for rlib in rlibs:
            stem = os.path.basename(rlib).split("-")[0]
            sub = os.path.join(td, stem)
            os.makedirs(sub, exist_ok=True)
            subprocess.run(["ar", "x", rlib], cwd=sub, check=True)
            c_counts: Counter[str] = Counter()
            for obj in glob.glob(f"{sub}/*.o"):
                rel_txt = subprocess.run(
                    ["llvm-readelf", "-rW", obj],
                    capture_output=True,
                    text=True,
                    check=True,
                ).stdout
                for line in rel_txt.splitlines():
                    parts = line.split()
                    if len(parts) >= 3 and parts[2].startswith("R_RISCV_"):
                        c_counts[parts[2]] += 1
                        reloc_totals[parts[2]] += 1
            if c_counts["R_RISCV_RELAX"] or c_counts["R_RISCV_ALIGN"]:
                relax_crates[stem] = {
                    "R_RISCV_RELAX": c_counts["R_RISCV_RELAX"],
                    "R_RISCV_ALIGN": c_counts["R_RISCV_ALIGN"],
                    "R_RISCV_CALL_PLT": c_counts["R_RISCV_CALL_PLT"],
                }

        src = r'''#![no_std]
#![no_main]
#![allow(named_asm_labels)]

use core::arch::asm;
use core::panic::PanicInfo;

#[panic_handler]
fn panic(_: &PanicInfo) -> ! { loop {} }

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn near_callee(x: u64) -> u64 {
    x.wrapping_add(10)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn victim_with_spans(mut val: u64) -> u64 {
    unsafe {
        asm!(
            ".option push",
            ".option relax",
            ".L__s1_{uid}:",
            "call near_callee",
            ".L__e1_{uid}:",
            ".cfi_remember_state",
            ".cfi_def_cfa_offset 32",
            "c.addi a0, 1",
            ".L__s2_{uid}:",
            ".balign 16",
            "addi a0, a0, 2",
            ".L__e2_{uid}:",
            ".cfi_restore_state",
            ".L__s3_{uid}:",
            "jump .L__after_{uid}, t1",
            ".L__e3_{uid}:",
            "addi a0, a0, 99",
            ".L__after_{uid}:",
            ".option pop",
            ".pushsection .anneal.asm_sites,\"e\",@progbits",
            ".quad .L__s1_{uid}",
            ".quad .L__e1_{uid}",
            ".quad .L__s2_{uid}",
            ".quad .L__e2_{uid}",
            ".quad .L__s3_{uid}",
            ".quad .L__e3_{uid}",
            ".popsection",
            ".pushsection .anneal.asm_sites_keep,\"\",@progbits",
            ".quad .L__s1_{uid}",
            ".quad .L__e1_{uid}",
            ".quad .L__e1_{uid} - .L__s1_{uid}",
            ".quad .L__s2_{uid}",
            ".quad .L__e2_{uid}",
            ".quad .L__e2_{uid} - .L__s2_{uid}",
            ".quad .L__s3_{uid}",
            ".quad .L__e3_{uid}",
            ".quad .L__e3_{uid} - .L__s3_{uid}",
            ".popsection",
            inout("a0") val,
            out("ra") _,
            out("t0") _, out("t1") _, out("t2") _,
            out("a1") _, out("a2") _, out("a3") _, out("a4") _, out("a5") _, out("a6") _, out("a7") _,
            uid = const 101usize,
        );
    }
    val.wrapping_mul(2).wrapping_add(5)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    let r = unsafe { victim_with_spans(7) };
    let code = if r == 45 { 0usize } else { r as usize };
    unsafe {
        asm!("ecall", in("a7") 93usize, in("a0") code, options(noreturn));
    }
}
'''
        src_p = os.path.join(td, "relax_probe.rs")
        obj_p = os.path.join(td, "relax_probe.o")
        Path(src_p).write_text(src, encoding="utf-8")
        subprocess.run(
            [
                "rustc",
                tc_rv,
                "--target",
                "riscv64gc-unknown-linux-gnu",
                "-C",
                "opt-level=2",
                "-C",
                "codegen-units=1",
                "-C",
                "panic=abort",
                "-C",
                "force-unwind-tables=yes",
                "--emit=obj",
                src_p,
                "-o",
                obj_p,
            ],
            check=True,
        )
        obj_secs = _parse_elf_sections(obj_p)
        pre_fn_size = obj_secs[".text.victim_with_spans"]["size"]

        configs = [
            ("lld21_relax", [lld_21, "-flavor", "gnu", "-m", "elf64lriscv", "--emit-relocs", "-e", "_start"]),
            ("lld21_norelax", [lld_21, "-flavor", "gnu", "-m", "elf64lriscv", "--no-relax", "--emit-relocs", "-e", "_start"]),
            ("lld23_relax", [lld_23, "-flavor", "gnu", "-m", "elf64lriscv", "--emit-relocs", "-e", "_start"]),
            ("lld23_norelax", [lld_23, "-flavor", "gnu", "-m", "elf64lriscv", "--no-relax", "--emit-relocs", "-e", "_start"]),
        ]
        if mold:
            configs.extend(
                [
                    ("mold_relax", [mold, "-m", "elf64lriscv", "--emit-relocs", "-e", "_start"]),
                    ("mold_norelax", [mold, "-m", "elf64lriscv", "--no-relax", "--emit-relocs", "-e", "_start"]),
                ]
            )

        link_outcomes: dict[str, Any] = {}
        for name, cmd in configs:
            elf_p = os.path.join(td, f"{name}.elf")
            subprocess.run(cmd + [obj_p, "-o", elf_p], check=True)
            qemu_rc = subprocess.run([qemu, elf_p], capture_output=True).returncode
            secs = _parse_elf_sections(elf_p)
            kb = secs[".anneal.asm_sites_keep"]["bytes"]
            qwords = struct.unpack(f"<{len(kb)//8}Q", kb)
            spans = [
                {"start": hex(qwords[i]), "end": hex(qwords[i + 1]), "len": qwords[i + 2]}
                for i in range(0, len(qwords), 3)
            ]
            sym_out = subprocess.run(
                ["llvm-readelf", "-sW", elf_p], capture_output=True, text=True, check=True
            ).stdout
            fn_size = 0
            for l in sym_out.splitlines():
                if l.endswith(" victim_with_spans"):
                    fn_size = int(l.split()[2])
                    break
            link_outcomes[name] = {
                "qemu_rc": qemu_rc,
                "post_fn_size": fn_size,
                "shf_exclude_retained": ".anneal.asm_sites" in secs,
                "shf_exclude_rela_retained": ".rela.anneal.asm_sites" in secs,
                "keep_section_retained": ".anneal.asm_sites_keep" in secs,
                "relocated_spans": spans,
            }

    return {
        "sysroot_rlibs_scanned": len(rlibs),
        "sysroot_reloc_totals": dict(reloc_totals.most_common(22)),
        "sysroot_crates_with_relax": relax_crates,
        "pre_link_victim_fn_size": pre_fn_size,
        "pre_link_site3_end_offset": 38,
        "link_outcomes": link_outcomes,
    }


def probe_rvc_gadgets_and_cgu_hazards(tc_rv: str, lld_21: str, qemu: str) -> dict[str, Any]:
    sr = _sysroot(tc_rv)
    rvc_vals = [h for h in range(0x10000) if (h & 3) != 3]

    with tempfile.TemporaryDirectory() as td:
        asm_p = os.path.join(td, "all_rvc.s")
        obj_p = os.path.join(td, "all_rvc.o")
        with open(asm_p, "w", encoding="utf-8") as f:
            f.write(".text\n.globl all_rvc\nall_rvc:\n")
            for h in rvc_vals:
                f.write(f"  .2byte 0x{h:04x}\n")
        subprocess.run(
            [
                "llvm-mc",
                "--triple=riscv64-unknown-linux-gnu",
                "-mattr=+m,+a,+f,+d,+c,+zca,+zcd",
                "-filetype=obj",
                asm_p,
                "-o",
                obj_p,
            ],
            check=True,
        )
        dump = subprocess.run(
            ["llvm-objdump", "-d", "-M", "no-aliases", "--mattr=+m,+a,+f,+d,+c,+zca,+zcd", obj_p],
            capture_output=True,
            text=True,
            check=True,
        ).stdout
        rvc_table: dict[int, tuple[str, str]] = {}
        for line in dump.splitlines():
            if ":" in line and "\t" in line:
                parts = line.split("\t")
                try:
                    off = int(parts[0].split(":")[0].strip(), 16)
                except ValueError:
                    continue
                mnem = parts[1].strip() if len(parts) > 1 else "<unknown>"
                ops = parts[2].strip() if len(parts) > 2 else ""
                rvc_table[rvc_vals[off // 2]] = (mnem, ops)

        def classify(mnem: str, ops: str) -> str:
            if mnem in ("<unknown>", "c.unimp") or mnem.startswith("."):
                return "illegal_16b"
            if mnem in ("c.jr", "c.jalr"):
                return "indirect_jump_call_c_jr_jalr"
            if mnem in ("c.j", "c.beqz", "c.bnez"):
                return "direct_branch_jump_c_j_bz"
            if mnem == "c.ebreak":
                return "ebreak_trap"
            if mnem in ("c.ld", "c.ldsp", "c.lw", "c.lwsp", "c.fld", "c.fldsp"):
                return "rvc_load"
            if mnem in ("c.sd", "c.sdsp", "c.sw", "c.swsp", "c.fsd", "c.fsdsp"):
                return "rvc_store"
            if mnem in ("c.addi16sp", "c.addi4spn") or ops.startswith("sp,"):
                return "sp_mutation"
            return "rvc_alu_reg"

        valid_16b_space = sum(1 for m, o in rvc_table.values() if classify(m, o) != "illegal_16b")

        all_objs: list[str] = []
        for crate in ("libcore", "liballoc", "libstd"):
            rlib = glob.glob(f"{sr}/lib/rustlib/riscv64gc-unknown-linux-gnu/lib/{crate}-*.rlib")[0]
            sub = os.path.join(td, crate)
            os.makedirs(sub)
            subprocess.run(["ar", "x", rlib], cwd=sub, check=True)
            all_objs.extend(sorted(glob.glob(f"{sub}/*.o")))

        total_insns = insns_16 = insns_32 = 0
        cats: Counter[str] = Counter()
        cross32: Counter[str] = Counter()
        for p in all_objs:
            dtxt = subprocess.run(
                ["llvm-objdump", "-d", "-M", "no-aliases", "--mattr=+m,+a,+f,+d,+c,+zca,+zcd", p],
                capture_output=True,
                text=True,
                check=True,
            ).stdout
            sec_insns: list[tuple[int, int, int]] = []

            def flush_sec(items: list[tuple[int, int, int]]) -> None:
                amap = {a: (s, v) for a, s, v in items}
                for addr, sz, val in items:
                    if sz == 4 and (((val >> 16) & 3) == 3) and (addr + 4) in amap:
                        w32 = ((val >> 16) & 0xFFFF) | ((amap[addr + 4][1] & 0xFFFF) << 16)
                        op7 = w32 & 0x7F
                        if op7 == 0x73:
                            cross32["SYSTEM_0x73"] += 1
                        elif op7 == 0x67:
                            cross32["JALR_0x67"] += 1
                        elif op7 == 0x6F:
                            cross32["JAL_0x6f"] += 1
                        elif op7 == 0x63:
                            cross32["BRANCH_0x63"] += 1
                        elif op7 == 0x03:
                            cross32["LOAD_0x03"] += 1
                        elif op7 == 0x23:
                            cross32["STORE_0x23"] += 1

            for line in dtxt.splitlines():
                if line.startswith("Disassembly of section "):
                    flush_sec(sec_insns)
                    sec_insns = []
                    continue
                if ":" in line and "\t" in line:
                    left = line.split("\t")[0]
                    if ":" not in left:
                        continue
                    addr_s, hex_s = left.split(":", 1)
                    hex_s = hex_s.strip().replace(" ", "")
                    try:
                        addr = int(addr_s.strip(), 16)
                        val = int(hex_s, 16)
                    except ValueError:
                        continue
                    sz = len(hex_s) // 2
                    if sz not in (2, 4):
                        continue
                    sec_insns.append((addr, sz, val))
                    total_insns += 1
                    if sz == 2:
                        insns_16 += 1
                    else:
                        insns_32 += 1
                        hi16 = (val >> 16) & 0xFFFF
                        if (hi16 & 3) != 3:
                            m16, o16 = rvc_table[hi16]
                            cats[classify(m16, o16)] += 1
                        else:
                            cats["low2_eq_11_4b_prefix"] += 1
            flush_sec(sec_insns)

        valid_hits = sum(v for k, v in cats.items() if k not in ("illegal_16b", "low2_eq_11_4b_prefix"))

        # Live QEMU execution of pc+2 c.sd + pc+2 c.jr + trailing .2byte 0x0537 ret-swallowing fallthrough
        live_src = r'''#![no_std]
#![no_main]
use core::arch::{asm, naked_asm};
use core::panic::PanicInfo;
#[panic_handler] fn panic(_: &PanicInfo) -> ! { loop {} }

#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn benign_4byte_store_gadget(ptr: *mut u64, val: u64) {
    naked_asm!(
        ".option push",
        ".option norvc",
        ".balign 4",
        "lui t0, 0xe10c0",
        "jalr x0, 0(ra)",
        ".option pop",
    );
}

#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn benign_4byte_jr_gadget(arg: u64, _u: u64, target: usize) -> u64 {
    naked_asm!(
        ".option push",
        ".option norvc",
        ".balign 4",
        "lui t0, 0x86020",
        "addi a0, zero, 1",
        "jalr x0, 0(ra)",
        ".option pop",
    );
}

#[inline(always)]
unsafe fn inlined_trailing_half11() {
    unsafe {
        asm!(
            ".2byte 0x0537",
            ".pushsection .anneal.asm_sites,\"e\",@progbits",
            ".quad 1234",
            ".popsection",
            options(nomem, nostack, preserves_flags)
        );
    }
}

#[unsafe(no_mangle)]
#[unsafe(link_section = ".text.fallthrough_pair")]
#[inline(never)]
pub unsafe extern "C" fn caller_corrupted_by_half11(val: u64) -> u64 {
    unsafe { inlined_trailing_half11(); }
    val.wrapping_add(1)
}

#[unsafe(no_mangle)]
#[unsafe(link_section = ".text.fallthrough_pair")]
#[inline(never)]
pub extern "C" fn secret_fallthrough_target(x: u64) -> u64 {
    x.wrapping_add(0x7777)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    let mut slot: u64 = 0x1111_2222_3333_4444;
    unsafe { benign_4byte_store_gadget(&raw mut slot, 0xdead_beef_cafe_babe); }
    let a_ok = slot == 0x1111_2222_3333_4444;
    let mid_store: unsafe extern "C" fn(*mut u64, u64) =
        unsafe { core::mem::transmute((benign_4byte_store_gadget as *const () as usize) + 2) };
    unsafe { mid_store(&raw mut slot, 0xdead_beef_cafe_babe); }
    let a_gadget = slot == 0xdead_beef_cafe_babe;

    let b_ok = unsafe { benign_4byte_jr_gadget(0x1000, 0, secret_fallthrough_target as *const () as usize) } == 1;
    let mid_jr: unsafe extern "C" fn(u64, u64, usize) -> u64 =
        unsafe { core::mem::transmute((benign_4byte_jr_gadget as *const () as usize) + 2) };
    let b_gadget = unsafe { mid_jr(0x1000, 0, secret_fallthrough_target as *const () as usize) } == 0x8777;

    // `caller_corrupted_by_half11` has its `ret` (`0x8082`) swallowed by `.2byte 0x0537` into `lui a0, 0x80820`
    // (RV64 sign-extended `0xffff_ffff_8082_0000`), falling straight through into `secret_fallthrough_target` (`0xffff_ffff_8082_7777`)!
    let c_res = unsafe { caller_corrupted_by_half11(41) };
    let c_swallowed_ret = c_res == 0xffff_ffff_8082_7777;

    let all_ok = a_ok && a_gadget && b_ok && b_gadget && c_swallowed_ret;
    unsafe {
        asm!("ecall", in("a7") 93usize, in("a0") if all_ok { 0usize } else { 42usize }, options(noreturn));
    }
}
'''
        l_rs = os.path.join(td, "live_gadgets.rs")
        l_elf = os.path.join(td, "live_gadgets.elf")
        Path(l_rs).write_text(live_src, encoding="utf-8")
        subprocess.run(
            [
                "rustc",
                tc_rv,
                "--target",
                "riscv64gc-unknown-linux-gnu",
                "-C",
                "opt-level=2",
                "-C",
                "codegen-units=1",
                "-C",
                "panic=abort",
                "-C",
                "relocation-model=static",
                "-C",
                f"linker={lld_21}",
                "-C",
                "linker-flavor=ld.lld",
                "-C",
                "link-arg=-e_start",
                l_rs,
                "-o",
                l_elf,
            ],
            check=True,
        )
        live_qemu_rc = subprocess.run([qemu, l_elf], capture_output=True).returncode

        # CGU .option / .attribute matrix & getInlineAsmLength Bcc drift at N=105 and N=520
        cgu_cases = {
            "baseline": "",
            "uncalled_option_norvc": '#[unsafe(no_mangle)] pub unsafe fn a_att() { unsafe { core::arch::asm!(".option norvc"); } }',
            "uncalled_option_relax": '#[unsafe(no_mangle)] pub unsafe fn a_att() { unsafe { core::arch::asm!(".option relax"); } }',
            "uncalled_option_arch_plus_v": '#[unsafe(no_mangle)] pub unsafe fn a_att() { unsafe { core::arch::asm!(".option arch, +v\\nvsetivli zero, 4, e64, m1, ta, ma"); } }',
            "uncalled_attribute_arch_poison": '#[unsafe(no_mangle)] pub unsafe fn a_att() { unsafe { core::arch::asm!(".attribute arch, \\"rv64i2p1\\""); } }',
        }
        cgu_results: dict[str, Any] = {}
        for name, snip in cgu_cases.items():
            code = f'''#![no_std]
use core::panic::PanicInfo;
#[panic_handler] fn panic(_: &PanicInfo) -> ! {{ loop {{}} }}
{snip}
#[unsafe(no_mangle)] #[inline(never)]
pub extern "C" fn z_pure_callee(x: u64) -> u64 {{ x.wrapping_add(1) }}
#[unsafe(no_mangle)] #[inline(never)]
pub extern "C" fn z_pure_victim(x: u64, y: u64) -> u64 {{
    z_pure_callee(x).wrapping_add(y)
}}
'''
            rs = os.path.join(td, f"{name}.rs")
            obj = os.path.join(td, f"{name}.o")
            asm_f = os.path.join(td, f"{name}.s")
            obj_s = os.path.join(td, f"{name}_s.o")
            Path(rs).write_text(code, encoding="utf-8")
            subprocess.run(
                [
                    "rustc",
                    tc_rv,
                    "--target",
                    "riscv64gc-unknown-linux-gnu",
                    "--crate-type=lib",
                    "-C",
                    "opt-level=2",
                    "-C",
                    "codegen-units=1",
                    "-C",
                    "panic=abort",
                    "--emit=obj",
                    rs,
                    "-o",
                    obj,
                ],
                check=True,
            )
            arch_txt = subprocess.run(
                ["llvm-readobj", "--arch-specific", obj], capture_output=True, text=True, check=True
            ).stdout
            arch_val = ""
            lines_a = [l.strip() for l in arch_txt.splitlines()]
            for i, l in enumerate(lines_a):
                if l == "TagName: arch" and i + 1 < len(lines_a):
                    arch_val = lines_a[i + 1].removeprefix("Value: ").strip()
            dis_o = subprocess.run(
                ["llvm-objdump", "-dr", "--disassemble-symbols=z_pure_victim", obj],
                capture_output=True,
                text=True,
                check=True,
            ).stdout
            o_rvc = any(
                len(l.split("\t")[0].split(":", 1)[1].strip().replace(" ", "")) == 4
                for l in dis_o.splitlines()
                if "\t" in l and ":" in l.split("\t")[0]
            )
            o_relax = "R_RISCV_RELAX" in dis_o

            subprocess.run(
                [
                    "rustc",
                    tc_rv,
                    "--target",
                    "riscv64gc-unknown-linux-gnu",
                    "--crate-type=lib",
                    "-C",
                    "opt-level=2",
                    "-C",
                    "codegen-units=1",
                    "-C",
                    "panic=abort",
                    "--emit=asm",
                    rs,
                    "-o",
                    asm_f,
                ],
                check=True,
            )
            subprocess.run(
                [
                    "llvm-mc",
                    "--triple=riscv64-unknown-linux-gnu",
                    "-mattr=+m,+a,+f,+d,+c",
                    "-filetype=obj",
                    asm_f,
                    "-o",
                    obj_s,
                ],
                check=True,
            )
            dis_s = subprocess.run(
                ["llvm-objdump", "-dr", "--disassemble-symbols=z_pure_victim", obj_s],
                capture_output=True,
                text=True,
                check=True,
            ).stdout
            s_rvc = any(
                len(l.split("\t")[0].split(":", 1)[1].strip().replace(" ", "")) == 4
                for l in dis_s.splitlines()
                if "\t" in l and ":" in l.split("\t")[0]
            )
            s_relax = "R_RISCV_RELAX" in dis_s
            cgu_results[name] = {
                "obj_streamer_tag_arch": arch_val,
                "obj_streamer_pure_rvc": o_rvc,
                "obj_streamer_pure_relax": o_relax,
                "asm_streamer_pure_rvc": s_rvc,
                "asm_streamer_pure_relax": s_relax,
            }

        bcc_results: dict[str, Any] = {}
        for n_sites in (80, 105, 520):
            row: dict[str, Any] = {}
            for mode in ("uninstrumented", "multiline_pushsection", "zero_sep_site_macro"):
                macro_def = (
                    r'''
core::arch::global_asm!(
    ".macro __aw id, reg",
    "1: addi \\reg, \\reg, 1",
    ".pushsection .anneal.asm_sites,\"e\",@progbits",
    ".quad 1b",
    ".quad \\id",
    ".popsection",
    ".endm"
);
'''
                    if mode == "zero_sep_site_macro"
                    else ""
                )
                body = []
                for k in range(n_sites):
                    if mode == "uninstrumented":
                        body.append('asm!("addi {0}, {0}, 1", inout(reg) acc, options(nomem, nostack, preserves_flags));')
                    elif mode == "multiline_pushsection":
                        body.append(
                            f'''asm!(
                                "1:", "addi {{0}}, {{0}}, 1", "2:",
                                ".pushsection .anneal.asm_sites,\\"e\\",@progbits",
                                ".quad 1b", ".quad 2b", ".quad {k}", ".popsection",
                                ".pushsection .anneal.asm_descs,\\"e\\",@progbits",
                                ".asciz \\"0={{0}}\\"", ".popsection",
                                inout(reg) acc, options(nomem, nostack, preserves_flags)
                            );'''
                        )
                    else:
                        body.append(f'asm!("__aw {k}, {{0}}", inout(reg) acc, options(nomem, nostack, preserves_flags));')
                bsrc = f'''#![no_std]
use core::arch::asm;
use core::panic::PanicInfo;
#[panic_handler] fn panic(_: &PanicInfo) -> ! {{ loop {{}} }}
{macro_def}
#[unsafe(no_mangle)] #[inline(never)]
pub unsafe extern "C" fn true_bcc(flag: u64, mut acc: u64, z: u64) -> u64 {{
    if flag != 0 {{
        unsafe {{ {chr(10).join(body)} }}
    }}
    acc.wrapping_mul(z | 1).wrapping_add(flag ^ 0x55)
}}
'''
                brs = os.path.join(td, f"bcc_{n_sites}_{mode}.rs")
                bobj = os.path.join(td, f"bcc_{n_sites}_{mode}.o")
                Path(brs).write_text(bsrc, encoding="utf-8")
                subprocess.run(
                    [
                        "rustc",
                        tc_rv,
                        "--target",
                        "riscv64gc-unknown-linux-gnu",
                        "--crate-type=lib",
                        "-C",
                        "opt-level=2",
                        "-C",
                        "codegen-units=1",
                        "-C",
                        "panic=abort",
                        "--emit=obj",
                        brs,
                        "-o",
                        bobj,
                    ],
                    check=True,
                )
                tb = _parse_elf_sections(bobj)[".text.true_bcc"]["bytes"]
                row[mode] = {
                    "size_bytes": len(tb),
                    "sha256_16": hashlib.sha256(tb).hexdigest()[:16],
                }
            bcc_results[str(n_sites)] = row

    return {
        "rvc_16bit_encoding_space": {
            "total_low2_ne_11": len(rvc_table),
            "valid_non_trapping_rv64gc": valid_16b_space,
            "valid_pct": round(valid_16b_space / len(rvc_table) * 100, 2),
        },
        "sysroot_libcore_liballoc_libstd_census": {
            "total_insns": total_insns,
            "insns_16b": insns_16,
            "insns_32b": insns_32,
            "pc_plus_2_low2_ne_11": insns_32 - cats["low2_eq_11_4b_prefix"],
            "pc_plus_2_low2_ne_11_pct": round((insns_32 - cats["low2_eq_11_4b_prefix"]) / insns_32 * 100, 2),
            "pc_plus_2_valid_rvc": valid_hits,
            "pc_plus_2_valid_rvc_pct": round(valid_hits / insns_32 * 100, 2),
            "categories": dict(cats),
            "cross_boundary_32b": dict(cross32),
        },
        "live_qemu_gadgets_and_half11_ret_swallow_rc": live_qemu_rc,
        "cgu_containment_matrix": cgu_results,
        "bcc_get_inline_asm_length_drift": bcc_results,
    }


def probe_preserves_flags_rvv_and_stt_tls(
    tc_rv: str,
    tc_nightly_nocore: str,
    lld_21: str,
    lld_23_1: str,
    lld_23_5: str,
    mold: str | None,
    qemu: str,
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        ir_src = r'''#![allow(internal_features)]
#![feature(no_core, lang_items, rustc_attrs)]
#![no_core]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[rustc_builtin_macro] macro_rules! asm { () => {} }

#[unsafe(no_mangle)] pub unsafe fn ir_default() { unsafe { asm!("nop"); } }
#[unsafe(no_mangle)] pub unsafe fn ir_preserves() { unsafe { asm!("nop", options(preserves_flags)); } }
#[unsafe(no_mangle)] pub unsafe fn ir_v0_clobber() { unsafe { asm!("nop", out("v0") _); } }
'''
        ir_rs = os.path.join(td, "ir.rs")
        ir_ll = os.path.join(td, "ir.ll")
        Path(ir_rs).write_text(ir_src, encoding="utf-8")
        subprocess.run(
            [
                "rustc",
                tc_nightly_nocore,
                "--target",
                "riscv64gc-unknown-linux-gnu",
                "--crate-type=lib",
                "--emit=llvm-ir",
                ir_rs,
                "-o",
                ir_ll,
            ],
            check=True,
        )
        ir_lines = [
            l.strip() for l in Path(ir_ll).read_text(encoding="utf-8").splitlines() if "call void asm" in l
        ]

        fcsr_src = r'''#![no_std]
#![no_main]
use core::arch::asm;
use core::panic::PanicInfo;
#[panic_handler] fn panic(_: &PanicInfo) -> ! { loop {} }

#[unsafe(no_mangle)] #[inline(never)]
pub unsafe extern "C" fn frm_before_sinks_into_rup(a: f64, b: f64, out_old: *mut u64) -> u64 {
    let sum_before = a + b;
    let old: u64;
    unsafe {
        asm!("fsrmi {old}, 3", old = out(reg) old);
        *out_old = old;
    }
    sum_before.to_bits()
}

#[unsafe(no_mangle)] #[inline(never)]
pub unsafe extern "C" fn frm_between_escapes_rup(a: f64, b: f64) -> u64 {
    let old: u64;
    unsafe { asm!("fsrmi {old}, 3", old = out(reg) old); }
    let sum_rup = a + b;
    unsafe { asm!("fsrm {old}", old = in(reg) old); }
    sum_rup.to_bits()
}

#[unsafe(no_mangle)] #[inline(never)]
pub unsafe extern "C" fn fflags_and_rvv_under_preserves(one: f64, zero: f64) -> (u64, u64, u64) {
    unsafe { asm!("fsflagsi 0", options(nomem, nostack)); }
    let _tmp: f64;
    unsafe {
        asm!(
            "fdiv.d {dst}, {a}, {b}",
            dst = out(freg) _tmp, a = in(freg) one, b = in(freg) zero,
            options(nomem, nostack, preserves_flags)
        );
    }
    let fflags: u64;
    unsafe { asm!("frflags {f}", f = out(reg) fflags, options(nomem, nostack)); }

    unsafe {
        asm!(
            ".option push", ".option arch, +v",
            "vsetivli zero, 2, e64, m1, ta, ma",
            "csrwi vxsat, 0",
            ".option pop",
            options(nomem, nostack)
        );
        asm!(
            ".option push", ".option arch, +v",
            "vsetivli zero, 1, e8, m1, ta, ma",
            "csrwi vxsat, 1",
            ".option pop",
            options(nomem, nostack, preserves_flags)
        );
    }
    let vl_after: u64;
    let vxsat_after: u64;
    unsafe {
        asm!(
            ".option push", ".option arch, +v",
            "csrr {vl}, vl",
            "csrr {vx}, vxsat",
            ".option pop",
            vl = out(reg) vl_after, vx = out(reg) vxsat_after,
            options(nomem, nostack)
        );
    }
    (fflags, vl_after, vxsat_after)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    let a = 1.0_f64;
    let b = f64::from_bits(0x39b0_0000_0000_0000);
    let mut saved = 0u64;
    let before_bits = unsafe { frm_before_sinks_into_rup(a, b, &raw mut saved) };
    unsafe { asm!("fsrm {old}", old = in(reg) saved); }
    let between_bits = unsafe { frm_between_escapes_rup(a, b) };
    let (fflags, vl_after, vxsat_after) = unsafe { fflags_and_rvv_under_preserves(1.0, 0.0) };

    let ok = (before_bits == 0x3ff0_0000_0000_0001)
        && (between_bits == 0x3ff0_0000_0000_0000)
        && ((fflags & 0x08) == 0x08)
        && (vl_after == 1)
        && (vxsat_after == 1);
    unsafe {
        asm!("ecall", in("a7") 93usize, in("a0") if ok { 0usize } else { 77usize }, options(noreturn));
    }
}
'''
        fr_rs = os.path.join(td, "fcsr.rs")
        fr_elf = os.path.join(td, "fcsr.elf")
        Path(fr_rs).write_text(fcsr_src, encoding="utf-8")
        subprocess.run(
            [
                "rustc",
                tc_rv,
                "--target",
                "riscv64gc-unknown-linux-gnu",
                "-A",
                "improper_ctypes_definitions",
                "-C",
                "opt-level=2",
                "-C",
                "panic=abort",
                "-C",
                "relocation-model=static",
                "-C",
                f"linker={lld_21}",
                "-C",
                "linker-flavor=ld.lld",
                "-C",
                "link-arg=-e_start",
                fr_rs,
                "-o",
                fr_elf,
            ],
            check=True,
        )
        fcsr_rvv_rc = subprocess.run(
            [qemu, "-cpu", "rv64,v=true,vlen=128,elen=64", fr_elf], capture_output=True
        ).returncode

        # 4-linker STT_TLS PIE + static matrix
        tls_def_s = r'''
.section .tdata,"awT",@progbits
.balign 8
.space 0x30
.globl c_tls_var
.type c_tls_var, @tls_object
.size c_tls_var, 8
c_tls_var:
    .quad 0x1122334455667788
'''
        pie_use_rs = r'''#![no_std]
#![no_main]
use core::arch::asm;
use core::panic::PanicInfo;
#[panic_handler] fn panic(_: &PanicInfo) -> ! { loop {} }

unsafe extern "C" {
    static c_tls_var: u64;
    static __ehdr_start: u8;
    static _DYNAMIC: [u64; 2];
}

#[repr(C)]
struct Elf64Rela { r_offset: u64, r_info: u64, r_addend: i64 }

unsafe fn apply_pie_relocs(base: usize, dyn_ptr: *const u64) {
    let (mut rela_addr, mut rela_sz, mut i) = (0usize, 0usize, 0usize);
    loop {
        let tag = unsafe { *dyn_ptr.add(i) };
        if tag == 0 { break; }
        let val = unsafe { *dyn_ptr.add(i + 1) } as usize;
        if tag == 7 { rela_addr = base + val; }
        else if tag == 8 { rela_sz = val; }
        i += 2;
    }
    let count = rela_sz / core::mem::size_of::<Elf64Rela>();
    let entries = rela_addr as *const Elf64Rela;
    for k in 0..count {
        let r = unsafe { &*entries.add(k) };
        if (r.r_info & 0xffff_ffff) == 3 {
            let slot = (base + r.r_offset as usize) as *mut u64;
            unsafe { *slot = (base as i64 + r.r_addend) as u64; }
        }
    }
}

fn write_hex(mut v: u64) {
    let mut buf = [0u8; 17];
    for i in (0..16).rev() {
        let d = (v & 0xf) as u8;
        buf[i] = if d < 10 { b'0' + d } else { b'a' + (d - 10) };
        v >>= 4;
    }
    buf[16] = b'\n';
    unsafe {
        asm!("ecall", in("a7") 64usize, in("a0") 1usize, in("a1") buf.as_ptr(), in("a2") 17usize, lateout("a0") _);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    let (base, dyn_p): (usize, *const u64);
    unsafe {
        asm!(
            ".option push", ".option norelax",
            "lla {b}, __ehdr_start", "lla {d}, _DYNAMIC",
            ".option pop",
            b = out(reg) base, d = out(reg) dyn_p,
        );
        apply_pie_relocs(base, dyn_p);
    }
    let v = unsafe { core::ptr::read_volatile(&raw const c_tls_var) };
    write_hex(v);
    unsafe { asm!("ecall", in("a7") 93usize, in("a0") 0usize, options(noreturn)); }
}
'''
        tls_s = os.path.join(td, "tls_def.s")
        tls_def_o = os.path.join(td, "tls_def.o")
        Path(tls_s).write_text(tls_def_s, encoding="utf-8")
        subprocess.run(
            [
                "llvm-mc",
                "--triple=riscv64-unknown-linux-gnu",
                "-mattr=+m,+a,+f,+d,+c",
                "-target-abi=lp64d",
                "-filetype=obj",
                tls_s,
                "-o",
                tls_def_o,
            ],
            check=True,
        )

        pie_rs = os.path.join(td, "pie_use.rs")
        pie_o = os.path.join(td, "pie_use.o")
        Path(pie_rs).write_text(pie_use_rs, encoding="utf-8")
        subprocess.run(
            [
                "rustc",
                tc_rv,
                "--target",
                "riscv64gc-unknown-linux-gnu",
                "-C",
                "opt-level=2",
                "-C",
                "panic=abort",
                "-C",
                "relocation-model=pic",
                "--emit=obj",
                pie_rs,
                "-o",
                pie_o,
            ],
            check=True,
        )

        linkers: list[tuple[str, list[str]]] = [
            ("rust_lld_21.1.8", [lld_21, "-flavor", "gnu", "-m", "elf64lriscv"]),
            ("rust_lld_23.1.1", [lld_23_1, "-flavor", "gnu", "-m", "elf64lriscv"]),
            ("rust_lld_23.1.5", [lld_23_5, "-flavor", "gnu", "-m", "elf64lriscv"]),
        ]
        if mold:
            linkers.append(("mold_2.42.1", [mold, "-m", "elf64lriscv"]))

        stt_tls_pie: dict[str, Any] = {}
        for lname, lcmd in linkers:
            elf_p = os.path.join(td, f"tls_pie_{lname}.elf")
            rl = subprocess.run(
                lcmd + ["-pie", "-e", "_start", pie_o, tls_def_o, "-o", elf_p],
                capture_output=True,
                text=True,
            )
            hdr_word = struct.unpack_from("<Q", Path(elf_p).read_bytes(), 0x30)[0]
            qt = subprocess.run([qemu, elf_p], capture_output=True, text=True)
            stt_tls_pie[lname] = {
                "link_returncode": rl.returncode,
                "qemu_returncode": qt.returncode,
                "stdout_hex": qt.stdout.strip(),
                "elf_header_0x30_word_hex": f"{hdr_word:016x}",
            }

    return {
        "nightly_1_102_llvm_ir_constraints": ir_lines,
        "live_fcsr_frm_inversion_and_rvv_preserves_flags_rc": fcsr_rvv_rc,
        "stt_tls_pie_matrix": stt_tls_pie,
    }


def main() -> None:
    tc_rv = os.environ.get("RV_TOOLCHAIN", "+nightly-2026-01-25")
    tc_1991 = os.environ.get("STABLE_1991_TOOLCHAIN", "+1.99.1")
    tc_1102 = os.environ.get("NIGHTLY_1102_TOOLCHAIN", "+nightly-2026-11-12")

    lld_21 = _rust_lld(tc_rv)
    lld_23_1 = _rust_lld(tc_1991)
    lld_23_5 = _rust_lld(tc_1102)
    mold = shutil.which("ld.mold")
    qemu = shutil.which("qemu-riscv64") or "/usr/bin/qemu-riscv64"

    results = {
        "relax_and_shf_exclude": probe_sysroot_and_relax_shf_exclude(
            tc_rv, lld_21, lld_23_5, mold, qemu
        ),
        "rvc_gadgets_and_cgu": probe_rvc_gadgets_and_cgu_hazards(tc_rv, lld_21, qemu),
        "preserves_flags_rvv_and_stt_tls": probe_preserves_flags_rvv_and_stt_tls(
            tc_rv, tc_1102, lld_21, lld_23_1, lld_23_5, mold, qemu
        ),
    }

    out_path = Path(__file__).resolve().parent / "probe_riscv64_results.json"
    out_path.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote {out_path.name} ({out_path.stat().st_size} bytes)")
    assert results["relax_and_shf_exclude"]["link_outcomes"]["lld23_relax"]["qemu_rc"] == 0
    assert results["rvc_gadgets_and_cgu"]["live_qemu_gadgets_and_half11_ret_swallow_rc"] == 0
    assert results["preserves_flags_rvv_and_stt_tls"]["live_fcsr_frm_inversion_and_rvv_preserves_flags_rc"] == 0


if __name__ == "__main__":
    main()
