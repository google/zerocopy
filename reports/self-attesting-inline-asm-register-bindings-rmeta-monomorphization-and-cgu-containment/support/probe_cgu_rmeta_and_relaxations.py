#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Standalone probe for CGU pure-Rust sibling containment, cross-crate .rmeta hijacks, and post-link relaxations."""

from __future__ import annotations

import argparse
import glob
import hashlib
import json
import os
import shutil
import struct
import subprocess
import tempfile
from pathlib import Path
from typing import Any

from probe_self_attesting_and_invariance import parse_elf64_reloc, run_cmd


def run_cgu_containment_suite(td: str, toolchains: list[str]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for tc in toolchains:
        tcs = tc.replace(".", "_")
        # 1. Three-way streamer split on `global_asm!(".macro xorq ...")` vs pure-Rust `x ^ y` (`10 ^ 3 == 9`)
        ps_ias = os.path.join(td, f"ias_{tcs}.rs")
        Path(ps_ias).write_text(
            'core::arch::global_asm!(".macro xorq a, b\\nsubq \\\\a, \\\\b\\n.endm");\n'
            '#[no_mangle] pub extern "C" fn pure_xor(x: u64, y: u64) -> u64 { x ^ y }\n'
        )
        oo_ias = os.path.join(td, f"ias_{tcs}.o")
        ss_ias = os.path.join(td, f"ias_{tcs}.s")
        os_ias = os.path.join(td, f"ias_{tcs}_from_s.o")
        run_cmd(["rustc", f"+{tc}", "--crate-name=ias", "--crate-type=lib", "-O", "-C", "codegen-units=1", "--emit=obj", ps_ias, "-o", oo_ias])
        run_cmd(["rustc", f"+{tc}", "--crate-name=ias", "--crate-type=lib", "-O", "-C", "codegen-units=1", "--emit=asm", ps_ias, "-o", ss_ias])
        Path(ss_ias).write_text("\n".join(l for l in Path(ss_ias).read_text().splitlines() if not l.strip().startswith(".prefalign")))
        run_cmd(["llvm-mc", "--filetype=obj", "--triple=x86_64-unknown-linux-gnu", ss_ias, "-o", os_ias])

        ps_noia = os.path.join(td, f"noia_{tcs}.rs")
        Path(ps_noia).write_text(
            '#[allow(bad_asm_style)]\n'
            'mod m { core::arch::global_asm!(".att_syntax\\n.macro xorq src, dst\\nsubq \\\\src, \\\\dst\\n.endm"); }\n'
            '#[no_mangle] pub extern "C" fn pure_xor(x: u64, y: u64) -> u64 { x ^ y }\n'
        )
        ss_noia = os.path.join(td, f"noia_{tcs}.s")
        os_noia = os.path.join(td, f"noia_{tcs}.o")
        run_cmd(["rustc", f"+{tc}", "--crate-name=noia", "--crate-type=lib", "-O", "-C", "codegen-units=1", "-C", "llvm-args=-no-integrated-as", "--emit=asm", ps_noia, "-o", ss_noia])
        Path(ss_noia).write_text("\n".join(l for l in Path(ss_noia).read_text().splitlines() if not l.strip().startswith(".prefalign")))
        run_cmd(["llvm-mc", "--filetype=obj", "--triple=x86_64-unknown-linux-gnu", ss_noia, "-o", os_noia])

        cdrv = os.path.join(td, "cdrv_xor.c")
        Path(cdrv).write_text(
            '#include <stdio.h>\n#include <stdint.h>\nuint64_t pure_xor(uint64_t, uint64_t);\n'
            'int main(void){ printf("%llu", (unsigned long long)pure_xor(10, 3)); return 0; }\n'
        )
        vals = {}
        for label, obj in [("mc_object_streamer", oo_ias), ("mc_asm_streamer_ias", os_ias), ("mc_asm_streamer_no_ias", os_noia)]:
            exe = obj + ".exe"
            run_cmd(["clang-19", obj, cdrv, "-o", exe])
            vals[label] = int(run_cmd([exe]).stdout.strip())

        # 2. `.code16` / `.code32` in MCObjectStreamer vs MCAsmStreamer (`--emit=asm`)
        mode_switch = {}
        for dname in [".code16", ".code32"]:
            key = dname.lstrip(".")
            pm = os.path.join(td, f"{key}_{tcs}.rs")
            om = os.path.join(td, f"{key}_{tcs}.o")
            sm = os.path.join(td, f"{key}_{tcs}.s")
            Path(pm).write_text(
                f'#[no_mangle] pub unsafe extern "C" fn a_mode() {{ core::arch::asm!("{dname}", options(nomem, nostack)); }}\n'
                '#[no_mangle] pub extern "C" fn z_pure_mul(x: u64, y: u64) -> u64 { x.wrapping_mul(7).wrapping_add(y) }\n'
            )
            run_cmd(["rustc", f"+{tc}", "--crate-name=ms", "--crate-type=lib", "-O", "-C", "codegen-units=1", "--emit=obj", pm, "-o", om])
            run_cmd(["rustc", f"+{tc}", "--crate-name=ms", "--crate-type=lib", "-O", "-C", "codegen-units=1", "--emit=asm", pm, "-o", sm])
            Path(sm).write_text("\n".join(l for l in Path(sm).read_text().splitlines() if not l.strip().startswith(".prefalign")))
            r_asm = run_cmd(["llvm-mc", "--filetype=obj", "--triple=x86_64-unknown-linux-gnu", sm, "-o", om + ".s.o"], check=False)
            cm = os.path.join(td, "cm.c")
            Path(cm).write_text('#include <stdio.h>\n#include <stdint.h>\nuint64_t z_pure_mul(uint64_t, uint64_t);\nint main(void){ printf("%llu", (unsigned long long)z_pure_mul(6, 5)); return 0; }\n')
            run_cmd(["clang-19", om, cm, "-o", om + ".exe"])
            mode_switch[key] = {
                "mc_object_streamer_pure_val": int(run_cmd([om + ".exe"]).stdout.strip()),
                "mc_asm_streamer_rejected_64bit_insn": r_asm.returncode != 0,
            }

        # 3. Live MCObjectStreamer hijacks on pure-Rust functions: `.weak`, `@gnu_indirect_function`, `.symver`
        pw = os.path.join(td, f"weak_ifunc_{tcs}.rs")
        ow = os.path.join(td, f"weak_ifunc_{tcs}.o")
        Path(pw).write_text(
            r'''
#[no_mangle] pub extern "C" fn a_pure_rust_auth() -> u64 { 1 }
#[no_mangle] pub unsafe extern "C" fn z_uncalled_weak() {
    core::arch::asm!(".weak a_pure_rust_auth", options(nomem, nostack));
}
#[no_mangle] pub extern "C" fn hijack_landing() -> u64 { 7777 }
#[no_mangle] pub extern "C" fn a_pure_victim() -> usize { hijack_landing as *const () as usize }
#[no_mangle] pub unsafe extern "C" fn z_uncalled_ifunc() {
    core::arch::asm!(".type a_pure_victim, @gnu_indirect_function", options(nomem, nostack));
}
#[no_mangle] pub unsafe extern "C" fn z_uncalled_symver() {
    core::arch::asm!(".symver hijack_landing, a_pure_symver@@@VER1", options(nomem, nostack));
}
'''
        )
        run_cmd(["rustc", f"+{tc}", "--crate-name=wi", "--crate-type=lib", "-O", "-C", "codegen-units=1", "--emit=obj", pw, "-o", ow])
        elf_wi = parse_elf64_reloc(ow)
        sym_by_name = {s["name"]: s for s in elf_wi["syms"]}
        cw = os.path.join(td, "cw.c")
        Path(cw).write_text(
            '#include <stdio.h>\n#include <stdint.h>\n'
            'uint64_t a_pure_rust_auth(void) { return 999; }\n'
            'uint64_t a_pure_victim(void);\n'
            'int main(void) { printf("%llu,%llu", (unsigned long long)a_pure_rust_auth(), (unsigned long long)a_pure_victim()); return 0; }\n'
        )
        run_cmd(["clang-19", ow, cw, "-o", ow + ".exe"])
        weak_val_s, ifunc_val_s = run_cmd([ow + ".exe"]).stdout.strip().split(",")

        # 4. `.cfi_sections .debug_frame` stripping `.eh_frame` from pure-Rust `catch_unwind`
        pcfi = os.path.join(td, f"cfi_{tcs}.rs")
        ecfi = os.path.join(td, f"cfi_{tcs}.exe")
        ocfi = os.path.join(td, f"cfi_{tcs}.o")
        Path(pcfi).write_text(
            r'''
core::arch::global_asm!(".cfi_sections .debug_frame");
#[inline(never)]
fn pure_rust_panicker(x: u64) -> u64 {
    if x == 0 { panic!("boom"); }
    x
}
fn main() {
    let caught = std::panic::catch_unwind(|| pure_rust_panicker(0)).is_err();
    println!("CAUGHT={}", caught);
}
'''
        )
        run_cmd(["rustc", f"+{tc}", "--crate-name=cfi", "-O", "-C", "codegen-units=1", "--emit=obj", pcfi, "-o", ocfi])
        run_cmd(["rustc", f"+{tc}", "--crate-name=cfi", "-O", "-C", "codegen-units=1", pcfi, "-o", ecfi])
        elf_cfi = parse_elf64_reloc(ocfi)
        cgu_has_eh_frame = any(s["name"] == ".eh_frame" for s in elf_cfi["shdrs"])
        r_cfi = run_cmd([ecfi], check=False)

        # 5. Unbalanced `.section .rodata.trap` (sibling vs inlined caller under `-C force-unwind-tables=no`)
        psec = os.path.join(td, f"sec_{tcs}.rs")
        osec = os.path.join(td, f"sec_{tcs}.o")
        Path(psec).write_text(
            r'''
#[no_mangle] pub unsafe extern "C" fn a_uncalled_sec() {
    core::arch::asm!(".section .rodata.trap,\"a\",@progbits", options(nomem, nostack));
}
#[no_mangle] #[inline(never)]
pub extern "C" fn b_pure_sibling_after_sec(x: u64) -> u64 { x + 42 }
#[inline(always)]
pub unsafe fn inline_sec_gadget() {
    core::arch::asm!(".section .rodata.trap,\"a\",@progbits", options(nomem, nostack));
}
#[no_mangle] #[inline(never)]
pub unsafe extern "C" fn c_caller_of_inline_sec(x: u64) -> u64 {
    inline_sec_gadget();
    x + 99
}
'''
        )
        run_cmd(["rustc", f"+{tc}", "--crate-name=sec", "--crate-type=lib", "-O", "-C", "codegen-units=1", "-C", "force-unwind-tables=no", "-C", "panic=abort", "--emit=obj", psec, "-o", osec])
        elf_sec = parse_elf64_reloc(osec)
        sh_sec = {s["name"]: s["data"].hex() for s in elf_sec["shdrs"]}

        # 6. Trailing bare x86 prefix bytes (`.byte 0x66`, `0x41`, `0xf0`, `0x64`) bleeding into pure Rust
        ppfx = os.path.join(td, f"pfx_{tcs}.rs")
        opfx = os.path.join(td, f"pfx_{tcs}.o")
        Path(ppfx).write_text(
            r'''
#[inline(always)]
unsafe fn pfx_66() {
    core::arch::asm!(
        "9996:\n.byte 0x66\n9997:\n.pushsection .anneal.asm_sites,\"e\",@progbits\n.quad 9996b, 9997b, 1\n.popsection",
        options(nomem, nostack, preserves_flags)
    );
}
#[inline(always)] unsafe fn pfx_41() { core::arch::asm!(".byte 0x41", options(nomem, nostack, preserves_flags)); }
#[inline(always)] unsafe fn pfx_f0() { core::arch::asm!(".byte 0xf0", options(nomem, nostack, preserves_flags)); }
#[inline(always)] unsafe fn pfx_64() { core::arch::asm!(".byte 0x64", options(nomem, nostack, preserves_flags)); }

#[no_mangle] #[inline(never)] pub fn victim_66() -> u32 { unsafe { pfx_66(); } 0x12345678u32 }
#[no_mangle] #[inline(never)] pub fn victim_41() -> u32 { unsafe { pfx_41(); } 0x12345678u32 }
#[no_mangle] #[inline(never)] pub fn victim_f0(x: u64, y: u64) -> u64 { unsafe { pfx_f0(); } x.wrapping_add(y) }
#[no_mangle] #[inline(never)] pub fn victim_64(p: &u64) -> u64 { unsafe { pfx_64(); } *p }
'''
        )
        run_cmd(["rustc", f"+{tc}", "--crate-name=pfx", "--crate-type=lib", "-O", "-C", "codegen-units=1", "--emit=obj", ppfx, "-o", opfx])
        elf_pfx = parse_elf64_reloc(opfx)
        sh_pfx = {s["name"]: s["data"].hex() for s in elf_pfx["shdrs"] if s["name"].startswith(".text.victim_")}

        c66 = os.path.join(td, "c66.c")
        Path(c66).write_text('#include <stdio.h>\n#include <stdint.h>\nuint32_t victim_66(void);\nint main(void){ printf("0x%04x", victim_66() & 0xffffu); return 0; }\n')
        run_cmd(["clang-19", opfx, c66, "-o", opfx + ".66"])
        v66_low16 = run_cmd([opfx + ".66"]).stdout.strip()

        cf0 = os.path.join(td, "cf0.c")
        Path(cf0).write_text('#include <stdint.h>\nuint64_t victim_f0(uint64_t, uint64_t);\nint main(void){ return (int)victim_f0(1, 2); }\n')
        run_cmd(["clang-19", opfx, cf0, "-o", opfx + ".f0"])
        rf0 = run_cmd([opfx + ".f0"], check=False)

        out[tc] = {
            "macro_xorq_streamer_matrix": vals,
            "mode_switch_matrix": mode_switch,
            "mc_object_streamer_symbol_hijacks": {
                "a_pure_rust_auth_elf_bind": sym_by_name["a_pure_rust_auth"]["bind"],  # 2 == STB_WEAK
                "a_pure_rust_auth_runtime_val": int(weak_val_s),
                "a_pure_victim_elf_type": sym_by_name["a_pure_victim"]["type"],  # 10 == STT_GNU_IFUNC
                "a_pure_victim_runtime_val": int(ifunc_val_s),
                "symver_alias_created": "a_pure_symver@@VER1" in sym_by_name,
            },
            "cfi_sections_debug_frame": {
                "cgu_has_eh_frame": cgu_has_eh_frame,
                "catch_unwind_aborted": r_cfi.returncode != 0,
                "exit_code": r_cfi.returncode,
            },
            "unbalanced_section": {
                "sibling_text_hex": sh_sec[".text.b_pure_sibling_after_sec"],
                "inlined_caller_text_hex": sh_sec[".text.c_caller_of_inline_sec"],
                "rodata_trap_hex": sh_sec[".rodata.trap"],
            },
            "trailing_prefix_bleed": {
                "section_hex": sh_pfx,
                "victim_66_corrupted_low16": v66_low16,
                "victim_f0_sigill_rc": rf0.returncode,
            },
        }
    return out


def run_rmeta_and_relaxation_suite(td: str, toolchains: list[str]) -> dict[str, Any]:
    out: dict[str, Any] = {"cross_crate_rmeta": {}, "x86_64_relaxations": {}, "aarch64_thunk_qemu": {}}
    sysroot_0 = run_cmd(["rustc", f"+{toolchains[0]}", "--print", "sysroot"]).stdout.strip()
    rust_lld = glob.glob(sysroot_0 + "/**/rust-lld", recursive=True)[0]
    lld_dir = os.path.join(td, "lld_bin")
    os.makedirs(lld_dir, exist_ok=True)
    os.symlink(rust_lld, os.path.join(lld_dir, "ld.lld"))

    for tc in toolchains:
        tcs = tc.replace(".", "_")
        up_rs = os.path.join(td, f"up_{tcs}.rs")
        up_rlib = os.path.join(td, f"libupstream_{tcs}.rlib")
        Path(up_rs).write_text(
            r'''
pub fn generic_helper<T>(x: u64) -> u64 {
    x.wrapping_add(core::mem::size_of::<T>() as u64)
}
pub unsafe fn generic_sub<T: Copy, const C: i32>(mut a: u64, b: u64) -> u64 {
    let _fn_addr: u64;
    core::arch::asm!(
        "9996:\nsub {0:r}, {1:r}\nadd {0:r}, {c}\nlea {2:r}, [rip + {s}]\n9997:",
        ".pushsection .anneal.asm_descs,\"e\",@progbits\n9998: .asciz \"kind=generic|0={0:r}|1={1:r}|2={2:r}|c={c}\"\n9999: .popsection",
        ".pushsection .anneal.asm_sites,\"e\",@progbits\n.quad 9996b, 9997b, 401, 9998b, 9999b - 9998b, 1, {s}\n.popsection",
        inout(reg) a, in(reg) b, out(reg) _fn_addr, c = const C, s = sym generic_helper::<T>, options(pure, nomem, nostack),
    );
    a
}
#[inline]
pub unsafe fn inline_sub(mut a: u64, b: u64) -> u64 {
    core::arch::asm!(
        "9996:\nsub {0:r}, {1:r}\n9997:\n.pushsection .anneal.asm_descs,\"e\",@progbits\n9998: .asciz \"kind=inline|0={0:r}|1={1:r}\"\n9999: .popsection",
        ".pushsection .anneal.asm_sites,\"e\",@progbits\n.quad 9996b, 9997b, 402, 9998b, 9999b - 9998b, 0\n.popsection",
        inout(reg) a, in(reg) b, options(pure, nomem, nostack),
    );
    a
}
#[inline(always)]
pub unsafe fn inline_always_sub(mut a: u64, b: u64) -> u64 {
    core::arch::asm!(
        "9996:\nsub {0:r}, {1:r}\n9997:\n.pushsection .anneal.asm_descs,\"e\",@progbits\n9998: .asciz \"kind=inline_always|0={0:r}|1={1:r}\"\n9999: .popsection",
        ".pushsection .anneal.asm_sites,\"e\",@progbits\n.quad 9996b, 9997b, 403, 9998b, 9999b - 9998b, 0\n.popsection",
        inout(reg) a, in(reg) b, options(pure, nomem, nostack),
    );
    a
}
pub unsafe fn unannotated_pub_sub(mut a: u64, b: u64) -> u64 {
    core::arch::asm!(
        "9996:\nsub {0:r}, {1:r}\n9997:\n.pushsection .anneal.asm_descs,\"e\",@progbits\n9998: .asciz \"kind=unannotated|0={0:r}|1={1:r}\"\n9999: .popsection",
        ".pushsection .anneal.asm_sites,\"e\",@progbits\n.quad 9996b, 9997b, 404, 9998b, 9999b - 9998b, 0\n.popsection",
        inout(reg) a, in(reg) b, options(pure, nomem, nostack),
    );
    a
}
#[inline(never)]
pub unsafe fn never_inline_sub(mut a: u64, b: u64) -> u64 {
    core::arch::asm!(
        "9996:\nsub {0:r}, {1:r}\n9997:\n.pushsection .anneal.asm_descs,\"e\",@progbits\n9998: .asciz \"kind=never_inline|0={0:r}|1={1:r}\"\n9999: .popsection",
        ".pushsection .anneal.asm_sites,\"e\",@progbits\n.quad 9996b, 9997b, 405, 9998b, 9999b - 9998b, 0\n.popsection",
        inout(reg) a, in(reg) b, options(pure, nomem, nostack),
    );
    a
}
'''
        )
        run_cmd(["rustc", f"+{tc}", "--crate-name=upstream", "--crate-type=rlib", "-C", "opt-level=3", "-C", "codegen-units=1", up_rs, "-o", up_rlib])
        ex_d = os.path.join(td, f"ex_{tcs}")
        os.makedirs(ex_d, exist_ok=True)
        run_cmd(["ar", "x", up_rlib], cwd=ex_d)
        up_descs: list[str] = []
        for of in sorted(glob.glob(os.path.join(ex_d, "*.rcgu.o"))):
            elf_u = parse_elf64_reloc(of)
            sh_u = {s["name"]: s for s in elf_u["shdrs"]}
            if ".anneal.asm_descs" in sh_u:
                up_descs.extend(
                    x.decode("utf-8", errors="replace")
                    for x in sh_u[".anneal.asm_descs"]["data"].split(b"\x00")
                    if x
                )

        dn_rs = os.path.join(td, f"dn_{tcs}.rs")
        dn_exe = os.path.join(td, f"dn_{tcs}.exe")
        dn_obj = os.path.join(td, f"dn_{tcs}.o")
        Path(dn_rs).write_text(
            r'''
extern crate upstream;
core::arch::global_asm!(".macro sub dst, src\nadd \\dst, \\src\n.endm");
fn main() {
    let a = std::hint::black_box(20u64);
    let b = std::hint::black_box(5u64);
    let res = unsafe { (
        upstream::generic_sub::<u32, 0>(a, b),
        upstream::inline_sub(a, b),
        upstream::inline_always_sub(a, b),
        upstream::unannotated_pub_sub(a, b),
        upstream::never_inline_sub(a, b),
    ) };
    println!("{},{},{},{},{}", res.0, res.1, res.2, res.3, res.4);
}
'''
        )
        run_cmd(["rustc", f"+{tc}", "--crate-name=downstream", "-C", "opt-level=3", "-C", "codegen-units=1", "--extern", f"upstream={up_rlib}", dn_rs, "-o", dn_exe])
        run_cmd(["rustc", f"+{tc}", "--crate-name=downstream", "-C", "opt-level=3", "-C", "codegen-units=1", "--extern", f"upstream={up_rlib}", "--emit=obj", dn_rs, "-o", dn_obj])
        vals_dn = [int(x) for x in run_cmd([dn_exe]).stdout.strip().split(",")]

        elf_dn = parse_elf64_reloc(dn_obj)
        sh_dn = {s["name"]: s for s in elf_dn["shdrs"]}
        s_dn, d_dn = sh_dn[".anneal.asm_sites"], sh_dn[".anneal.asm_descs"]
        rel_dn = {r["r_offset"]: r for r in elf_dn["relas"][s_dn["idx"]]}
        dn_caught = 0
        dn_total = 0
        off = 0
        while off < s_dn["size"]:
            _, _, _sid, _, _dlen, n_tgt = struct.unpack_from("<QQQQQQ", s_dn["data"], off)
            rs, re_ = rel_dn[off], rel_dn[off + 8]
            so, eo = rs["sym_value"] + rs["r_addend"], re_["sym_value"] + re_["r_addend"]
            cbytes = elf_dn["shdrs"][rs["sym_shndx"]]["data"][so:eo]
            dn_total += 1
            if cbytes[1] == 0x01:  # ADD r/m64, r64 (`0x01`) instead of SUB (`0x29`)
                dn_caught += 1
            off += 48 + n_tgt * 8

        out["cross_crate_rmeta"][tc] = {
            "upstream_rlib_descs": up_descs,
            "downstream_runtime_20_minus_5": {
                "generic_sub": vals_dn[0],
                "inline_sub": vals_dn[1],
                "inline_always_sub": vals_dn[2],
                "unannotated_pub_sub": vals_dn[3],
                "never_inline_sub": vals_dn[4],
            },
            "downstream_attested_sites_total": dn_total,
            "downstream_hijacked_sites_caught_by_opcode_mismatch": dn_caught,
        }

        # 4B. x86-64 GOTPCREL (type 9) vs REX_GOTPCRELX (type 42) and GOTTPOFF (%rax vs %r12)
        rel_rs = os.path.join(td, f"rlx_{tcs}.rs")
        Path(rel_rs).write_text(
            r'''
core::arch::global_asm!(
    ".section .tdata,\"awT\",@progbits\n.globl my_tls_slot\n.type my_tls_slot,@object\n.p2align 3\nmy_tls_slot:\n.quad 0x1234\n.size my_tls_slot, 8"
);
unsafe extern "C" { static EXT_DATA: u64; }
#[no_mangle] #[inline(never)]
pub unsafe extern "C" fn test_got(x: u64, y: u64) -> u64 {
    let cond = x == y;
    let addr: u64;
    core::arch::asm!(
        "mov {0:r}, qword ptr [rip + {s}@GOTPCREL]",
        out(reg) addr, s = sym EXT_DATA, options(pure, readonly, nostack, preserves_flags),
    );
    if cond { unsafe { *(addr as *const u64) } } else { 999 }
}
#[no_mangle] #[inline(never)]
pub unsafe extern "C" fn test_gottpoff_rax() -> u64 {
    let zf: u8; let tp: u64 = 0;
    core::arch::asm!("xor eax, eax\nadd rax, qword ptr [rip + my_tls_slot@GOTTPOFF]\nsete {zf}", inout("rax") tp => _, zf = out(reg_byte) zf, options(nostack));
    zf as u64
}
#[no_mangle] #[inline(never)]
pub unsafe extern "C" fn test_gottpoff_r12() -> u64 {
    let zf: u8; let tp: u64 = 0;
    core::arch::asm!("xor eax, eax\nadd r12, qword ptr [rip + my_tls_slot@GOTTPOFF]\nsete {zf}", inout("r12") tp => _, out("eax") _, zf = out(reg_byte) zf, options(nostack));
    zf as u64
}
'''
        )
        crlx = os.path.join(td, "crlx.c")
        Path(crlx).write_text(
            '#include <stdio.h>\n#include <stdint.h>\nuint64_t EXT_DATA = 0xfeedfaceULL;\n'
            'uint64_t test_got(uint64_t,uint64_t); uint64_t test_gottpoff_rax(void); uint64_t test_gottpoff_r12(void);\n'
            'int main(void){ printf("0x%llx,%llu,%llu", (unsigned long long)test_got(7,7), (unsigned long long)test_gottpoff_rax(), (unsigned long long)test_gottpoff_r12()); return 0; }\n'
        )
        is_nightly = "nightly" in run_cmd(["rustc", f"+{tc}", "-vV"]).stdout
        modes_list = [("default_gotpcrel", [])]
        if is_nightly:
            modes_list.append(("relax_elf_relocs_rex_gotpcrelx", ["-Z", "relax-elf-relocations=yes"]))
        rlx_modes: dict[str, Any] = {}
        for rmode, rustc_extra in modes_list:
            ro = os.path.join(td, f"rlx_{tcs}_{rmode}.o")
            run_cmd(["rustc", f"+{tc}", "--crate-name=rlx", "--crate-type=lib", "-O", "-C", "relocation-model=pic", *rustc_extra, "--emit=obj", rel_rs, "-o", ro])
            elf_ro = parse_elf64_reloc(ro)
            sh_ro = {s["name"]: s for s in elf_ro["shdrs"]}
            got_rtype = elf_ro["relas"][sh_ro[".text.test_got"]["idx"]][0]["r_type"]
            lkr_res = {"prelink_got_reloc_type": got_rtype}
            for lkr_name, lkr_flags in [
                ("rust_lld_pie", [f"-B{lld_dir}", "-fuse-ld=lld", "-pie", "-fPIE"]),
                ("rust_lld_pie_norelax", [f"-B{lld_dir}", "-fuse-ld=lld", "-pie", "-fPIE", "-Wl,--no-relax"]),
                ("ld_bfd_pie", ["-fuse-ld=bfd", "-pie", "-fPIE"]),
                ("ld_bfd_pie_norelax", ["-fuse-ld=bfd", "-pie", "-fPIE", "-Wl,--no-relax"]),
            ]:
                exe = ro + f".{lkr_name}"
                run_cmd(["clang-19", *lkr_flags, ro, crlx, "-o", exe])
                got_s, zf_rax_s, zf_r12_s = run_cmd([exe]).stdout.strip().split(",")
                dis_got = run_cmd(["llvm-objdump", "-d", "--disassemble-symbols=test_got", exe]).stdout
                relaxed_got_to_lea = "\tleaq\t" in dis_got
                lkr_res[lkr_name] = {
                    "got_relaxed_to_lea": relaxed_got_to_lea,
                    "got_val": got_s,
                    "zf_rax": int(zf_rax_s),
                    "zf_r12": int(zf_r12_s),
                }
            rlx_modes[rmode] = lkr_res
        out["x86_64_relaxations"][tc] = rlx_modes

    # 4C. AArch64 >128 MiB Range-Extension Thunk (`x16` clobber!) on `/usr/bin/qemu-aarch64`
    targets_199 = run_cmd(["rustup", "target", "list", "--installed", "--toolchain", "1.99.1"]).stdout.splitlines()
    qemu = shutil.which("qemu-aarch64")
    if "aarch64-unknown-linux-gnu" in targets_199 and qemu:
        a64_rs = os.path.join(td, "a64_thunk.rs")
        a64_o = os.path.join(td, "a64_thunk.o")
        Path(a64_rs).write_text(
            r'''#![no_std]
#![no_main]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
core::arch::global_asm!(
    ".section .text.far,\"ax\",@progbits\n.globl far_leaf_helper\n.type far_leaf_helper,@function\nfar_leaf_helper:\nadd x0, x0, #42\nret\n.size far_leaf_helper, .-far_leaf_helper"
);
unsafe extern "C" { fn far_leaf_helper(); }
#[no_mangle] #[inline(never)]
pub unsafe extern "C" fn caller_holding_x16(input: u64) -> (u64, u64) {
    let mut val = input;
    let mut live_x16: u64 = 0x1122_3344_5566_7788;
    core::arch::asm!("nop", inout("x16") live_x16, options(nomem, nostack, preserves_flags));
    core::arch::asm!(
        "9996:\nbl {callee}\n9997:\n.pushsection .anneal.asm_sites,\"e\",@progbits\n.xword 9996b, 9997b, 701, {callee}\n.popsection",
        inout("x0") val, out("x30") _, callee = sym far_leaf_helper, options(nomem, nostack, preserves_flags),
    );
    core::arch::asm!("nop", inout("x16") live_x16, options(nomem, nostack, preserves_flags));
    (val, live_x16)
}
#[no_mangle]
pub unsafe extern "C" fn _start() -> ! {
    let (res, x16_after) = caller_holding_x16(100);
    let mut out = [0u8; 42];
    let hex = b"0123456789abcdef";
    out[0..4].copy_from_slice(b"VAL=");
    let mut i = 0;
    while i < 16 { out[4 + i] = hex[((res >> ((15 - i) * 4)) & 0xf) as usize]; i += 1; }
    out[20..25].copy_from_slice(b" X16=");
    let mut k = 0;
    while k < 16 { out[25 + k] = hex[((x16_after >> ((15 - k) * 4)) & 0xf) as usize]; k += 1; }
    out[41] = b'\n';
    core::arch::asm!("mov x8, #64\nmov x0, #1\nsvc #0", in("x1") out.as_ptr(), in("x2") out.len(), out("x8") _, out("x0") _, options(nostack));
    let code: u64 = if x16_after == 0x1122_3344_5566_7788 { 0 } else { 42 };
    core::arch::asm!("mov x8, #93\nsvc #0", in("x0") code, options(noreturn));
}
'''
        )
        run_cmd(["rustc", "+1.99.1", "--target", "aarch64-unknown-linux-gnu", "--crate-name=a64t", "-C", "opt-level=3", "-C", "codegen-units=1", "-C", "panic=abort", "--emit=obj", a64_rs, "-o", a64_o])
        near_elf, far_elf = os.path.join(td, "near.elf"), os.path.join(td, "far.elf")
        lds = os.path.join(td, "far.lds")
        Path(lds).write_text("SECTIONS {\n  . = 0x200000;\n  .text : { *(.text) *(.text.caller_holding_x16) *(.text._start) }\n  . = 0x10000000;\n  .text.far : { *(.text.far) }\n}\n")
        run_cmd([rust_lld, "-flavor", "gnu", "-m", "aarch64linux", "--image-base=0x200000", a64_o, "-o", near_elf])
        run_cmd([rust_lld, "-flavor", "gnu", "-m", "aarch64linux", "-T", lds, a64_o, "-o", far_elf])
        r_near = run_cmd([qemu, near_elf], check=False)
        r_far = run_cmd([qemu, far_elf], check=False)
        out["aarch64_thunk_qemu"] = {
            "shared_object_sha256_16": hashlib.sha256(Path(a64_o).read_bytes()).hexdigest()[:16],
            "near_lt_128mib": {"exit_code": r_near.returncode, "output": r_near.stdout.strip()},
            "far_gt_128mib": {"exit_code": r_far.returncode, "output": r_far.stdout.strip()},
        }
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchains", nargs="+", default=["1.99.1", "nightly"])
    parser.add_argument("--out", default="")
    args = parser.parse_args()

    with tempfile.TemporaryDirectory() as td:
        payload = {
            "probe_3_cgu_pure_rust_containment": run_cgu_containment_suite(td, args.toolchains),
            "probe_4_rmeta_and_postlink_relaxations": run_rmeta_and_relaxation_suite(td, args.toolchains),
        }
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
