#!/usr/bin/env python3
"""Reproduce AArch64 inline-asm, SVE/PCS clobber, PAC/MTE/TBI0, STT_TLS, and outlined-atomics probes."""

from __future__ import annotations

import glob
import json
import os
import shutil
import struct
import subprocess
import tempfile
from pathlib import Path
from typing import Any


def run_cmd(cmd: list[str], input_bytes: bytes | None = None) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(cmd, input=input_bytes, capture_output=True)


def parse_kv_lines(text: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for line in text.splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            out[k.strip()] = v.strip()
    return out


def rustc_sysroot(tc: str) -> Path:
    r = subprocess.run(["rustc", tc, "--print", "sysroot"], text=True, capture_output=True, check=True)
    return Path(r.stdout.strip())


def rustc_version_info(tc: str) -> dict[str, str]:
    r = subprocess.run(["rustc", tc, "-vV"], text=True, capture_output=True, check=True)
    info: dict[str, str] = {}
    for idx, line in enumerate(r.stdout.strip().splitlines()):
        if idx == 0:
            info["headline"] = line
        elif ":" in line:
            k, v = line.split(":", 1)
            info[k.strip()] = v.strip()
    return info


def probe_asm_feature_matrix(toolchains: list[str]) -> dict[str, Any]:
    cases: dict[str, tuple[str, tuple[str, ...]]] = {
        "baseline_out_z0_clobber": (
            '#![no_std]\n#[unsafe(no_mangle)] pub unsafe fn f() { core::arch::asm!("nop", out("z0") _); }',
            (),
        ),
        "baseline_out_z0_typed_u64": (
            '#![no_std]\n#[unsafe(no_mangle)] pub unsafe fn f() -> u64 { let y: u64; core::arch::asm!("movi v0.2d, #0", out("z0") y); y }',
            (),
        ),
        "baseline_z0_modifier_z": (
            '#![no_std]\n#[unsafe(no_mangle)] pub unsafe fn f() -> u64 { let y: u64; core::arch::asm!("nop // {:z}", out(vreg) y); y }',
            (),
        ),
        "baseline_out_p0_ffr_clobber": (
            '#![no_std]\n#[unsafe(no_mangle)] pub unsafe fn f() { core::arch::asm!("nop", out("p0") _, out("ffr") _); }',
            (),
        ),
        "sve_out_p0_typed": (
            '#![no_std]\n#[target_feature(enable = "sve")]\n#[unsafe(no_mangle)] pub unsafe fn f() -> u16 { let y: u16; core::arch::asm!("nop", out("p0") y); y }',
            (),
        ),
        "baseline_raw_sve_no_directive": (
            '#![no_std]\n#[unsafe(no_mangle)] pub unsafe fn f() -> u64 { let mut x = 0u64; core::arch::asm!("incb {0}", inout(reg) x); x }',
            (),
        ),
        "baseline_raw_sve_arch_extension": (
            '#![no_std]\n#[unsafe(no_mangle)] pub unsafe fn f() -> u64 { let mut x = 0u64; core::arch::asm!(".arch_extension sve\\n incb {0}\\n ptrue p0.b\\n dup z0.d, #1", inout(reg) x, out("z0") _, out("p0") _); x }',
            (),
        ),
        "baseline_raw_sme_arch_extension": (
            '#![no_std]\n#[unsafe(no_mangle)] pub unsafe fn f() { core::arch::asm!(".arch_extension sme\\n smstart\\n smstop", out("z0") _); }',
            (),
        ),
        "baseline_raw_pac_no_directive": (
            '#![no_std]\n#[unsafe(no_mangle)] pub unsafe fn f(mut p: u64, m: u64) -> u64 { core::arch::asm!("pacia {0}, {1}", inout(reg) p, in(reg) m); p }',
            (),
        ),
        "baseline_raw_pac_arch_extension": (
            '#![no_std]\n#[unsafe(no_mangle)] pub unsafe fn f(mut p: u64, m: u64) -> u64 { core::arch::asm!(".arch_extension pauth\\n pacia {0}, {1}\\n autia {0}, {1}", inout(reg) p, in(reg) m); p }',
            (),
        ),
        "baseline_pac_hint_space": (
            '#![no_std]\n#[unsafe(no_mangle)] pub unsafe fn f() { core::arch::asm!("paciasp\\n autiasp"); }',
            (),
        ),
        "preserves_flags_omitted_vs_enabled": (
            '#![no_std]\n#[unsafe(no_mangle)] pub unsafe fn f_def() { core::arch::asm!("nop"); }\n#[unsafe(no_mangle)] pub unsafe fn f_pres() { core::arch::asm!("nop", options(preserves_flags)); }',
            (),
        ),
    }

    results: dict[str, Any] = {}
    for tc in toolchains:
        tc_res: dict[str, Any] = {}
        for name, (code, extra_flags) in cases.items():
            with tempfile.TemporaryDirectory() as tmp:
                src = os.path.join(tmp, "lib.rs")
                with open(src, "w", encoding="utf-8") as f:
                    f.write(code)
                cmd = [
                    "rustc",
                    tc,
                    "--target",
                    "aarch64-unknown-linux-gnu",
                    "--crate-type=lib",
                    "-O",
                    "--emit=llvm-ir,obj",
                    "--out-dir",
                    tmp,
                    *extra_flags,
                    src,
                ]
                r = subprocess.run(cmd, text=True, capture_output=True)
                ir_calls: list[str] = []
                for ll_file in glob.glob(os.path.join(tmp, "*.ll")):
                    with open(ll_file, encoding="utf-8") as lf:
                        for line in lf:
                            if "asm " in line:
                                ir_calls.append(line.strip())
                errs = [
                    line.strip()
                    for line in r.stderr.splitlines()
                    if line.strip().startswith("error")
                ]
                tc_res[name] = {
                    "returncode": r.returncode,
                    "errors": errs,
                    "llvm_ir_asm_calls": ir_calls,
                }
        results[tc] = tc_res
    return results


def probe_sve_pcs_and_flags(qemu_bin: str) -> dict[str, Any]:
    rust_src = """#![no_std]
#![no_main]
#![feature(stdarch_aarch64_sve, naked_functions_target_feature)]
#![allow(improper_ctypes_definitions)]

use core::arch::asm;
use core::arch::aarch64::*;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

unsafe fn write_bytes(buf: &[u8]) {
    asm!(
        "mov x8, #64\\n svc #0",
        in("x0") 1usize, in("x1") buf.as_ptr(), in("x2") buf.len(),
        lateout("x0") _, out("x8") _, options(nostack)
    );
}

unsafe fn write_hex_u64(label: &[u8], val: u64) {
    write_bytes(label);
    let mut out = [0u8; 19];
    out[0] = b'0'; out[1] = b'x';
    let hex = b"0123456789abcdef";
    let mut i = 0;
    while i < 16 {
        out[2 + i] = hex[((val >> ((15 - i) * 4)) & 0xf) as usize];
        i += 1;
    }
    out[18] = b'\\n';
    write_bytes(&out);
}

#[inline(never)]
#[target_feature(enable = "sve")]
pub unsafe fn test_sve_spill_across_all_z_clobbers(input: &[u64; 8], out_buf: &mut [u64; 8]) {
    let pg = svptrue_b64();
    let v = svld1_u64(pg, input.as_ptr());
    asm!(
        "dup z0.d, #-1",
        "dup z8.d, #-1",
        out("z0") _, out("z1") _, out("z2") _, out("z3") _,
        out("z4") _, out("z5") _, out("z6") _, out("z7") _,
        out("z8") _, out("z9") _, out("z10") _, out("z11") _,
        out("z12") _, out("z13") _, out("z14") _, out("z15") _,
        out("z16") _, out("z17") _, out("z18") _, out("z19") _,
        out("z20") _, out("z21") _, out("z22") _, out("z23") _,
        out("z24") _, out("z25") _, out("z26") _, out("z27") _,
        out("z28") _, out("z29") _, out("z30") _, out("z31") _,
        out("p0") _, out("p1") _, out("p2") _, out("p3") _,
        out("p4") _, out("p5") _, out("p6") _, out("p7") _,
    );
    svst1_u64(pg, out_buf.as_mut_ptr(), v);
}

#[inline(never)]
#[target_feature(enable = "sve")]
pub unsafe extern "C" fn compiler_sve_pcs_callee(x: svuint64_t, ptr: *const u64) -> svuint64_t {
    let pg = svptrue_b64();
    let a = svld1_u64(pg, ptr);
    asm!("dup z8.d, #0x55", out("z8") _, out("z9") _, out("p4") _);
    svadd_u64_x(pg, x, a)
}

#[inline(never)]
#[target_feature(enable = "sve")]
pub unsafe extern "C" fn compiler_base_pcs_callee(ptr: *const u64) -> u64 {
    let pg = svptrue_b64();
    let a = svld1_u64(pg, ptr);
    asm!("dup z8.d, #0x55", out("z8") _, out("p4") _);
    svaddv_u64(pg, a)
}

#[unsafe(naked)]
#[target_feature(enable = "sve")]
unsafe extern "C" fn buggy_d8_only_sve_callee(x: svuint64_t) -> svuint64_t {
    core::arch::naked_asm!(
        "str d8, [sp, #-16]!",
        "dup z8.d, #0x55",
        "ldr d8, [sp], #16",
        "ret",
    );
}

#[inline(never)]
#[target_feature(enable = "sve")]
unsafe fn test_sve_pcs_z8_partial_save_corruption(input: &[u64; 8], out_buf: &mut [u64; 8]) {
    asm!(
        "ptrue p0.d",
        "ld1d {{z8.d}}, p0/z, [{inp}]",
        "bl {callee}",
        "ptrue p0.d",
        "st1d {{z8.d}}, p0, [{outp}]",
        inp = in(reg) input.as_ptr(),
        outp = in(reg) out_buf.as_mut_ptr(),
        callee = sym buggy_d8_only_sve_callee,
        out("z0") _, out("p0") _, out("x30") _,
    );
}

#[inline(never)]
#[target_feature(enable = "sve")]
unsafe fn test_compiler_base_pcs_callee_on_z8(input: &[u64; 8], out_buf: &mut [u64; 8]) {
    asm!(
        "ptrue p0.d",
        "ld1d {{z8.d}}, p0/z, [{inp}]",
        "mov x0, {inp}",
        "bl {callee}",
        "ptrue p0.d",
        "st1d {{z8.d}}, p0, [{outp}]",
        inp = in(reg) input.as_ptr(),
        outp = in(reg) out_buf.as_mut_ptr(),
        callee = sym compiler_base_pcs_callee,
        out("x0") _, out("x1") _, out("x2") _, out("x3") _,
        out("v0") _, out("v1") _, out("p0") _, out("p4") _, out("x30") _,
    );
}

#[inline(never)]
#[target_feature(enable = "sve")]
unsafe fn run_compiler_sve_pcs_callee(inp: &[u64; 8], out4: &mut [u64; 8]) {
    let pg = svptrue_b64();
    let r_sve = compiler_sve_pcs_callee(svld1_u64(pg, inp.as_ptr()), inp.as_ptr());
    svst1_u64(pg, out4.as_mut_ptr(), r_sve);
}

#[inline(never)]
pub unsafe fn nzcv_miscompile_witness(a: u64, b: u64) -> u64 {
    let eq = a == b;
    let mut x = a;
    let mut y = b;
    asm!(
        "subs {x}, {x}, {x}",
        "mov {y}, #0",
        x = inout(reg) x,
        y = inout(reg) y,
        options(nomem, nostack, preserves_flags)
    );
    if eq { 0xDEAD_BEEF + x + y } else { 0x1111_2222 + x + y }
}

#[inline(never)]
pub unsafe fn fpcr_sink_demo(a: f64, b: f64) -> (u64, u64) {
    let sum_before = a + b;
    let orig_fpcr: u64;
    asm!(
        "mrs {orig}, fpcr",
        "orr x9, {orig}, #(1 << 24)",
        "msr fpcr, x9",
        orig = out(reg) orig_fpcr,
        out("x9") _,
        options(nomem, nostack, preserves_flags)
    );
    let sum_during = core::hint::black_box(a) + core::hint::black_box(b);
    asm!("msr fpcr, {orig}", orig = in(reg) orig_fpcr, options(nomem, nostack, preserves_flags));
    (sum_before.to_bits(), sum_during.to_bits())
}

#[inline(never)]
pub unsafe fn fpsr_qc_sticky_probe() -> (u64, u64, u64, u64) {
    let (c, q, s, dz): (u64, u64, u64, u64);
    asm!(
        "msr fpsr, xzr",
        "mrs {c}, fpsr",
        "movi v0.16b, #0xff",
        "uqadd v0.16b, v0.16b, v0.16b",
        "mrs {q}, fpsr",
        "add v0.16b, v0.16b, v0.16b",
        "mrs {s}, fpsr",
        "msr fpsr, xzr",
        "fmov s0, #1.0",
        "movi d1, #0",
        "fdiv s0, s0, s1",
        "mrs {dz}, fpsr",
        "msr fpsr, xzr",
        c = out(reg) c, q = out(reg) q, s = out(reg) s, dz = out(reg) dz,
        out("v0") _, out("v1") _,
        options(nomem, nostack, preserves_flags)
    );
    (c, q, s, dz)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    let vl_bytes: u64;
    asm!(".arch_extension sve\\n cntb {0}", out(reg) vl_bytes, options(nomem, nostack, preserves_flags));
    write_hex_u64(b"vl_bytes=", vl_bytes);

    let inp = [
        0x1111_1111_1111_1110u64, 0x2222_2222_2222_2221u64,
        0x3333_3333_3333_3332u64, 0x4444_4444_4444_4443u64,
        0x5555_5555_5555_5554u64, 0x6666_6666_6666_6665u64,
        0x7777_7777_7777_7776u64, 0x8888_8888_8888_8887u64,
    ];
    let mut out1 = [0u64; 8];
    test_sve_spill_across_all_z_clobbers(&inp, &mut out1);
    write_hex_u64(b"spill_lane0=", out1[0]);
    write_hex_u64(b"spill_lane1=", out1[1]);
    write_hex_u64(b"spill_lane3=", out1[3]);
    write_hex_u64(b"spill_lane7=", out1[7]);

    let mut out2 = [0u64; 8];
    test_sve_pcs_z8_partial_save_corruption(&inp, &mut out2);
    write_hex_u64(b"sve_pcs_d8_save_lane0=", out2[0]);
    write_hex_u64(b"sve_pcs_d8_save_lane1=", out2[1]);
    write_hex_u64(b"sve_pcs_d8_save_lane2=", out2[2]);

    let mut out3 = [0u64; 8];
    test_compiler_base_pcs_callee_on_z8(&inp, &mut out3);
    write_hex_u64(b"base_pcs_callee_z8_lane0=", out3[0]);
    write_hex_u64(b"base_pcs_callee_z8_lane1=", out3[1]);
    write_hex_u64(b"base_pcs_callee_z8_lane2=", out3[2]);

    let mut out4 = [0u64; 8];
    run_compiler_sve_pcs_callee(&inp, &mut out4);
    write_hex_u64(b"compiler_sve_pcs_ret_lane3=", out4[3]);

    let nzcv_bad = nzcv_miscompile_witness(core::hint::black_box(5), core::hint::black_box(9));
    write_hex_u64(b"nzcv_5_eq_9_miscompiled=", nzcv_bad);

    let sub = core::hint::black_box(f64::from_bits(1));
    let (sb, sd) = fpcr_sink_demo(sub, sub);
    write_hex_u64(b"fpcr_sum_before_sunk=", sb);
    write_hex_u64(b"fpcr_sum_during_fz1=", sd);

    let (c, q, s, dz) = fpsr_qc_sticky_probe();
    write_hex_u64(b"fpsr_clean=", c);
    write_hex_u64(b"fpsr_after_uqadd_qc=", q);
    write_hex_u64(b"fpsr_sticky_after_add=", s);
    write_hex_u64(b"fpsr_after_divzero_dzc=", dz);

    asm!("mov x8, #93\\n svc #0", in("x0") 0usize, options(noreturn));
}
"""
    with tempfile.TemporaryDirectory() as tmp:
        src = os.path.join(tmp, "sve_flags.rs")
        exe = os.path.join(tmp, "sve_flags")
        with open(src, "w", encoding="utf-8") as f:
            f.write(rust_src)
        subprocess.run(
            [
                "rustc",
                "+nightly-2026-09-30",
                "--target",
                "aarch64-unknown-linux-gnu",
                "-C",
                "linker-flavor=ld.lld",
                "-C",
                "linker=rust-lld",
                "-C",
                "relocation-model=static",
                "-C",
                "panic=abort",
                "-O",
                src,
                "-o",
                exe,
            ],
            check=True,
        )
        runs: dict[str, Any] = {}
        for label, cpu in [
            ("vl256", "max,sve-default-vector-length=32"),
            ("vl512_default_max", "max"),
        ]:
            q = run_cmd([qemu_bin, "-cpu", cpu, exe])
            runs[label] = {
                "returncode": q.returncode,
                "values": parse_kv_lines(q.stdout.decode("utf-8", errors="replace")),
            }
        return runs


def probe_pac_mte_tbi(qemu_bin: str) -> dict[str, Any]:
    rust_src = """#![no_std]
#![no_main]
use core::arch::asm;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

unsafe fn write_bytes(buf: &[u8]) {
    asm!(
        "mov x8, #64\\n svc #0",
        in("x0") 1usize, in("x1") buf.as_ptr(), in("x2") buf.len(),
        lateout("x0") _, out("x8") _, options(nostack)
    );
}

unsafe fn write_hex_u64(label: &[u8], val: u64) {
    write_bytes(label);
    let mut out = [0u8; 19];
    out[0] = b'0'; out[1] = b'x';
    let hex = b"0123456789abcdef";
    let mut i = 0;
    while i < 16 { out[2 + i] = hex[((val >> ((15 - i) * 4)) & 0xf) as usize]; i += 1; }
    out[18] = b'\\n';
    write_bytes(&out);
}

unsafe fn syscall6(nr: usize, a0: usize, a1: usize, a2: usize, a3: usize, a4: usize, a5: usize) -> isize {
    let ret: isize;
    asm!(
        "svc #0",
        in("x8") nr, inout("x0") a0 as isize => ret,
        in("x1") a1, in("x2") a2, in("x3") a3, in("x4") a4, in("x5") a5,
        options(nostack)
    );
    ret
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    let mut mode = [b'0'; 1];
    let _ = syscall6(63, 0, mode.as_mut_ptr() as usize, 1, 0, 0, 0);

    if mode[0] == b'0' {
        let mut cell: u64 = 0xCAFE_BABE_1234_5678;
        let raw_p = (&raw mut cell) as u64;
        let tbi_p = raw_p | (0xA5u64 << 56);
        write_hex_u64(b"ptr_eq=", (raw_p == tbi_p) as u64);
        write_hex_u64(b"tbi_load=", core::ptr::read_volatile(tbi_p as *const u64));
        core::ptr::write_volatile(tbi_p as *mut u64, 0xDEAD_BEEF_9999_0001);
        write_hex_u64(b"raw_readback=", core::ptr::read_volatile(&raw const cell));

        let mut pacda_tbi = tbi_p;
        let modifier: u64 = 0x1234_5678_9ABC_DEF0;
        asm!(".arch_extension pauth\\n pacda {d}, {m}", d = inout(reg) pacda_tbi, m = in(reg) modifier, options(nomem, nostack));
        write_hex_u64(b"pacda_top_byte=", pacda_tbi >> 56);
        write_hex_u64(b"pacda_pac_field_nonzero=", (((pacda_tbi ^ tbi_p) >> 48) & 0x7f != 0) as u64);

        let mut aut_ok = pacda_tbi;
        asm!(".arch_extension pauth\\n autda {d}, {m}", d = inout(reg) aut_ok, m = in(reg) modifier, options(nomem, nostack));
        write_hex_u64(b"autda_restored_eq_tbi=", (aut_ok == tbi_p) as u64);

        let mut xpac_forged = pacda_tbi ^ (1u64 << 50);
        asm!(".arch_extension pauth\\n xpacd {d}", d = inout(reg) xpac_forged, options(nomem, nostack));
        write_hex_u64(b"xpacd_forged_deref=", core::ptr::read_volatile(xpac_forged as *const u64));

        let prctl_rc = syscall6(167, 55, 1 | 2 | (0xfffe << 3), 0, 0, 0, 0);
        write_hex_u64(b"mte_prctl_rc=", prctl_rc as u64);
        let mte_page = syscall6(222, 0, 4096, 1 | 2 | 0x20, 2 | 0x20, usize::MAX, 0);
        let base = mte_page as u64;
        let p_tag5 = base | (5u64 << 56);
        let p_tag9 = (base + 16) | (9u64 << 56);
        let mut ldg_out = base;
        asm!(
            ".arch_extension memtag\\n stg {p5}, [{p5}]\\n stg {p9}, [{p9}]\\n ldg {lo}, [{b}]",
            p5 = in(reg) p_tag5, p9 = in(reg) p_tag9, lo = inout(reg) ldg_out, b = in(reg) base,
            options(nostack)
        );
        write_hex_u64(b"mte_ldg_tag_nibble=", (ldg_out >> 56) & 0xf);
        core::ptr::write_volatile(p_tag5 as *mut u64, 0x7777_8888_9999_AAAA);
        write_hex_u64(b"mte_tag5_load=", core::ptr::read_volatile(p_tag5 as *const u64));
    } else if mode[0] == b'1' {
        let mut cell: u64 = 0x42;
        let raw = (&raw mut cell) as u64;
        let mut signed = raw;
        let m: u64 = 0x1111;
        asm!(".arch_extension pauth\\n pacda {p}, {m}", p = inout(reg) signed, m = in(reg) m, options(nomem, nostack));
        let mut bad = signed ^ (1u64 << 49);
        write_bytes(b"stage=before_autda\\n");
        asm!(".arch_extension pauth\\n autda {p}, {m}", p = inout(reg) bad, m = in(reg) m, options(nomem, nostack));
        write_hex_u64(b"post_autda_xor_residual=", (bad ^ raw) >> 48);
        let mut stripped = bad;
        asm!(".arch_extension pauth\\n xpacd {p}", p = inout(reg) stripped, options(nomem, nostack));
        write_hex_u64(b"pre_fpac_xpacd_bypass_val=", core::ptr::read_volatile(stripped as *const u64));
        let _ = core::ptr::read_volatile(bad as *const u64);
    } else if mode[0] == b'2' {
        let _ = syscall6(167, 55, 1 | 2 | (0xfffe << 3), 0, 0, 0, 0);
        let base = syscall6(222, 0, 4096, 1 | 2 | 0x20, 2 | 0x20, usize::MAX, 0) as u64;
        let p_tag5 = base | (5u64 << 56);
        asm!(".arch_extension memtag\\n stg {p5}, [{p5}]", p5 = in(reg) p_tag5, options(nostack));
        write_bytes(b"stage=before_mte_tag0_mismatch\\n");
        let _ = core::ptr::read_volatile(base as *const u64);
    } else if mode[0] == b'3' {
        let _ = syscall6(167, 55, 1 | 2 | (0xfffe << 3), 0, 0, 0, 0);
        let base = syscall6(222, 0, 4096, 1 | 2 | 0x20, 2 | 0x20, usize::MAX, 0) as u64;
        let p_tag5 = base | (5u64 << 56);
        let p_tag9 = (base + 16) | (9u64 << 56);
        asm!(".arch_extension memtag\\n stg {p5}, [{p5}]\\n stg {p9}, [{p9}]", p5 = in(reg) p_tag5, p9 = in(reg) p_tag9, options(nostack));
        write_bytes(b"stage=before_mte_spatial_overflow\\n");
        let _ = core::ptr::read_volatile((p_tag5 + 16) as *const u64);
    }
    asm!("mov x8, #93\\n svc #0", in("x0") 0usize, options(noreturn));
}
"""
    with tempfile.TemporaryDirectory() as tmp:
        src = os.path.join(tmp, "pac_mte.rs")
        exe = os.path.join(tmp, "pac_mte")
        with open(src, "w", encoding="utf-8") as f:
            f.write(rust_src)
        subprocess.run(
            [
                "rustc",
                "+1.99.1",
                "--target",
                "aarch64-unknown-linux-gnu",
                "-C",
                "linker-flavor=ld.lld",
                "-C",
                "linker=rust-lld",
                "-C",
                "relocation-model=static",
                "-C",
                "panic=abort",
                "-O",
                src,
                "-o",
                exe,
            ],
            check=True,
        )
        out: dict[str, Any] = {}
        for key, mode_b, cpu in [
            ("valid_tbi0_pacda_xpacd_mte_max", b"0", "max"),
            ("corrupted_autda_fpac_max", b"1", "max"),
            ("corrupted_autda_fpac_neoverse_n2", b"1", "neoverse-n2"),
            ("corrupted_autda_pre_fpac_epac_neoverse_v1", b"1", "neoverse-v1"),
            ("mte_sync_temporal_tag_mismatch_max", b"2", "max"),
            ("mte_sync_spatial_granule_overflow_max", b"3", "max"),
        ]:
            q = run_cmd([qemu_bin, "-cpu", cpu, exe], input_bytes=mode_b)
            out[key] = {
                "cpu": cpu,
                "returncode": q.returncode,
                "values": parse_kv_lines(q.stdout.decode("utf-8", errors="replace")),
            }
        return out


def probe_stt_tls_and_outlined_atomics(qemu_bin: str) -> dict[str, Any]:
    sysroot = rustc_sysroot("+1.99.1")
    lld_bin = str(sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld/ld.lld")
    llvm_mc = shutil.which("llvm-mc") or "/usr/bin/llvm-mc"

    with tempfile.TemporaryDirectory() as tmp:
        tls_s = os.path.join(tmp, "tls_def.s")
        tls_o = os.path.join(tmp, "tls_def.o")
        with open(tls_s, "w", encoding="utf-8") as f:
            f.write(
                """
    .type c_tls_var, %tls_object
    .section .tdata,"awT",@progbits
    .globl c_tls_var
    .space 0x30
    .p2align 3
c_tls_var:
    .xword 0x1122334455667788
    .size c_tls_var, 8
"""
            )
        subprocess.run(
            [llvm_mc, "--triple=aarch64-unknown-linux-gnu", "--filetype=obj", tls_s, "-o", tls_o],
            check=True,
        )

        # 1. Static non-PIE STT_TLS mislink -> resolves to 0x30 and faults with SIGSEGV
        rs_static = os.path.join(tmp, "tls_static.rs")
        obj_static = os.path.join(tmp, "tls_static.o")
        exe_static = os.path.join(tmp, "tls_static")
        with open(rs_static, "w", encoding="utf-8") as f:
            f.write(
                """#![no_std]
#![no_main]
use core::arch::asm;
#[panic_handler] fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
unsafe extern "C" { static c_tls_var: u64; }
unsafe fn write_bytes(buf: &[u8]) {
    asm!("mov x8, #64\\n svc #0", in("x0") 1usize, in("x1") buf.as_ptr(), in("x2") buf.len(), lateout("x0") _, out("x8") _, options(nostack));
}
unsafe fn write_hex_u64(label: &[u8], val: u64) {
    write_bytes(label);
    let mut out = [0u8; 19]; out[0] = b'0'; out[1] = b'x';
    let hex = b"0123456789abcdef";
    let mut i = 0; while i < 16 { out[2 + i] = hex[((val >> ((15 - i) * 4)) & 0xf) as usize]; i += 1; }
    out[18] = b'\\n'; write_bytes(&out);
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    let addr = (&raw const c_tls_var) as u64;
    write_hex_u64(b"static_resolved_addr=", addr);
    let _ = core::ptr::read_volatile(&raw const c_tls_var);
    asm!("mov x8, #93\\n svc #0", in("x0") 0usize, options(noreturn));
}
"""
            )
        subprocess.run(
            [
                "rustc",
                "+1.99.1",
                "--target=aarch64-unknown-linux-gnu",
                "-Crelocation-model=static",
                "-Cpanic=abort",
                "-O",
                "--emit=obj",
                rs_static,
                "-o",
                obj_static,
            ],
            check=True,
        )
        r_link_static = subprocess.run([lld_bin, obj_static, tls_o, "-o", exe_static], capture_output=True)
        q_static = run_cmd([qemu_bin, "-cpu", "max", exe_static])

        # 2. PIE STT_TLS mislink -> R_AARCH64_RELATIVE (pie_base + 0x30) reads ELF64 header bytes!
        rs_pie = os.path.join(tmp, "tls_pie.rs")
        obj_pie = os.path.join(tmp, "tls_pie.o")
        exe_pie = os.path.join(tmp, "tls_pie")
        with open(rs_pie, "w", encoding="utf-8") as f:
            f.write(
                """#![no_std]
#![no_main]
use core::arch::asm;
#[panic_handler] fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
unsafe extern "C" { static c_tls_var: u64; }
#[repr(C)] struct Elf64Rela { r_offset: u64, r_info: u64, r_addend: i64 }
unsafe fn write_bytes(buf: &[u8]) {
    asm!("mov x8, #64\\n svc #0", in("x0") 1usize, in("x1") buf.as_ptr(), in("x2") buf.len(), lateout("x0") _, out("x8") _, options(nostack));
}
unsafe fn write_hex_u64(label: &[u8], val: u64) {
    write_bytes(label);
    let mut out = [0u8; 19]; out[0] = b'0'; out[1] = b'x';
    let hex = b"0123456789abcdef";
    let mut i = 0; while i < 16 { out[2 + i] = hex[((val >> ((15 - i) * 4)) & 0xf) as usize]; i += 1; }
    out[18] = b'\\n'; write_bytes(&out);
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    let pie_base: u64;
    asm!("adrp {0}, __ehdr_start", out(reg) pie_base, options(nomem, nostack, preserves_flags));
    let e_phoff = *((pie_base + 32) as *const u64);
    let e_phnum = *((pie_base + 56) as *const u16) as usize;
    let (mut rela_addr, mut rela_sz) = (0u64, 0u64);
    let mut i = 0;
    while i < e_phnum {
        let ph = pie_base + e_phoff + (i as u64) * 56;
        if *(ph as *const u32) == 2 {
            let mut dyn_p = (pie_base + *((ph + 16) as *const u64)) as *const u64;
            loop {
                let tag = *dyn_p; let val = *dyn_p.add(1);
                if tag == 0 { break; }
                if tag == 7 { rela_addr = pie_base + val; }
                if tag == 8 { rela_sz = val; }
                dyn_p = dyn_p.add(2);
            }
        }
        i += 1;
    }
    let mut k = 0;
    while k < (rela_sz / 24) as usize {
        let r = &*((rela_addr as *const Elf64Rela).add(k));
        if (r.r_info & 0xffff_ffff) == 0x403 {
            *((pie_base + r.r_offset) as *mut u64) = (pie_base as i64 + r.r_addend) as u64;
        }
        k += 1;
    }
    let bad_offset = (&raw const c_tls_var) as u64 - pie_base;
    let bad_val = core::ptr::read_volatile(&raw const c_tls_var);
    write_hex_u64(b"pie_offset_from_ehdr=", bad_offset);
    write_hex_u64(b"pie_corrupted_elf_hdr_val=", bad_val);
    asm!("mov x8, #93\\n svc #0", in("x0") 0usize, options(noreturn));
}
"""
            )
        subprocess.run(
            [
                "rustc",
                "+1.99.1",
                "--target=aarch64-unknown-linux-gnu",
                "-Crelocation-model=pic",
                "-Cpanic=abort",
                "-O",
                "--emit=obj",
                rs_pie,
                "-o",
                obj_pie,
            ],
            check=True,
        )
        r_link_pie = subprocess.run([lld_bin, "-pie", obj_pie, tls_o, "-o", exe_pie], capture_output=True)
        with open(exe_pie, "rb") as bf:
            bf.seek(0x30)
            elf_hdr_u64 = f"0x{struct.unpack('<Q', bf.read(8))[0]:016x}"
        q_pie = run_cmd([qemu_bin, "-cpu", "max", exe_pie])

        # 3. Outlined atomics (LL/SC vs LSE) + ExclusiveMonitor nondeterminism probe
        atom_rs = os.path.join(tmp, "atom.rs")
        atom_exe = os.path.join(tmp, "atom")
        with open(atom_rs, "w", encoding="utf-8") as f:
            f.write(
                """#![no_std]
#![no_main]
#![feature(integer_atomics)]
use core::arch::asm;
use core::sync::atomic::{AtomicU32, AtomicU64, AtomicU128, Ordering};

#[panic_handler] fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[unsafe(no_mangle)] pub unsafe extern "C" fn getauxval(_ty: u64) -> u64 { 0 }
unsafe extern "C" {
    static mut __aarch64_have_lse_atomics: u8;
    fn __aarch64_cas8_acq_rel(expected: u64, desired: u64, ptr: *mut u64) -> u64;
}
unsafe fn write_bytes(buf: &[u8]) {
    asm!("mov x8, #64\\n svc #0", in("x0") 1usize, in("x1") buf.as_ptr(), in("x2") buf.len(), lateout("x0") _, out("x8") _, options(nostack));
}
unsafe fn write_hex_u64(label: &[u8], val: u64) {
    write_bytes(label);
    let mut out = [0u8; 19]; out[0] = b'0'; out[1] = b'x';
    let hex = b"0123456789abcdef";
    let mut i = 0; while i < 16 { out[2 + i] = hex[((val >> ((15 - i) * 4)) & 0xf) as usize]; i += 1; }
    out[18] = b'\\n'; write_bytes(&out);
}
#[inline(never)]
pub fn run_outlined_suite(a: &AtomicU32, b: &AtomicU64, c: &AtomicU128, vals: &[u64; 16]) -> u64 {
    let mut acc = 0u64;
    let mut i = 0;
    while i < 16 { acc ^= vals[i]; i += 1; }
    let old_a = a.fetch_add(7, Ordering::SeqCst) as u64;
    let _ = b.compare_exchange(10, 20, Ordering::SeqCst, Ordering::Acquire);
    let _ = c.compare_exchange(100, 200, Ordering::SeqCst, Ordering::Acquire);
    let max_prev = a.fetch_max(99, Ordering::AcqRel) as u64;
    acc ^ old_a ^ max_prev
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    let vals = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,0x1234_5678_9abc_def0u64];
    __aarch64_have_lse_atomics = 0;
    let (a1, b1, c1) = (AtomicU32::new(5), AtomicU64::new(10), AtomicU128::new(100));
    let r_llsc = run_outlined_suite(&a1, &b1, &c1, &vals);

    __aarch64_have_lse_atomics = 1;
    let (a2, b2, c2) = (AtomicU32::new(5), AtomicU64::new(10), AtomicU128::new(100));
    let r_lse = run_outlined_suite(&a2, &b2, &c2, &vals);
    write_hex_u64(b"llsc_eq_lse=", (r_llsc == r_lse && b1.load(Ordering::Relaxed) == 20 && b2.load(Ordering::Relaxed) == 20) as u64);

    let (mut cell_x, mut cell_y) = (0x100u64, 0x200u64);
    let (st_clrex, st_interleaved, st_clean, st_failed_cas): (u32, u32, u32, u32);
    __aarch64_have_lse_atomics = 0;
    asm!(
        "ldxr x9, [{px}]\\n clrex\\n mov x10, #0x999\\n stxr {s1:w}, x10, [{px}]",
        "ldxr x9, [{px}]\\n ldxr x11, [{py}]\\n add x11, x11, #1\\n stxr w12, x11, [{py}]\\n stxr {s2:w}, x10, [{px}]",
        "ldxr x9, [{px}]\\n add x9, x9, #0x55\\n stxr {s3:w}, x9, [{px}]",
        "ldxr x9, [{px}]\\n mov x0, #0xdead\\n mov x1, #0xbeef\\n mov x2, {py}\\n bl __aarch64_cas8_acq_rel\\n mov x10, #0x777\\n stxr {s4:w}, x10, [{px}]",
        px = in(reg) &raw mut cell_x, py = in(reg) &raw mut cell_y,
        s1 = out(reg) st_clrex, s2 = out(reg) st_interleaved, s3 = out(reg) st_clean, s4 = out(reg) st_failed_cas,
        out("x0") _, out("x1") _, out("x2") _, out("x9") _, out("x10") _, out("x11") _, out("w12") _,
        out("x16") _, out("x17") _, out("x30") _,
        options(nostack)
    );
    write_hex_u64(b"stxr_after_clrex=", st_clrex as u64);
    write_hex_u64(b"stxr_after_interleaved_y=", st_interleaved as u64);
    write_hex_u64(b"stxr_clean=", st_clean as u64);
    write_hex_u64(b"stxr_after_nested_failed_cas=", st_failed_cas as u64);
    write_hex_u64(b"final_cell_x=", cell_x);
    asm!("mov x8, #93\\n svc #0", in("x0") 0usize, options(noreturn));
}
"""
            )
        subprocess.run(
            [
                "rustc",
                "+nightly-2026-09-30",
                "--target=aarch64-unknown-linux-gnu",
                "-Clinker-flavor=ld.lld",
                "-Clinker=rust-lld",
                "-Crelocation-model=static",
                "-Cpanic=abort",
                "-O",
                atom_rs,
                "-o",
                atom_exe,
            ],
            check=True,
        )
        q_atom = run_cmd([qemu_bin, "-cpu", "max", atom_exe])

        return {
            "stt_tls_static_mislink": {
                "lld_returncode": r_link_static.returncode,
                "qemu_returncode": q_static.returncode,
                "values": parse_kv_lines(q_static.stdout.decode("utf-8", errors="replace")),
            },
            "stt_tls_pie_mislink": {
                "lld_returncode": r_link_pie.returncode,
                "qemu_returncode": q_pie.returncode,
                "elf64_header_bytes_0x30_0x38": elf_hdr_u64,
                "values": parse_kv_lines(q_pie.stdout.decode("utf-8", errors="replace")),
            },
            "outlined_atomics_and_exclusive_monitor": {
                "qemu_returncode": q_atom.returncode,
                "values": parse_kv_lines(q_atom.stdout.decode("utf-8", errors="replace")),
            },
        }


def main() -> int:
    qemu_bin = shutil.which("qemu-aarch64") or "/usr/bin/qemu-aarch64"
    qemu_ver = subprocess.check_output([qemu_bin, "--version"], text=True).splitlines()[0]
    toolchains = ["+1.99.1", "+nightly-2026-09-30"]

    payload = {
        "toolchains": {tc: rustc_version_info(tc) for tc in toolchains},
        "qemu_aarch64_version": qemu_ver,
        "asm_feature_and_constraint_matrix": probe_asm_feature_matrix(toolchains),
        "sve_pcs_and_flags_live": probe_sve_pcs_and_flags(qemu_bin),
        "pac_mte_tbi0_live": probe_pac_mte_tbi(qemu_bin),
        "stt_tls_and_outlined_atomics_live": probe_stt_tls_and_outlined_atomics(qemu_bin),
    }

    out_path = Path(__file__).resolve().with_name("probe_aarch64_seams_results.json")
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {out_path.name} successfully")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
