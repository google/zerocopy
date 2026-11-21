#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Standalone empirical probes for Seams 1 & 2:
1. System V 128-byte red-zone corruption of safe Rust locals across balanced
   `push`/`pop`, `pushfq`/`pop`, and `call` inside `options(nostack)` (`rsp_exit == rsp_entry`),
   contrasted against omitting `nostack` and `-C no-redzone=yes` across `rustc 1.99.1` and `1.102.0-nightly`.
2. `MXCSR` sticky flags (`[5:0]`) vs control bits (`[15:6]`) under `options(preserves_flags)`,
   `rustc` `out("mxcsr")` rejection, and LLVM IR clobber lowering.
3. `gcc 15.2.0` `crtfastmath.o` `.init_array` pre-`main` `MXCSR` (`DAZ | FTZ`) poisoning
   across executable linkage (`-ffast-math` / `-Ofast`) and shared-library linkage (`-shared -ffast-math`
   vs `-shared -mdaz-ftz`).
4. Exhaustive bit-level comparison of Rust `f32::{min, max, minimum, maximum, mul_add}`
   against hardware x86 `vminss`, `vmaxss`, and `vfmadd213ss` (`+fma` vs baseline `fmaf`).
"""

from __future__ import annotations

import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile


TOOLCHAINS = [
    ("1.99.1", "+1.99.1"),
    ("1.102.0-nightly", "+nightly"),
]


def run_cmd(cmd: list[str], cwd: pathlib.Path | None = None, check: bool = True, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    cp = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, env=env)
    if check and cp.returncode != 0:
        raise RuntimeError(f"Command {cmd} failed (rc={cp.returncode}):\nSTDOUT:\n{cp.stdout}\nSTDERR:\n{cp.stderr}")
    return cp


def probe_1_nostack_redzone() -> dict:
    rust_src = r'''
#![allow(unused_assignments)]
use core::arch::asm;

// Leaf function: zero function calls! Under SysV AMD64 (`x86_64-unknown-linux-gnu`),
// `options(nostack)` sets `alignstack = false`, so `MFI.adjustsStack()` stays `false`
// (`FinalizeISel.cpp:61-62`) and `X86FrameLowering.cpp:1780-1793` places the pure
// safe Rust stack array `safe_locals` inside the 128-byte red zone (`-16(%rsp)..0(%rsp)`).
// Note: `push` decrements `%rsp` by 8 and writes to `(%rsp)` = `rsp_entry - 8`, which
// aliases `safe_locals[1]` (`-8(%rsp)`)!
#[unsafe(no_mangle)]
#[inline(never)]
pub fn victim_nostack_push_pop(v0: u64, v1: u64, idx: usize, poison: u64) -> (u64, u64, u64) {
    let mut safe_locals: [u64; 2] = [v0, v1];
    // Dynamic indexed mutation forces `safe_locals` onto the stack (cannot stay in GPRs)
    safe_locals[idx & 1] ^= 0;
    let rsp_before: u64;
    let rsp_after: u64;
    let scratch: u64;
    unsafe {
        asm!(
            "mov {rb}, rsp",
            "push {p}",
            "pop {sc}",
            "mov {ra}, rsp",
            p = in(reg) poison,
            rb = out(reg) rsp_before,
            ra = out(reg) rsp_after,
            sc = out(reg) scratch,
            options(nomem, nostack, preserves_flags),
        );
    }
    let _ = scratch;
    (safe_locals[idx & 1], safe_locals[(idx + 1) & 1], rsp_before ^ rsp_after)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn victim_nostack_pushfq_pop(v0: u64, v1: u64, idx: usize) -> (u64, u64, u64) {
    let mut safe_locals: [u64; 2] = [v0, v1];
    safe_locals[idx & 1] ^= 0;
    let rsp_before: u64;
    let rsp_after: u64;
    let flags_copy: u64;
    unsafe {
        asm!(
            "mov {rb}, rsp",
            "pushfq",
            "pop {fc}",
            "mov {ra}, rsp",
            rb = out(reg) rsp_before,
            ra = out(reg) rsp_after,
            fc = out(reg) flags_copy,
            options(nomem, nostack, preserves_flags),
        );
    }
    let _ = flags_copy;
    (safe_locals[idx & 1], safe_locals[(idx + 1) & 1], rsp_before ^ rsp_after)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn victim_nostack_internal_call(v0: u64, v1: u64, idx: usize) -> (u64, u64, u64) {
    let mut safe_locals: [u64; 2] = [v0, v1];
    safe_locals[idx & 1] ^= 0;
    let rsp_before: u64;
    let rsp_after: u64;
    unsafe {
        asm!(
            "mov {rb}, rsp",
            "call 2f",
            "jmp 3f",
            "2:",
            "ret",
            "3:",
            "mov {ra}, rsp",
            rb = out(reg) rsp_before,
            ra = out(reg) rsp_after,
            options(nomem, nostack, preserves_flags),
        );
    }
    (safe_locals[idx & 1], safe_locals[(idx + 1) & 1], rsp_before ^ rsp_after)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn safe_with_stack_option(v0: u64, v1: u64, idx: usize, poison: u64) -> (u64, u64, u64) {
    let mut safe_locals: [u64; 2] = [v0, v1];
    safe_locals[idx & 1] ^= 0;
    let rsp_before: u64;
    let rsp_after: u64;
    let scratch: u64;
    unsafe {
        // Omitting `nostack` sets `alignstack = true`, allocating frame above `rsp`.
        asm!(
            "mov {rb}, rsp",
            "push {p}",
            "pop {sc}",
            "mov {ra}, rsp",
            p = in(reg) poison,
            rb = out(reg) rsp_before,
            ra = out(reg) rsp_after,
            sc = out(reg) scratch,
            options(nomem, preserves_flags),
        );
    }
    let _ = scratch;
    (safe_locals[idx & 1], safe_locals[(idx + 1) & 1], rsp_before ^ rsp_after)
}

fn main() {
    let v0 = std::hint::black_box(0x1122_3344_5566_7788u64);
    let v1 = std::hint::black_box(0x99aa_bbcc_ddee_ff00u64);
    let idx = std::hint::black_box(0usize);
    let poison = std::hint::black_box(0xdead_beef_cafe_babeu64);
    let (a0, a1, dx_a) = victim_nostack_push_pop(v0, v1, idx, poison);
    let (b0, b1, dx_b) = victim_nostack_pushfq_pop(v0, v1, idx);
    let (c0, c1, dx_c) = victim_nostack_internal_call(v0, v1, idx);
    let (d0, d1, dx_d) = safe_with_stack_option(v0, v1, idx, poison);
    println!(
        "{{\"push_pop\":[\"0x{:016x}\",\"0x{:016x}\",{}],\"pushfq\":[\"0x{:016x}\",\"0x{:016x}\",{}],\"call\":[\"0x{:016x}\",\"0x{:016x}\",{}],\"without_nostack\":[\"0x{:016x}\",\"0x{:016x}\",{}]}}",
        a0, a1, dx_a, b0, b1, dx_b, c0, c1, dx_c, d0, d1, dx_d
    );
}
'''
    results = {}
    with tempfile.TemporaryDirectory() as td:
        tdp = pathlib.Path(td)
        src = tdp / "redzone_probe.rs"
        src.write_text(rust_src)
        for tc_label, tc_arg in TOOLCHAINS:
            tc_res = {}
            for mode, extra_flags in [
                ("default_redzone", []),
                ("no_redzone", ["-C", "no-redzone=yes"]),
            ]:
                bin_path = tdp / f"rz_{tc_label}_{mode}"
                asm_path = tdp / f"rz_{tc_label}_{mode}.s"
                run_cmd(["rustc", tc_arg, "--edition=2024", "-C", "opt-level=3", *extra_flags, str(src), "-o", str(bin_path)])
                run_cmd(["rustc", tc_arg, "--edition=2024", "-C", "opt-level=3", *extra_flags, "--emit=asm", str(src), "-o", str(asm_path)])
                out_json = json.loads(run_cmd([str(bin_path)]).stdout.strip())
                asm_txt = asm_path.read_text()
                # Extract victim_nostack_push_pop and safe_with_stack_option assembly snippets
                snippets = {}
                for fn_name in ["victim_nostack_push_pop", "safe_with_stack_option"]:
                    m = re.search(rf"([A-Za-z0-9_$.]*{fn_name}[A-Za-z0-9_$.]*:\n(?:.*\n){{1,38}}?)\s*\.size", asm_txt)
                    snippets[fn_name] = m.group(1).strip() if m else "NOT_FOUND"
                tc_res[mode] = {
                    "runtime": out_json,
                    "asm_snippets": snippets,
                }
            results[tc_label] = tc_res
    return results


def probe_2_mxcsr_and_fastmath() -> dict:
    results = {}
    with tempfile.TemporaryDirectory() as td:
        tdp = pathlib.Path(td)

        # 2A. Check if `out("mxcsr") _` is accepted or rejected by rustc, and inspect LLVM IR for preserves_flags
        mxcsr_reg_test = tdp / "mxcsr_reg_test.rs"
        mxcsr_reg_test.write_text(
            'pub unsafe fn f() { core::arch::asm!("nop", out("mxcsr") _); }\n'
        )
        reg_check = {}
        for tc_label, tc_arg in TOOLCHAINS:
            cp = run_cmd(["rustc", tc_arg, "--edition=2024", "--crate-type=lib", str(mxcsr_reg_test), "-o", str(tdp / "libmx.rlib")], check=False)
            reg_check[tc_label] = {
                "returncode": cp.returncode,
                "stderr_first_line": cp.stderr.strip().splitlines()[0] if cp.stderr.strip() else "",
            }
        results["rustc_mxcsr_clobber_register"] = reg_check

        # Check LLVM IR constraint strings with vs without preserves_flags
        ir_src = tdp / "mxcsr_ir.rs"
        ir_src.write_text(r'''
use core::arch::asm;
#[unsafe(no_mangle)]
pub unsafe fn asm_with_preserves(mut x: f32, y: f32) -> f32 {
    unsafe { asm!("addss {x}, {y}", x = inout(xmm_reg) x, y = in(xmm_reg) y, options(nomem, nostack, preserves_flags)); }
    x
}
#[unsafe(no_mangle)]
pub unsafe fn asm_without_preserves(mut x: f32, y: f32) -> f32 {
    unsafe { asm!("addss {x}, {y}", x = inout(xmm_reg) x, y = in(xmm_reg) y, options(nomem, nostack)); }
    x
}
''')
        ir_out = tdp / "mxcsr_ir.ll"
        run_cmd(["rustc", "+1.99.1", "--edition=2024", "-C", "opt-level=3", "--crate-type=lib", "--emit=llvm-ir", str(ir_src), "-o", str(ir_out)])
        ir_lines = [l.strip() for l in ir_out.read_text().splitlines() if "call float asm" in l]
        results["llvm_ir_preserves_flags_constraints"] = ir_lines

        # Live hardware MXCSR sticky flag transitions across instructions
        mxcsr_hw_src = tdp / "mxcsr_hw.rs"
        mxcsr_hw_src.write_text(r'''
use core::arch::asm;

#[inline(never)]
fn read_mxcsr() -> u32 {
    let mut v: u32 = 0;
    unsafe { asm!("stmxcsr [{p}]", p = in(reg) &mut v, options(nostack, preserves_flags)); }
    v
}

#[inline(never)]
fn write_mxcsr(v: u32) {
    unsafe { asm!("ldmxcsr [{p}]", p = in(reg) &v, options(nostack, preserves_flags)); }
}

fn main() {
    let init = read_mxcsr();
    // 1. Inexact (PE = 0x20): 1.0f32 + 0.1f32
    write_mxcsr(init & !0x3f);
    let mut a = 1.0f32;
    let b = 0.1f32;
    unsafe { asm!("addss {a}, {b}", a = inout(xmm_reg) a, b = in(xmm_reg) b, options(nomem, nostack)); }
    let after_inexact = read_mxcsr();

    // 2. Invalid (IE = 0x01): vminss(sNaN, 1.0)
    write_mxcsr(init & !0x3f);
    let mut snan = f32::from_bits(0x7f80_0001);
    let one = 1.0f32;
    unsafe { asm!("minss {a}, {b}", a = inout(xmm_reg) snan, b = in(xmm_reg) one, options(nomem, nostack)); }
    let after_invalid = read_mxcsr();

    // 3. Denormal (DE = 0x02): addss(subnormal, 1.0)
    write_mxcsr(init & !0x3f);
    let mut sub = f32::from_bits(0x0040_0000);
    unsafe { asm!("addss {a}, {b}", a = inout(xmm_reg) sub, b = in(xmm_reg) one, options(nomem, nostack)); }
    let after_denorm = read_mxcsr();

    // 4. Divide-by-zero (ZE = 0x04): 1.0 / 0.0
    write_mxcsr(init & !0x3f);
    let mut num = 1.0f32;
    let zero = 0.0f32;
    unsafe { asm!("divss {a}, {b}", a = inout(xmm_reg) num, b = in(xmm_reg) zero, options(nomem, nostack)); }
    let after_divzero = read_mxcsr();

    // 5. Overflow + Inexact (OE | PE = 0x28): f32::MAX * 2.0
    write_mxcsr(init & !0x3f);
    let mut big = f32::MAX;
    let two = 2.0f32;
    unsafe { asm!("mulss {a}, {b}", a = inout(xmm_reg) big, b = in(xmm_reg) two, options(nomem, nostack)); }
    let after_overflow = read_mxcsr();

    // 6. Underflow + Inexact (UE | PE = 0x30): 1e-38 * 1e-10
    write_mxcsr(init & !0x3f);
    let mut tiny = f32::from_bits(0x0080_0000);
    let half = 0.3f32;
    unsafe { asm!("mulss {a}, {b}", a = inout(xmm_reg) tiny, b = in(xmm_reg) half, options(nomem, nostack)); }
    let after_underflow = read_mxcsr();

    write_mxcsr(init);
    let _ = (a, snan, sub, num, big, tiny);
    println!(
        "{{\"init\":\"0x{:04x}\",\"inexact_pe\":\"0x{:04x}\",\"invalid_ie\":\"0x{:04x}\",\"denorm_de\":\"0x{:04x}\",\"divzero_ze\":\"0x{:04x}\",\"overflow_oe_pe\":\"0x{:04x}\",\"underflow_ue_pe\":\"0x{:04x}\"}}",
        init, after_inexact, after_invalid, after_denorm, after_divzero, after_overflow, after_underflow
    );
}
''')
        mxcsr_hw_bin = tdp / "mxcsr_hw"
        run_cmd(["rustc", "+1.99.1", "--edition=2024", "-C", "opt-level=3", str(mxcsr_hw_src), "-o", str(mxcsr_hw_bin)])
        results["hardware_mxcsr_sticky_transitions"] = json.loads(run_cmd([str(mxcsr_hw_bin)]).stdout.strip())

        # 2B. Live gcc 15.2.0 crtfastmath.o `.init_array` FFI poisoning of pure safe Rust!
        # Pure safe Rust arithmetic function (0 unsafe inside `pure_safe_rust_subnormal_probe`):
        rust_app = tdp / "fastmath_victim.rs"
        rust_app.write_text(r'''
#[cfg(link_plugin)]
#[link(name = "cplugin")]
unsafe extern "C" {
    #[allow(dead_code)]
    fn never_called_c_symbol() -> i32;
}

#[inline(never)]
pub fn pure_safe_rust_subnormal_rt(x: f32, y: f32) -> (u32, u32) {
    // Pure safe Rust: RFC 3514 guarantees gradual underflow & subnormal preservation!
    let sum = x + y;
    let scaled = x * 0.5f32;
    (sum.to_bits(), scaled.to_bits())
}

pub fn pure_safe_rust_subnormal_const() -> (u32, u32) {
    const X: f32 = f32::from_bits(0x0040_0000);
    const SUM: u32 = (X + 0.0f32).to_bits();
    const SCALED: u32 = (X * 0.5f32).to_bits();
    (SUM, SCALED)
}

fn read_mxcsr() -> u32 {
    let mut v: u32 = 0;
    unsafe { core::arch::asm!("stmxcsr [{}]", in(reg) &mut v, options(nostack, preserves_flags)); }
    v
}

fn main() {
    let mxcsr_at_main = read_mxcsr();
    let sub = std::hint::black_box(f32::from_bits(0x0040_0000));
    let zero = std::hint::black_box(0.0f32);
    let (rt_sum, rt_scaled) = pure_safe_rust_subnormal_rt(sub, zero);
    let (ct_sum, ct_scaled) = pure_safe_rust_subnormal_const();
    println!(
        "{{\"mxcsr_at_main\":\"0x{:04x}\",\"rt_sum\":\"0x{:08x}\",\"rt_scaled\":\"0x{:08x}\",\"ct_sum\":\"0x{:08x}\",\"ct_scaled\":\"0x{:08x}\"}}",
        mxcsr_at_main, rt_sum, rt_scaled, ct_sum, ct_scaled
    );
}
''')
        c_plugin = tdp / "cplugin.c"
        c_plugin.write_text("int never_called_c_symbol(void) { return 42; }\n")

        fastmath_cases = {}
        # Case 1: Pure rustc default link
        b1 = tdp / "fm_clean"
        run_cmd(["rustc", "+1.99.1", "--edition=2024", "-C", "opt-level=3", str(rust_app), "-o", str(b1)])
        fastmath_cases["1_pure_rustc_clean"] = json.loads(run_cmd([str(b1)]).stdout.strip())

        # Case 2: Executable linked with gcc -ffast-math (e.g. build system passing -ffast-math to linker)
        b2 = tdp / "fm_exec_ffast_math"
        run_cmd(["rustc", "+1.99.1", "--edition=2024", "-C", "opt-level=3", "-C", "linker=gcc", "-C", "link-arg=-ffast-math", str(rust_app), "-o", str(b2)])
        fastmath_cases["2_exec_link_ffast_math"] = json.loads(run_cmd([str(b2)]).stdout.strip())

        # Case 3: Shared library built with `gcc -shared -fPIC -ffast-math` (GCC 15 `%{!shared:...}` suppresses crtfastmath.o!)
        so_ffast = tdp / "so_ffast"
        so_ffast.mkdir()
        run_cmd(["gcc", "-shared", "-fPIC", "-O3", "-ffast-math", str(c_plugin), "-o", str(so_ffast / "libcplugin.so")])
        b3 = tdp / "fm_shared_ffast"
        run_cmd(["rustc", "+1.99.1", "--edition=2024", "-C", "opt-level=3", "-L", str(so_ffast), "-C", "link-arg=-Wl,--no-as-needed", "-C", "link-arg=-lcplugin", str(rust_app), "-o", str(b3)])
        env3 = dict(os.environ, LD_LIBRARY_PATH=str(so_ffast))
        fastmath_cases["3_shared_so_ffast_math"] = json.loads(run_cmd([str(b3)], env=env3).stdout.strip())
        nm_ffast = run_cmd(["nm", "-a", str(so_ffast / "libcplugin.so")], check=False).stdout
        fastmath_cases["3_shared_so_has_set_fast_math_sym"] = "set_fast_math" in nm_ffast

        # Case 4: Shared library built with `gcc -shared -fPIC -mdaz-ftz` (bypasses `%{!shared:...}` in GCC 15 specs, injecting crtfastmath.o into .so!)
        so_daz = tdp / "so_daz"
        so_daz.mkdir()
        run_cmd(["gcc", "-shared", "-fPIC", "-O3", "-mdaz-ftz", str(c_plugin), "-o", str(so_daz / "libcplugin.so")])
        b4 = tdp / "fm_shared_mdaz_ftz"
        run_cmd(["rustc", "+1.99.1", "--edition=2024", "-C", "opt-level=3", "-L", str(so_daz), "-C", "link-arg=-Wl,--no-as-needed", "-C", "link-arg=-lcplugin", str(rust_app), "-o", str(b4)])
        env4 = dict(os.environ, LD_LIBRARY_PATH=str(so_daz))
        fastmath_cases["4_shared_so_mdaz_ftz"] = json.loads(run_cmd([str(b4)], env=env4).stdout.strip())
        nm_daz = run_cmd(["nm", "-a", str(so_daz / "libcplugin.so")], check=False).stdout
        fastmath_cases["4_shared_so_has_set_fast_math_sym"] = "set_fast_math" in nm_daz

        results["crtfastmath_ffi_poisoning"] = fastmath_cases

        # 2C. Exhaustive corner-case matrix: f32::{min, max, minimum, maximum, mul_add} vs x86 vminss, vmaxss, vfmadd213ss
        fp_probe_src = tdp / "fp_corners.rs"
        fp_probe_src.write_text(r'''
#![cfg_attr(use_nightly_minmax, feature(float_minimum_maximum))]
use core::arch::asm;

#[inline(never)]
fn hw_vminss(a: f32, b: f32) -> (u32, u32) {
    let init: u32;
    let mut mx: u32 = 0;
    unsafe {
        asm!("stmxcsr [{p}]", p = in(reg) &mut mx, options(nostack, preserves_flags));
        init = mx;
        let clean = init & !0x3f;
        asm!("ldmxcsr [{p}]", p = in(reg) &clean, options(nostack, preserves_flags));
    }
    let out: f32;
    unsafe {
        // Note: in AT&T / Intel syntax: `vminss dst, src1, src2` computes `src1 < src2 ? src1 : src2`
        // so on NaN or (-0.0 == +0.0), X86 `vminss dst, a, b` ALWAYS returns SECOND source operand `b`!
        asm!(
            "vminss {out}, {a}, {b}",
            out = lateout(xmm_reg) out,
            a = in(xmm_reg) a,
            b = in(xmm_reg) b,
            options(nomem, nostack),
        );
        asm!("stmxcsr [{p}]", p = in(reg) &mut mx, options(nostack, preserves_flags));
        asm!("ldmxcsr [{p}]", p = in(reg) &init, options(nostack, preserves_flags));
    }
    (out.to_bits(), mx & 0x3f)
}

#[inline(never)]
fn hw_vmaxss(a: f32, b: f32) -> (u32, u32) {
    let init: u32;
    let mut mx: u32 = 0;
    unsafe {
        asm!("stmxcsr [{p}]", p = in(reg) &mut mx, options(nostack, preserves_flags));
        init = mx;
        let clean = init & !0x3f;
        asm!("ldmxcsr [{p}]", p = in(reg) &clean, options(nostack, preserves_flags));
    }
    let out: f32;
    unsafe {
        asm!(
            "vmaxss {out}, {a}, {b}",
            out = lateout(xmm_reg) out,
            a = in(xmm_reg) a,
            b = in(xmm_reg) b,
            options(nomem, nostack),
        );
        asm!("stmxcsr [{p}]", p = in(reg) &mut mx, options(nostack, preserves_flags));
        asm!("ldmxcsr [{p}]", p = in(reg) &init, options(nostack, preserves_flags));
    }
    (out.to_bits(), mx & 0x3f)
}

#[inline(never)]
fn hw_vfmadd213ss(a: f32, b: f32, c: f32) -> (u32, u32) {
    // Intel `vfmadd213ss dst(a), b, c` computes `b * a + c` (or with dst=b: `a * b + c` via `vfmadd213ss b_inout, a, c`)
    let init: u32;
    let mut mx: u32 = 0;
    unsafe {
        asm!("stmxcsr [{p}]", p = in(reg) &mut mx, options(nostack, preserves_flags));
        init = mx;
        let clean = init & !0x3f;
        asm!("ldmxcsr [{p}]", p = in(reg) &clean, options(nostack, preserves_flags));
    }
    let mut acc = b;
    unsafe {
        asm!(
            "vfmadd213ss {acc}, {a}, {c}",
            acc = inout(xmm_reg) acc,
            a = in(xmm_reg) a,
            c = in(xmm_reg) c,
            options(nomem, nostack),
        );
        asm!("stmxcsr [{p}]", p = in(reg) &mut mx, options(nostack, preserves_flags));
        asm!("ldmxcsr [{p}]", p = in(reg) &init, options(nostack, preserves_flags));
    }
    (acc.to_bits(), mx & 0x3f)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn rust_min(a: f32, b: f32) -> u32 { a.min(b).to_bits() }
#[unsafe(no_mangle)]
#[inline(never)]
pub fn rust_max(a: f32, b: f32) -> u32 { a.max(b).to_bits() }

#[cfg(use_nightly_minmax)]
#[unsafe(no_mangle)]
#[inline(never)]
pub fn rust_minimum(a: f32, b: f32) -> u32 { a.minimum(b).to_bits() }
#[cfg(not(use_nightly_minmax))]
#[unsafe(no_mangle)]
#[inline(never)]
pub fn rust_minimum(_a: f32, _b: f32) -> u32 { 0xffff_ffff }

#[cfg(use_nightly_minmax)]
#[unsafe(no_mangle)]
#[inline(never)]
pub fn rust_maximum(a: f32, b: f32) -> u32 { a.maximum(b).to_bits() }
#[cfg(not(use_nightly_minmax))]
#[unsafe(no_mangle)]
#[inline(never)]
pub fn rust_maximum(_a: f32, _b: f32) -> u32 { 0xffff_ffff }

#[unsafe(no_mangle)]
#[inline(never)]
pub fn rust_mul_add(a: f32, b: f32, c: f32) -> u32 { a.mul_add(b, c).to_bits() }

#[inline(never)]
fn rust_sep_mul_add(a: f32, b: f32, c: f32) -> u32 { (a * b + c).to_bits() }

fn main() {
    let pairs: &[(&str, u32, u32)] = &[
        ("neg0_pos0", 0x8000_0000, 0x0000_0000),
        ("pos0_neg0", 0x0000_0000, 0x8000_0000),
        ("qnan1_one", 0x7fc0_0001, 0x3f80_0000),
        ("one_qnan1", 0x3f80_0000, 0x7fc0_0001),
        ("qnan1_qnan2", 0x7fc0_0001, 0x7fc0_0002),
        ("snan1_one", 0x7f80_0001, 0x3f80_0000),
        ("one_snan1", 0x3f80_0000, 0x7f80_0001),
    ];
    print!("{{\"minmax\":[");
    for (i, &(name, ab, bb)) in pairs.iter().enumerate() {
        let a = std::hint::black_box(f32::from_bits(ab));
        let b = std::hint::black_box(f32::from_bits(bb));
        let (vmin_b, vmin_f) = hw_vminss(a, b);
        let (vmax_b, vmax_f) = hw_vmaxss(a, b);
        let rmin = rust_min(a, b);
        let rmax = rust_max(a, b);
        let rminimum = rust_minimum(a, b);
        let rmaximum = rust_maximum(a, b);
        if i > 0 { print!(","); }
        print!(
            "{{\"case\":\"{}\",\"a\":\"0x{:08x}\",\"b\":\"0x{:08x}\",\"rust_min\":\"0x{:08x}\",\"rust_max\":\"0x{:08x}\",\"rust_minimum\":\"0x{:08x}\",\"rust_maximum\":\"0x{:08x}\",\"hw_vminss\":\"0x{:08x}\",\"hw_vminss_flags\":\"0x{:02x}\",\"hw_vmaxss\":\"0x{:08x}\",\"hw_vmaxss_flags\":\"0x{:02x}\"}}",
            name, ab, bb, rmin, rmax, rminimum, rmaximum, vmin_b, vmin_f, vmax_b, vmax_f
        );
    }
    print!("],\"fma\":[");
    let fma_cases: &[(&str, u32, u32, u32)] = &[
        // (1 + 2^-23) * (1 - 2^-23) - 1.0 = -2^-46 (0xa8800000) single-rounded vs +0.0 double-rounded
        ("cancellation_diff_squares", 0x3f80_0001, 0x3f7f_fffe, 0xbf80_0000),
        // Double-rounding midpoint flip: a = 1 + 2^-23 (0x3f800001), b = 1 + 2^-23 (0x3f800001), c = 2^-24 - 2^-47?
        // Let's test (1 + 2^-23)*(1 + 2^-22) + tiny where intermediate tie-even rounds differently!
        // Specifically: a = 0x3f800001 (1 + 2^-23), b = 0x3f800002 (1 + 2^-22):
        // a * b = 1 + 3*2^-23 + 2^-45. Rounded to f32: bit 23 is 1 (odd), sticky 2^-45 > 0, no half bit (2^-24 = 0) -> rounds down to 1 + 3*2^-23 (0x3f800003).
        // Now add c = 2^-24 - 2^-46 (0x337ffffe = 2^-24 * (1 - 2^-23)):
        // Exact a*b + c = 1 + 3*2^-23 + 2^-24 + (2^-45 - 2^-46) = 1 + 3*2^-23 + 2^-24 + 2^-46 > midpoint -> single-round UP to 1 + 4*2^-23 (0x3f800004)!
        // Double-rounded: fl(a*b) = 1 + 3*2^-23 (0x3f800003); fl(a*b) + c = 1 + 3*2^-23 + 2^-24 - 2^-46 < midpoint -> rounds DOWN to 0x3f800003!
        ("double_rounding_1ulp_flip", 0x3f80_0001, 0x3f80_0002, 0x337f_fffe),
        ("qnan_a_b_c", 0x7fc0_0001, 0x3f80_0000, 0x7fc0_0002),
        ("snan_a_b_c", 0x7f80_0001, 0x3f80_0000, 0x3f80_0000),
        ("inf_mul_zero_plus_one", 0x7f80_0000, 0x0000_0000, 0x3f80_0000),
    ];
    for (i, &(name, ab, bb, cb)) in fma_cases.iter().enumerate() {
        let a = std::hint::black_box(f32::from_bits(ab));
        let b = std::hint::black_box(f32::from_bits(bb));
        let c = std::hint::black_box(f32::from_bits(cb));
        let r_fma = rust_mul_add(a, b, c);
        let r_sep = rust_sep_mul_add(a, b, c);
        let (hw_b, hw_f) = hw_vfmadd213ss(a, b, c);
        if i > 0 { print!(","); }
        print!(
            "{{\"case\":\"{}\",\"rust_mul_add\":\"0x{:08x}\",\"rust_sep_mul_add\":\"0x{:08x}\",\"hw_vfmadd213ss\":\"0x{:08x}\",\"hw_flags\":\"0x{:02x}\"}}",
            name, r_fma, r_sep, hw_b, hw_f
        );
    }
    println!("]}}");
}
''')
        fp_results = {}
        for tc_label, tc_arg in TOOLCHAINS:
            extra_cfg = ["--cfg", "use_nightly_minmax"] if "nightly" in tc_label else []
            for fma_mode, tf in [("baseline_sse2", []), ("target_fma", ["-C", "target-feature=+fma,+avx"])]:
                b_fp = tdp / f"fp_{tc_label}_{fma_mode}"
                s_fp = tdp / f"fp_{tc_label}_{fma_mode}.s"
                run_cmd(["rustc", tc_arg, "--edition=2024", "-C", "opt-level=3", *extra_cfg, *tf, str(fp_probe_src), "-o", str(b_fp)])
                run_cmd(["rustc", tc_arg, "--edition=2024", "-C", "opt-level=3", *extra_cfg, *tf, "--emit=asm", str(fp_probe_src), "-o", str(s_fp)])
                data = json.loads(run_cmd([str(b_fp)]).stdout.strip())
                asm_txt = s_fp.read_text()
                fn_asms = {}
                for fn_n in ["rust_min", "rust_max", "rust_minimum", "rust_mul_add"]:
                    m = re.search(rf"([A-Za-z0-9_$.]*\b\d*{fn_n}\b:\n(?:.*\n){{1,25}}?)\s*\.size", asm_txt)
                    fn_asms[fn_n] = m.group(1).strip() if m else "NOT_FOUND"
                fp_results[f"{tc_label}_{fma_mode}"] = {
                    "data": data,
                    "asm": fn_asms,
                }
        results["fp_minmax_fma_corners"] = fp_results
    return results


def main() -> None:
    all_res = {
        "seam1_nostack_redzone": probe_1_nostack_redzone(),
        "seam2_mxcsr_fastmath_and_fp": probe_2_mxcsr_and_fastmath(),
    }
    out_path = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else None
    rendered = json.dumps(all_res, indent=2)
    if out_path:
        out_path.write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
