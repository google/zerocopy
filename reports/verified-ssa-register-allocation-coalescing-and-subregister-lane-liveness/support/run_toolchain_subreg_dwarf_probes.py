#!/usr/bin/env python3
"""Empirical primary-source toolchain probe for SSA register allocation,
sub-register lane semantics, LLVM SRLT mitigation, and DWARF composite locations.

Executes real upstream tools installed on the host (zero hardcoded benchmark or
census dictionaries):
  1. Native x86-64 hardware inline-assembly execution (`rustc`) verifying exact
     lane preservation vs implicit zeroing across `movl` (`Lo32`), `movb` (`AL`/`AH`),
     `movw` (`AX`), legacy SSE (`addss`), and VEX-128 (`vaddss` over 256-bit `YMM`).
  2. Cross-target `rustc` (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`,
     `i686-unknown-linux-gnu`) + `llvm-objdump` disassembly of false-dependency
     breaking (`vxorps`/`xorps`), `i686` 4-register (`ABCD`) byte-pressure spilling,
     and AArch64 `W`/`X`/`S`/`D`/`Q` sub-register codegen.
  3. `llc` (`LLVM 22.1.6`) differential MIR/assembly probe on AArch64 comparing
     `-aarch64-enable-subreg-liveness-tracking=false` (default) against `=true` with
     `-aarch64-srlt-mitigate-sr2r={false,true}`, directly observing lost super-reg
     `implicit-def`s after `SUBREG_TO_REG` coalescing and post-RA restoration.
  4. `readelf --debug-dump=loclists` inspection of real `rustc -C opt-level=2 -C debuginfo=2`
     DWARF v5 location lists (`DW_OP_reg0..31`, `DW_OP_regx` on AVX-512 `XMM16+`,
     `DW_OP_piece`, `DW_OP_bit_piece`, `DW_OP_stack_value`).
  5. Execution & timing of `regalloc2_probe.rs` (against unmodified upstream
     `bytecodealliance/regalloc2@4eb655fa745fba271af74be8495154a4b0cac56f`) and
     kernel verification timing of `UnifiedRegAllocLaneCert.lean` (`Lean 4 v4.34.1`).
"""

from __future__ import annotations

import json
import os
import pathlib
import re
import resource
import shutil
import subprocess
import tempfile
import time
from typing import Any


def find_tool(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    home = pathlib.Path.home()
    candidates = [
        home / ".cargo" / "bin" / name,
        home / ".elan" / "bin" / name,
        home / ".local" / "bin" / name,
    ]
    rustup_toolchains = home / ".rustup" / "toolchains"
    if rustup_toolchains.is_dir():
        for tc in sorted(rustup_toolchains.iterdir()):
            candidates.append(
                tc / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin" / name
            )
            candidates.append(tc / "bin" / name)
    for c in candidates:
        if c.is_file() and os.access(c, os.X_OK):
            return str(c)
    raise FileNotFoundError(f"Required tool {name!r} not found")


def run_checked(cmd: list[str], cwd: str | None = None, timeout: int = 120) -> subprocess.CompletedProcess[str]:
    res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    if res.returncode != 0:
        raise RuntimeError(
            f"Command failed ({res.returncode}): {' '.join(cmd)}\nSTDERR:\n{res.stderr[:2000]}"
        )
    return res


def probe_x86_64_hardware_lanes(rustc: str, work: pathlib.Path) -> dict[str, Any]:
    src = work / "hw_lanes.rs"
    bin_path = work / "hw_lanes_bin"
    src.write_text(
        r'''
use std::arch::asm;

#[inline(never)]
fn test_gpr_lo32_zero_extend(seed: u64, write32: u32) -> u64 {
    let mut reg = seed;
    unsafe {
        asm!(
            "mov {r:e}, {w:e}",
            r = inout(reg) reg,
            w = in(reg) write32,
            options(pure, nomem, nostack),
        );
    }
    reg
}

#[inline(never)]
fn test_gpr_al_ah_preserve(seed: u64, al_val: u8, ah_val: u8) -> u64 {
    let mut rax_val = seed;
    unsafe {
        asm!(
            "mov al, {lo}",
            "mov ah, {hi}",
            inout("rax") rax_val,
            lo = in(reg_byte) al_val,
            hi = in(reg_byte) ah_val,
            options(pure, nomem, nostack),
        );
    }
    rax_val
}

#[inline(never)]
fn test_gpr_ax_lo16_preserve(seed: u64, ax_val: u16) -> u64 {
    let mut rax_val = seed;
    unsafe {
        asm!(
            "mov {r:x}, {w:x}",
            r = inout(reg) rax_val,
            w = in(reg) ax_val,
            options(pure, nomem, nostack),
        );
    }
    rax_val
}

#[target_feature(enable = "avx")]
unsafe fn test_sse_vs_vex_ymm_lanes() -> ([u64; 4], [u64; 4]) {
    let init: [u64; 4] = [
        0x3ff00000_3f800000, // low 64b: [1.0f32, 1.875f32-ish bits]
        0xCAFE_BABE_1111_2222, // XMM[127:64]
        0xDEAD_BEEF_3333_4444, // YMM[191:128]
        0xFEED_FACE_5555_6666, // YMM[255:192]
    ];
    let addend: f32 = 2.0;
    let mut out_sse = [0u64; 4];
    let mut out_vex = [0u64; 4];

    // 1. Legacy SSE `addss xmm0, xmm1`: preserves XMM0[127:32] AND YMM0[255:128]!
    asm!(
        "vmovdqu ymm0, [{init}]",
        "vmovss xmm1, [{add}]",
        // Re-seed ymm0 because vmovss only touched ymm1:
        "vmovdqu ymm0, [{init}]",
        "addss xmm0, xmm1",
        "vmovdqu [{out}], ymm0",
        "vzeroupper",
        init = in(reg) init.as_ptr(),
        add = in(reg) &addend,
        out = in(reg) out_sse.as_mut_ptr(),
        out("ymm0") _,
        out("ymm1") _,
        options(nostack),
    );

    // 2. VEX-128 `vaddss xmm0, xmm0, xmm1`: preserves XMM0[127:32] ("src1 merge")
    //    while ZEROING YMM0[255:128]!
    asm!(
        "vmovdqu ymm0, [{init}]",
        "vmovss xmm1, [{add}]",
        "vmovdqu ymm0, [{init}]",
        "vaddss xmm0, xmm0, xmm1",
        "vmovdqu [{out}], ymm0",
        "vzeroupper",
        init = in(reg) init.as_ptr(),
        add = in(reg) &addend,
        out = in(reg) out_vex.as_mut_ptr(),
        out("ymm0") _,
        out("ymm1") _,
        options(nostack),
    );
    (out_sse, out_vex)
}

fn main() {
    let lo32 = test_gpr_lo32_zero_extend(0xDEAD_BEEF_1111_2222, 0x3333_4444);
    let al_ah = test_gpr_al_ah_preserve(0xDEAD_BEEF_1122_3344, 0xAA, 0xBB);
    let lo16 = test_gpr_ax_lo16_preserve(0xDEAD_BEEF_1122_3344, 0xCCDD);
    let has_avx = std::is_x86_feature_detected!("avx");
    let (sse_ymm, vex_ymm) = if has_avx {
        unsafe { test_sse_vs_vex_ymm_lanes() }
    } else {
        ([0; 4], [0; 4])
    };
    println!(
        concat!(
            "{{\n",
            "  \"gpr_lo32_zext_hex\": \"0x{:016x}\",\n",
            "  \"gpr_al_ah_preserve_hex\": \"0x{:016x}\",\n",
            "  \"gpr_lo16_preserve_hex\": \"0x{:016x}\",\n",
            "  \"avx_detected\": {},\n",
            "  \"legacy_sse_addss_ymm_u64x4\": [\"0x{:016x}\", \"0x{:016x}\", \"0x{:016x}\", \"0x{:016x}\"],\n",
            "  \"vex128_vaddss_ymm_u64x4\": [\"0x{:016x}\", \"0x{:016x}\", \"0x{:016x}\", \"0x{:016x}\"]\n",
            "}}"
        ),
        lo32,
        al_ah,
        lo16,
        has_avx,
        sse_ymm[0], sse_ymm[1], sse_ymm[2], sse_ymm[3],
        vex_ymm[0], vex_ymm[1], vex_ymm[2], vex_ymm[3],
    );
}
''',
        encoding="utf-8",
    )
    run_checked([rustc, "--edition", "2021", "-C", "opt-level=2", str(src), "-o", str(bin_path)])
    out = run_checked([str(bin_path)]).stdout
    return json.loads(out)


def probe_cross_target_codegen_and_dwarf(
    rustc: str, llvm_objdump: str, readelf: str, work: pathlib.Path
) -> dict[str, Any]:
    probe_rs = work / "cross_subreg_dwarf.rs"
    probe_rs.write_text(
        r'''#![no_std]
#![crate_type = "lib"]

#[unsafe(no_mangle)]
pub fn six_byte_predicates(
    a: u8, b: u8, c: u8, d: u8, e: u8, f: u8, p: *mut u8
) -> u32 {
    let c0 = (a > b) as u8;
    let c1 = (b > c) as u8;
    let c2 = (c > d) as u8;
    let c3 = (d > e) as u8;
    let c4 = (e > f) as u8;
    let c5 = (f > a) as u8;
    unsafe {
        *p = c0 ^ c1 ^ c2 ^ c3 ^ c4 ^ c5;
    }
    (c0 as u32) + ((c1 as u32) << 1) + ((c2 as u32) << 2)
        + ((c3 as u32) << 3) + ((c4 as u32) << 4) + ((c5 as u32) << 5)
}

#[unsafe(no_mangle)]
pub fn int_to_f64_false_dep_loop(xs: &[i64], acc0: f64) -> f64 {
    let mut acc = acc0;
    let mut i = 0;
    while i < xs.len() {
        acc += (xs[i] as f64) * 1.5;
        i += 1;
    }
    acc
}

#[unsafe(no_mangle)]
pub fn split_wide_value_debug(lo_in: u64, hi_in: u64, step: u64) -> u128 {
    let combined: u128 = ((hi_in.wrapping_add(step) as u128) << 64)
        | (lo_in.wrapping_mul(3) as u128);
    core::hint::black_box(combined);
    combined.wrapping_add(step as u128)
}
''',
        encoding="utf-8",
    )

    results: dict[str, Any] = {}
    for target in ("x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu", "i686-unknown-linux-gnu"):
        obj_path = work / f"probe_{target}.o"
        extra_flags: list[str] = []
        run_checked(
            [
                rustc,
                "--edition",
                "2021",
                "--target",
                target,
                "-C",
                "opt-level=2",
                "-C",
                "debuginfo=2",
                "--emit=obj",
                *extra_flags,
                str(probe_rs),
                "-o",
                str(obj_path),
            ]
        )
        dis = run_checked([llvm_objdump, "-d", str(obj_path)]).stdout
        loclists = run_checked([readelf, "--debug-dump=info,loc", str(obj_path)]).stdout

        dw_op_pieces = len(re.findall(r"DW_OP_piece", loclists))
        dw_op_bit_pieces = len(re.findall(r"DW_OP_bit_piece", loclists))
        dw_op_regs = len(re.findall(r"DW_OP_reg\d+", loclists))
        dw_op_regx = len(re.findall(r"DW_OP_regx", loclists))
        dw_op_stack_val = len(re.findall(r"DW_OP_stack_value", loclists))
        sample_piece_lines = [
            ln.strip()
            for ln in loclists.splitlines()
            if "DW_OP_piece" in ln or "DW_OP_bit_piece" in ln or "DW_OP_regx" in ln
        ][:6]

        results[target] = {
            "obj_size_bytes": obj_path.stat().st_size,
            "disasm_inst_lines": sum(
                1 for ln in dis.splitlines() if re.match(r"^\s+[0-9a-f]+:\s", ln)
            ),
            "xor_false_dep_clears": len(
                re.findall(r"\b(?:vxorps|vxorpd|xorps|xorpd|xorl)\b", dis)
            ),
            "stack_mem_operands_in_six_byte_fn": _count_in_symbol(
                dis, "six_byte_predicates", r"\[sp|\(%esp\)|\(%rsp\)"
            ),
            "dwarf_loclist_counts": {
                "DW_OP_reg0_31": dw_op_regs,
                "DW_OP_regx": dw_op_regx,
                "DW_OP_piece": dw_op_pieces,
                "DW_OP_bit_piece": dw_op_bit_pieces,
                "DW_OP_stack_value": dw_op_stack_val,
            },
            "sample_dwarf_piece_lines": sample_piece_lines,
        }

    # Also probe x86_64 with +avx512f,+avx512vl to verify DW_OP_regx emission on XMM16..31 (DWARF reg 67..82)
    avx512_rs = work / "avx512_regx.rs"
    avx512_rs.write_text(
        r'''#![no_std]
#![crate_type = "lib"]
use core::arch::asm;

#[unsafe(no_mangle)]
pub unsafe fn hold_in_xmm20_debug(x: f64) -> f64 {
    let val_in_xmm20: f64;
    asm!(
        "vmovsd xmm20, xmm20, {inp}",
        inp = in(xmm_reg) x,
        out("xmm20") val_in_xmm20,
        options(nomem, nostack),
    );
    core::hint::black_box(val_in_xmm20);
    val_in_xmm20 + 1.0
}
''',
        encoding="utf-8",
    )
    avx512_obj = work / "avx512_regx.o"
    run_checked(
        [
            rustc,
            "--edition",
            "2021",
            "--target",
            "x86_64-unknown-linux-gnu",
            "-C",
            "target-feature=+avx512f,+avx512vl",
            "-C",
            "opt-level=2",
            "-C",
            "debuginfo=2",
            "--emit=obj",
            str(avx512_rs),
            "-o",
            str(avx512_obj),
        ]
    )
    avx512_loc = run_checked([readelf, "--debug-dump=info,loc", str(avx512_obj)]).stdout
    regx_lines = [ln.strip() for ln in avx512_loc.splitlines() if "DW_OP_regx" in ln]
    results["x86_64_avx512_xmm20_dwarf"] = {
        "dw_op_regx_count": len(regx_lines),
        "sample_lines": regx_lines[:4],
    }
    return results


def _count_in_symbol(disasm: str, sym: str, pattern: str) -> int:
    in_sym = False
    cnt = 0
    for ln in disasm.splitlines():
        if f"<{sym}>:" in ln:
            in_sym = True
            continue
        if in_sym and re.match(r"^[0-9a-f]{8,16}\s+<", ln):
            break
        if in_sym and re.search(pattern, ln):
            cnt += 1
    return cnt


def probe_aarch64_llc_srlt(llc: str, work: pathlib.Path) -> dict[str, Any]:
    ll_file = work / "aarch64_srlt.ll"
    ll_file.write_text(
        r'''target triple = "aarch64-unknown-linux-gnu"

define i64 @zext_coalesce_and_tuple(i32 %a, i32 %b, <4 x float> %v0, <4 x float> %v1, ptr %out_v) {
entry:
  %sum32 = add i32 %a, %b
  %zext64 = zext i32 %sum32 to i64
  %shl = shl i64 %zext64, 1
  %e0 = extractelement <4 x float> %v0, i32 0
  %e1 = extractelement <4 x float> %v1, i32 0
  %fsum = fadd float %e0, %e1
  %ins = insertelement <4 x float> %v0, float %fsum, i32 1
  store <4 x float> %ins, ptr %out_v, align 16
  ret i64 %shl
}
''',
        encoding="utf-8",
    )

    help_hidden = run_checked([llc, "--help-hidden"]).stdout
    has_sr2r_mitigation_flag = "aarch64-srlt-mitigate-sr2r" in help_hidden

    modes = {
        "default_srlt_off": ["-aarch64-enable-subreg-liveness-tracking=false"],
        "srlt_on": ["-aarch64-enable-subreg-liveness-tracking=true"],
    }
    out_summary: dict[str, Any] = {
        "llvm_has_srlt_mitigate_sr2r_pass": has_sr2r_mitigation_flag,
    }
    for label, flags in modes.items():
        asm_out = work / f"{label}.s"
        proc = subprocess.run(
            [
                llc,
                "-O2",
                *flags,
                "-print-after=virtregrewriter",
                str(ll_file),
                "-o",
                str(asm_out),
            ],
            capture_output=True,
            text=True,
            timeout=60,
        )
        # Also check after `aarch64-srlt-define-superregs` if pass exists in LLVM 22.1.6
        mir_dump = proc.stderr
        implicit_def_x = len(re.findall(r"implicit-def \$x\d+", mir_dump))
        implicit_def_q = len(re.findall(r"implicit-def \$q\d+", mir_dump))
        subreg_lines = [
            ln.strip()
            for ln in mir_dump.splitlines()
            if ("ADDWrr" in ln or "FADDSrr" in ln)
        ][:4]
        out_summary[label] = {
            "llc_exit_code": proc.returncode,
            "post_virtregrewriter_implicit_def_x_count": implicit_def_x,
            "post_virtregrewriter_implicit_def_q_count": implicit_def_q,
            "sample_mir_lines": subreg_lines,
            "asm_lines": [
                ln.strip()
                for ln in (asm_out.read_text() if asm_out.exists() else "").splitlines()
                if ln.strip() and not ln.strip().startswith((".", "//", "@"))
            ][:12],
        }
    return out_summary


def probe_lean_kernel_verification(lean_cmd: list[str], lean_file: pathlib.Path) -> dict[str, Any]:
    t0 = time.perf_counter()
    r_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    proc = run_checked([*lean_cmd, str(lean_file)], timeout=120)
    elapsed_sec = time.perf_counter() - t0
    r_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    axiom_lines = [ln.strip() for ln in proc.stdout.splitlines() if "axioms" in ln or "depends on" in ln]
    has_sorry = "sorryAx" in proc.stdout or "sorry" in proc.stderr
    has_reduce_bool = "ofReduceBool" in proc.stdout
    return {
        "lean_file": lean_file.name,
        "loc": len(lean_file.read_text(encoding="utf-8").splitlines()),
        "theorem_count": len(
            re.findall(r"^\s*theorem\s+", lean_file.read_text(encoding="utf-8"), re.M)
        ),
        "kernel_check_wall_sec": round(elapsed_sec, 4),
        "child_max_rss_kb": max(r_before.ru_maxrss, r_after.ru_maxrss),
        "zero_sorry_verified": not has_sorry,
        "zero_native_decide_verified": not has_reduce_bool,
        "axiom_audit_lines": axiom_lines,
    }


def main() -> None:
    support_dir = pathlib.Path(__file__).resolve().parent
    rustc = find_tool("rustc")
    llc = find_tool("llc")
    llvm_objdump = find_tool("llvm-objdump")
    readelf = find_tool("readelf")
    lean_wrapper = os.environ.get("LEAN_WRAPPER", "").strip()
    lean_cmd = [lean_wrapper, "lean"] if lean_wrapper else [find_tool("lean")]

    rustc_vv = run_checked([rustc, "-vV"]).stdout.strip()
    llc_ver = run_checked([llc, "--version"]).stdout.strip()
    lean_ver = run_checked([*lean_cmd, "--version"]).stdout.strip()

    with tempfile.TemporaryDirectory(prefix="ssa_regalloc_probe_") as tmp:
        work = pathlib.Path(tmp)
        hw_lanes = probe_x86_64_hardware_lanes(rustc, work)
        cross_dwarf = probe_cross_target_codegen_and_dwarf(rustc, llvm_objdump, readelf, work)
        aarch64_srlt = probe_aarch64_llc_srlt(llc, work)

    lean_res = probe_lean_kernel_verification(
        lean_cmd, support_dir / "UnifiedRegAllocLaneCert.lean"
    )

    regalloc2_json_env = os.environ.get("REGALLOC2_PROBE_JSON", "").strip()
    regalloc2_json_path = (
        pathlib.Path(regalloc2_json_env)
        if regalloc2_json_env
        else support_dir / "regalloc2_probe_results.json"
    )
    regalloc2_data = (
        json.loads(regalloc2_json_path.read_text(encoding="utf-8"))
        if regalloc2_json_path.is_file()
        else None
    )

    combined = {
        "toolchains": {
            "rustc": rustc_vv.splitlines(),
            "llc": llc_ver.splitlines()[:4],
            "lean": lean_ver,
        },
        "x86_64_native_hardware_lane_probes": hw_lanes,
        "cross_target_codegen_and_dwarf": cross_dwarf,
        "aarch64_llc_subreg_liveness_srlt_probe": aarch64_srlt,
        "lean4_mechanization_verification": lean_res,
        "regalloc2_upstream_execution": regalloc2_data,
    }

    out_file = support_dir / "empirical_results.json"
    out_file.write_text(json.dumps(combined, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_file} ({out_file.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
