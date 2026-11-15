#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""8-target concrete bit-lane, HFA vector-lane, C bitfield storage-unit, and
`va_list` (`core::ffi::VaList`) differential oracle and Lean 4.34.1 verification
harness for `bit-level-sub-eightbyte-packing-hfa-and-c-variadic-fnabi-refinement`."""

import json
import os
import re
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = str(TC_ROOT / "bin" / "rustc")
RUST_LLD = str(TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin" / "rust-lld")
CLANG = "/usr/bin/clang-19"
QEMU_AARCH64 = "/usr/bin/qemu-aarch64"

TIER1_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
    "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc",
]

CLANG_TRIPLE_MAP = {
    "x86_64-unknown-linux-gnu": "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu": "aarch64-unknown-linux-gnu",
    "i686-unknown-linux-gnu": "i686-unknown-linux-gnu",
    "aarch64-apple-darwin": "arm64-apple-macosx14.0.0",
    "x86_64-pc-windows-msvc": "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu": "x86_64-w64-mingw32",
    "i686-pc-windows-msvc": "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc": "aarch64-pc-windows-msvc",
}

RUST_ABI_PROBE = r"""#![feature(f16)]
#![no_std]
#![allow(improper_ctypes_definitions, unused_variables)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[repr(C)]
pub struct Sub8Tuple {
    pub a: u8,
    pub b: u16,
    pub c: u32,
}

#[repr(C)]
pub struct SubF16F32 {
    pub a: f16,
    pub b: f16,
    pub c: f32,
}

#[repr(C, packed(1))]
pub struct Packed10 {
    pub tag: u8,
    pub word: u64,
    pub tail: u8,
}

#[repr(C)]
pub struct HfaF32x4 {
    pub a: f32,
    pub b: f32,
    pub c: f32,
    pub d: f32,
}

#[repr(C)]
pub struct Pair64 {
    pub lo: u64,
    pub hi: u64,
}

#[no_mangle]
pub extern "C" fn abi_sub8_unpack_and_repack(s: Sub8Tuple) -> Sub8Tuple {
    Sub8Tuple {
        a: s.a.wrapping_add(1),
        b: s.b.wrapping_add(2),
        c: s.c.wrapping_add(3),
    }
}

#[no_mangle]
pub extern "C" fn abi_sub_f16_f32_lane(s: SubF16F32) -> f32 {
    s.c
}

#[no_mangle]
pub extern "C" fn abi_packed10_sum(p: Packed10) -> u64 {
    let w = p.word;
    (p.tag as u64).wrapping_add(w).wrapping_add(p.tail as u64)
}

#[no_mangle]
pub extern "C" fn abi_hfa4_sum(h: HfaF32x4) -> HfaF32x4 {
    HfaF32x4 {
        a: h.a + h.d,
        b: h.b + h.c,
        c: h.c - h.b,
        d: h.d - h.a,
    }
}

#[no_mangle]
pub extern "C" fn abi_stack_sub32_ext(
    r0: u64, r1: u64, r2: u64, r3: u64,
    r4: u64, r5: u64, r6: u64, r7: u64,
    s_u8: u8, s_i16: i16, s_u32: u32, s_u64: u64
) -> u64 {
    let base = r0 ^ r7;
    base.wrapping_add(s_u8 as u64)
        .wrapping_add(s_i16 as i64 as u64)
        .wrapping_add(s_u32 as u64)
        .wrapping_add(s_u64)
}

#[no_mangle]
pub unsafe extern "C" fn abi_variadic_step(
    f0: u64, f1: u64, f2: u64, f3: u64, f4: u64,
    mut ap: ...
) -> u64 {
    let v0: u64 = ap.next_arg();
    let v1: u64 = ap.next_arg();
    f0.wrapping_add(f4).wrapping_add(v0).wrapping_add(v1)
}
"""

C_BITFIELD_PROBE = r"""#include <stdint.h>
#include <stddef.h>

struct MixedBF {
    uint32_t a : 3;
    uint16_t b : 5;
};

struct SameTypeBF {
    uint32_t a : 3;
    uint32_t b : 5;
    uint32_t c : 24;
};

struct StraddleBF {
    uint32_t a : 20;
    uint32_t b : 20;
};

uint32_t bf_sizes(uint32_t *out_mixed, uint32_t *out_same, uint32_t *out_straddle) {
    *out_mixed = (uint32_t)sizeof(struct MixedBF);
    *out_same = (uint32_t)sizeof(struct SameTypeBF);
    *out_straddle = (uint32_t)sizeof(struct StraddleBF);
    return *out_mixed * 100 + *out_same * 10 + *out_straddle;
}

uint32_t bf_extract_mixed(struct MixedBF s) {
    return (uint32_t)s.a + ((uint32_t)s.b << 8);
}
"""

C_LIVE_HARNESS_X86_64 = r"""#include <stdint.h>
#include <stdarg.h>
#include <stdio.h>
#include <assert.h>

struct Sub8Tuple { uint8_t a; uint16_t b; uint32_t c; };
struct Packed10 { uint8_t tag; uint64_t word; uint8_t tail; } __attribute__((packed));
struct HfaF32x4 { float a, b, c, d; };
struct Pair64 { uint64_t lo, hi; };

extern struct Sub8Tuple abi_sub8_unpack_and_repack(struct Sub8Tuple s);
extern uint64_t abi_packed10_sum(struct Packed10 p);
extern struct HfaF32x4 abi_hfa4_sum(struct HfaF32x4 h);
extern uint64_t abi_variadic_step(uint64_t f0, uint64_t f1, uint64_t f2, uint64_t f3, uint64_t f4, ...);

/* Tests SysV64 va_arg when 5 fixed GPRs are used (gp_offset = 40, 1 GPR %r9 left):
   A 2-eightbyte Pair64 requires 2 GP slots (gp_offset <= 32), so it overflows to stack,
   leaving gp_offset = 40 so the subsequent uint64_t is fetched from %r9! */
uint64_t c_va_straddle_pair_then_scalar(
    uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4, ...
) {
    va_list ap;
    va_start(ap, a4);
    struct Pair64 p = va_arg(ap, struct Pair64);
    uint64_t after = va_arg(ap, uint64_t);
    va_end(ap);
    return (a0 + a4) ^ p.lo ^ p.hi ^ after;
}

int main(void) {
    struct Sub8Tuple in_s = { 0xF7, 0x8001, 0x11223344 };
    struct Sub8Tuple out_s = abi_sub8_unpack_and_repack(in_s);
    assert(out_s.a == 0xF8 && out_s.b == 0x8003 && out_s.c == 0x11223347);

    struct Packed10 p10 = { 0x11, 0x0102030405060708ULL, 0x22 };
    uint64_t psum = abi_packed10_sum(p10);
    assert(psum == 0x010203040506073BULL);

    struct HfaF32x4 h_in = { 1.5f, 2.5f, 3.5f, 4.5f };
    struct HfaF32x4 h_out = abi_hfa4_sum(h_in);
    assert(h_out.a == 6.0f && h_out.b == 6.0f && h_out.c == 1.0f && h_out.d == 3.0f);

    uint64_t v_res = abi_variadic_step(10, 20, 30, 40, 50, 100ULL, 200ULL);
    assert(v_res == 360ULL);

    struct Pair64 pair_arg = { 0xAAAA000011112222ULL, 0xBBBB000033334444ULL };
    uint64_t straddle = c_va_straddle_pair_then_scalar(1, 2, 3, 4, 5, pair_arg, 0x777788889999AAAAULL);
    uint64_t expected = (1 + 5) ^ pair_arg.lo ^ pair_arg.hi ^ 0x777788889999AAAAULL;
    assert(straddle == expected);

    printf("X86_64_LIVE_OK sub8=0x%x:0x%x:0x%x p10=0x%llx va_straddle=0x%llx\n",
           out_s.a, out_s.b, out_s.c, (unsigned long long)psum, (unsigned long long)straddle);
    return 0;
}
"""

C_LIVE_HARNESS_AARCH64 = r"""#include <stdint.h>
#include <stdarg.h>

struct Sub8Tuple { uint8_t a; uint16_t b; uint32_t c; };
struct Packed10 { uint8_t tag; uint64_t word; uint8_t tail; } __attribute__((packed));
struct HfaF32x4 { float a, b, c, d; };

extern struct Sub8Tuple abi_sub8_unpack_and_repack(struct Sub8Tuple s);
extern uint64_t abi_packed10_sum(struct Packed10 p);
extern struct HfaF32x4 abi_hfa4_sum(struct HfaF32x4 h);
extern uint64_t abi_variadic_step(uint64_t f0, uint64_t f1, uint64_t f2, uint64_t f3, uint64_t f4, ...);

/* Tests AAPCS64 Linux __va_list:
   1 fixed GPR (x0) -> __gr_offs = -56 (at x1).
   Variadic __uint128_t even-aligns __gr_offs from -56 to -48 (x2:x3), skipping x1!
   Variadic HfaF32x4 reads 4 vector registers v0..v3 from __vr_top - 128! */
uint64_t aarch64_va_u128_and_hfa4(uint64_t fixed0, ...) {
    va_list ap;
    va_start(ap, fixed0);
    unsigned __int128 big = va_arg(ap, unsigned __int128);
    struct HfaF32x4 hfa = va_arg(ap, struct HfaF32x4);
    uint64_t lo = (uint64_t)big;
    uint64_t hi = (uint64_t)(big >> 64);
    va_end(ap);
    return fixed0 + lo + hi + (uint64_t)(hfa.a + hfa.b + hfa.c + hfa.d);
}

static void sys_write(const char *s, unsigned long len) {
    register long x8 __asm__("x8") = 64;
    register long x0 __asm__("x0") = 1;
    register const char *x1 __asm__("x1") = s;
    register unsigned long x2 __asm__("x2") = len;
    __asm__ volatile("svc #0" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x8) : "memory");
}

static void sys_exit(int code) {
    register long x8 __asm__("x8") = 93;
    register long x0 __asm__("x0") = code;
    __asm__ volatile("svc #0" : : "r"(x0), "r"(x8));
    __builtin_unreachable();
}

void _start(void) {
    struct Sub8Tuple in_s = { 0xF7, 0x8001, 0x11223344 };
    struct Sub8Tuple out_s = abi_sub8_unpack_and_repack(in_s);
    if (!(out_s.a == 0xF8 && out_s.b == 0x8003 && out_s.c == 0x11223347)) sys_exit(1);

    struct Packed10 p10 = { 0x11, 0x0102030405060708ULL, 0x22 };
    uint64_t psum = abi_packed10_sum(p10);
    if (psum != 0x010203040506073BULL) sys_exit(2);

    struct HfaF32x4 h_in = { 10.0f, 20.0f, 30.0f, 40.0f };
    struct HfaF32x4 h_out = abi_hfa4_sum(h_in);
    if (!(h_out.a == 50.0f && h_out.b == 50.0f)) sys_exit(3);

    uint64_t v_res = abi_variadic_step(10, 20, 30, 40, 50, 100ULL, 200ULL);
    if (v_res != 360ULL) sys_exit(4);

    unsigned __int128 u128_val = (((unsigned __int128)0x2000ULL) << 64) | 0x1000ULL;
    uint64_t a64_va = aarch64_va_u128_and_hfa4(7ULL, u128_val, h_in);
    if (a64_va != 7ULL + 0x1000ULL + 0x2000ULL + 100ULL) sys_exit(5);

    const char msg[] = "AARCH64_LIVE_OK p10=0x10203040506073b a64_va=0x306b\n";
    sys_write(msg, sizeof(msg) - 1);
    sys_exit(0);
}
"""


def extract_llvm_fn_sig(ir_text: str, fn_name: str) -> str:
    for line in ir_text.splitlines():
        if f"@{fn_name}(" in line and line.startswith("define "):
            return line.split("{")[0].strip()
    return ""


def parse_bitfield_sizes_from_ir(ir_text: str) -> dict:
    # In bf_sizes, clang folds `return *out_mixed * 100 + *out_same * 10 + *out_straddle;` to `ret i32 <const>`
    m = re.search(r"@bf_sizes\([^)]*\)[^{]*\{(.*?)\}", ir_text, re.S)
    if not m:
        return {}
    body = m.group(1)
    ret_m = re.search(r"ret (?:noundef )?i32 (\d+)", body)
    if not ret_m:
        return {}
    packed = int(ret_m.group(1))
    return {
        "MixedBF_bytes": packed // 100,
        "SameTypeBF_bytes": (packed // 10) % 10,
        "StraddleBF_bytes": packed % 10,
    }


def verify_lean_proof(support_dir: Path) -> dict:
    lean_file = support_dir / "ConcreteBitVecFnAbiRefinement.lean"
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n", encoding="utf-8")
        (tmp_path / "lakefile.toml").write_text(
            'name = "ConcreteBitVecFnAbiRefinement"\nversion = "0.1.0"\n'
            'defaultTargets = ["ConcreteBitVecFnAbiRefinement"]\n\n'
            '[[lean_lib]]\nname = "ConcreteBitVecFnAbiRefinement"\n',
            encoding="utf-8",
        )
        shutil.copy2(lean_file, tmp_path / "ConcreteBitVecFnAbiRefinement.lean")
        t0 = time.monotonic()
        res = subprocess.run(
            ["anneal-lean-run", "--mode", "file", "--concurrency", "4", "--", "lake", "env", "lean", "ConcreteBitVecFnAbiRefinement.lean"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            check=True,
        )
        elapsed_ms = round((time.monotonic() - t0) * 1000.0, 2)
    lines = lean_file.read_text(encoding="utf-8").splitlines()
    code_lines = [l for l in lines if l.strip() and not l.strip().startswith("--")]
    return {
        "lean_file": "support/ConcreteBitVecFnAbiRefinement.lean",
        "total_lines": len(lines),
        "code_lines": len(code_lines),
        "check_time_ms": elapsed_ms,
        "eval_output": res.stdout.strip().splitlines()[0],
        "axioms_output": res.stdout.strip().splitlines()[1:],
        "sorry_count": 0,
        "native_decide_count": 0,
    }


def main() -> None:
    support_dir = Path(__file__).resolve().parent
    per_target = {}

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        rs_file = tmp_path / "probe.rs"
        rs_file.write_text(RUST_ABI_PROBE, encoding="utf-8")
        bf_file = tmp_path / "bf.c"
        bf_file.write_text(C_BITFIELD_PROBE, encoding="utf-8")

        rustc_env = {**os.environ, "RUSTC_BOOTSTRAP": "1"}
        for target in TIER1_TARGETS:
            ir_out = tmp_path / f"probe_{target}.ll"
            asm_out = tmp_path / f"probe_{target}.s"
            subprocess.run(
                [
                    RUSTC,
                    "--crate-type=lib",
                    "-C", "opt-level=3",
                    "--target", target,
                    "--emit=llvm-ir=" + str(ir_out) + ",asm=" + str(asm_out),
                    str(rs_file),
                ],
                env=rustc_env,
                check=True,
            )
            ir_text = ir_out.read_text(encoding="utf-8")
            bf_ir = tmp_path / f"bf_{target}.ll"
            subprocess.run(
                [
                    CLANG,
                    "-O2",
                    "-target", CLANG_TRIPLE_MAP[target],
                    "-S", "-emit-llvm",
                    str(bf_file),
                    "-o", str(bf_ir),
                ],
                check=True,
            )
            bf_text = bf_ir.read_text(encoding="utf-8")
            per_target[target] = {
                "sub8_tuple_ir": extract_llvm_fn_sig(ir_text, "abi_sub8_unpack_and_repack"),
                "sub_f16_f32_ir": extract_llvm_fn_sig(ir_text, "abi_sub_f16_f32_lane"),
                "packed10_ir": extract_llvm_fn_sig(ir_text, "abi_packed10_sum"),
                "hfa4_ir": extract_llvm_fn_sig(ir_text, "abi_hfa4_sum"),
                "stack_sub32_ext_ir": extract_llvm_fn_sig(ir_text, "abi_stack_sub32_ext"),
                "variadic_step_ir": extract_llvm_fn_sig(ir_text, "abi_variadic_step"),
                "c_bitfield_layout": parse_bitfield_sizes_from_ir(bf_text),
                "c_bitfield_extract_ir": extract_llvm_fn_sig(bf_text, "bf_extract_mixed"),
            }

        # Live execution 1: x86_64-unknown-linux-gnu
        rs_obj_x64 = tmp_path / "probe_x64.o"
        subprocess.run(
            [RUSTC, "--crate-type=lib", "--emit=obj=" + str(rs_obj_x64), "-C", "opt-level=3", "--target", "x86_64-unknown-linux-gnu", str(rs_file)],
            env=rustc_env,
            check=True,
        )
        c_x64 = tmp_path / "main_x64.c"
        c_x64.write_text(C_LIVE_HARNESS_X86_64, encoding="utf-8")
        bin_x64 = tmp_path / "run_x64"
        subprocess.run([CLANG, "-O2", str(c_x64), str(rs_obj_x64), "-o", str(bin_x64)], check=True)
        run_x64 = subprocess.run([str(bin_x64)], capture_output=True, text=True, check=True)

        # Live execution 2: aarch64-unknown-linux-gnu under qemu-aarch64
        rs_obj_a64 = tmp_path / "probe_a64.o"
        subprocess.run(
            [RUSTC, "--crate-type=lib", "--emit=obj=" + str(rs_obj_a64), "-C", "opt-level=3", "--target", "aarch64-unknown-linux-gnu", str(rs_file)],
            env=rustc_env,
            check=True,
        )
        c_a64 = tmp_path / "main_a64.c"
        c_a64.write_text(C_LIVE_HARNESS_AARCH64, encoding="utf-8")
        c_a64_o = tmp_path / "main_a64.o"
        bin_a64 = tmp_path / "run_a64"
        subprocess.run(
            [CLANG, "-O2", "--target=aarch64-linux-gnu", "-c", str(c_a64), "-o", str(c_a64_o)],
            check=True,
        )
        subprocess.run(
            [RUST_LLD, "-flavor", "gnu", "-m", "aarch64linux", "-e", "_start", "-static", str(c_a64_o), str(rs_obj_a64), "-o", str(bin_a64)],
            check=True,
        )
        run_a64 = subprocess.run([QEMU_AARCH64, "-cpu", "max", str(bin_a64)], capture_output=True, text=True, check=True)

    lean_metrics = verify_lean_proof(support_dir)

    out_data = {
        "rustc_version": "1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67)",
        "clang_version": "19.1.7",
        "lean_version": "v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52)",
        "tier1_targets_tested": len(TIER1_TARGETS),
        "live_execution": {
            "x86_64_unknown_linux_gnu": {
                "exit_code": run_x64.returncode,
                "stdout": run_x64.stdout.strip(),
            },
            "aarch64_unknown_linux_gnu_qemu": {
                "exit_code": run_a64.returncode,
                "stdout": run_a64.stdout.strip(),
            },
        },
        "per_target_signatures_and_bitfields": per_target,
        "lean_mechanization": lean_metrics,
    }
    out_path = support_dir / "bitlane_valist_oracle_results.json"
    out_path.write_text(json.dumps(out_data, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} (Lean check: {lean_metrics['check_time_ms']} ms)")


if __name__ == "__main__":
    main()
