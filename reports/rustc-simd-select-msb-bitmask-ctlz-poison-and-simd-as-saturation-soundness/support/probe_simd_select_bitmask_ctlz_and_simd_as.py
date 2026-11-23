#!/usr/bin/env python3
"""Differential execution probe for rustc LLVM-IR lowering vs. Miri UB across:
  (A) ctlz/cttz vs. ctlz_nonzero/cttz_nonzero vs. simd_ctlz/simd_cttz
  (B) simd_select MSB lowering vs. Miri {0, -1} validity, simd_select_bitmask LE packing,
      simd_bitmask, simd_shuffle, and simd_reduce_{all,any}
  (C) simd_as saturating float-to-int vs. simd_cast and scalar float_to_int_unchecked
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

RUSTC_ENV = {
    **os.environ,
    "PATH": f"{Path.home() / '.cargo' / 'bin'}:{os.environ.get('PATH', '')}",
}

PROBE_A_RS = r"""#![feature(repr_simd, core_intrinsics)]
#![allow(internal_features)]
use core::hint::black_box;
use core::intrinsics::{ctlz, ctlz_nonzero, cttz, cttz_nonzero};
use core::intrinsics::simd::{simd_ctlz, simd_cttz, simd_extract};

#[repr(simd)]
#[derive(Copy, Clone)]
struct U32x4([u32; 4]);

#[inline(never)]
unsafe fn unpack_u32x4(v: U32x4) -> [u32; 4] {
    unsafe { [simd_extract(v, 0), simd_extract(v, 1), simd_extract(v, 2), simd_extract(v, 3)] }
}

#[inline(never)]
unsafe fn call_ctlz_nonzero(x: u32) -> u32 {
    unsafe { ctlz_nonzero(x) }
}

#[inline(never)]
unsafe fn call_cttz_nonzero(x: u32) -> u32 {
    unsafe { cttz_nonzero(x) }
}

#[inline(never)]
fn call_ctlz(x: u32) -> u32 {
    ctlz(x)
}

#[inline(never)]
fn call_cttz(x: u32) -> u32 {
    cttz(x)
}

#[inline(never)]
unsafe fn call_simd_ctlz(v: U32x4) -> U32x4 {
    unsafe { simd_ctlz(v) }
}

#[inline(never)]
unsafe fn call_simd_cttz(v: U32x4) -> U32x4 {
    unsafe { simd_cttz(v) }
}

#[inline(never)]
unsafe fn fold_ctlz_nonzero_lt32(x: u32) -> u32 {
    let n = unsafe { ctlz_nonzero(x) };
    if n < 32 { n.wrapping_add(1000) } else { 9999 }
}

#[inline(never)]
fn fold_ctlz_safe_lt32(x: u32) -> u32 {
    let n = ctlz(x);
    if n < 32 { n.wrapping_add(1000) } else { 9999 }
}

fn main() {
    let arg = std::env::args().nth(1).unwrap_or_else(|| "safe".to_string());
    let s_ctlz = call_ctlz(black_box(0));
    let s_ctlz_nz = unsafe { call_ctlz_nonzero(black_box(0x0001_ffff)) };
    let s_cttz = call_cttz(black_box(0));
    let s_cttz_nz = unsafe { call_cttz_nonzero(black_box(0x0001_0000)) };
    let v_ctlz = unsafe { call_simd_ctlz(black_box(U32x4([0, 1, 0x8000_0000, 0x0001_0000]))) };
    let v_cttz = unsafe { call_simd_cttz(black_box(U32x4([0, 1, 0x8000_0000, 0x0001_0000]))) };
    let safe_lt32_at_0 = fold_ctlz_safe_lt32(black_box(0));
    println!(
        "SAFE_CTLZ={s_ctlz} SAFE_CTLZ_NZ={s_ctlz_nz} SAFE_CTTZ={s_cttz} SAFE_CTTZ_NZ={s_cttz_nz} SIMD_CTLZ={:?} SIMD_CTTZ={:?} SAFE_LT32_AT_0={safe_lt32_at_0}",
        unsafe { unpack_u32x4(v_ctlz) }, unsafe { unpack_u32x4(v_cttz) }
    );
    match arg.as_str() {
        "safe" => {}
        "ctlz_zero" => {
            let v = unsafe { call_ctlz_nonzero(black_box(0)) };
            let folded = unsafe { fold_ctlz_nonzero_lt32(black_box(0)) };
            println!("CTLZ_ZERO={v} FOLDED_LT32={folded}");
        }
        "cttz_zero" => {
            let v = unsafe { call_cttz_nonzero(black_box(0)) };
            println!("CTTZ_ZERO={v}");
        }
        other => panic!("unknown mode: {other}"),
    }
}
"""

PROBE_B_RS = r"""#![feature(repr_simd, core_intrinsics)]
#![allow(internal_features)]
use core::hint::black_box;
use core::intrinsics::simd::{
    simd_bitmask, simd_extract, simd_reduce_all, simd_reduce_any, simd_select, simd_select_bitmask,
    simd_shuffle,
};

#[repr(simd)]
#[derive(Copy, Clone)]
struct I32x4([i32; 4]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct I8x16([i8; 16]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct U8x16([u8; 16]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct U8x10([u8; 10]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct U32x4([u32; 4]);

#[inline(never)]
unsafe fn unpack_i32x4(v: I32x4) -> [i32; 4] {
    unsafe { [simd_extract(v, 0), simd_extract(v, 1), simd_extract(v, 2), simd_extract(v, 3)] }
}

#[inline(never)]
unsafe fn unpack_u8x16(v: U8x16) -> [u8; 16] {
    unsafe {
        [
            simd_extract(v, 0), simd_extract(v, 1), simd_extract(v, 2), simd_extract(v, 3),
            simd_extract(v, 4), simd_extract(v, 5), simd_extract(v, 6), simd_extract(v, 7),
            simd_extract(v, 8), simd_extract(v, 9), simd_extract(v, 10), simd_extract(v, 11),
            simd_extract(v, 12), simd_extract(v, 13), simd_extract(v, 14), simd_extract(v, 15),
        ]
    }
}

#[inline(never)]
unsafe fn unpack_u8x10(v: U8x10) -> [u8; 10] {
    unsafe {
        [
            simd_extract(v, 0), simd_extract(v, 1), simd_extract(v, 2), simd_extract(v, 3),
            simd_extract(v, 4), simd_extract(v, 5), simd_extract(v, 6), simd_extract(v, 7),
            simd_extract(v, 8), simd_extract(v, 9),
        ]
    }
}

#[inline(never)]
unsafe fn do_simd_select(mask: I32x4, a: I32x4, b: I32x4) -> I32x4 {
    unsafe { simd_select(mask, a, b) }
}

#[inline(never)]
unsafe fn do_simd_select_bitmask_u8(mask: u8, a: I32x4, b: I32x4) -> I32x4 {
    unsafe { simd_select_bitmask(mask, a, b) }
}

#[inline(never)]
unsafe fn do_simd_select_bitmask_arr2(mask: [u8; 2], a: U8x16, b: U8x16) -> U8x16 {
    unsafe { simd_select_bitmask(mask, a, b) }
}

#[inline(never)]
unsafe fn do_simd_select_bitmask_arr2_len10(mask: [u8; 2], a: U8x10, b: U8x10) -> U8x10 {
    unsafe { simd_select_bitmask(mask, a, b) }
}

#[inline(never)]
unsafe fn do_simd_bitmask_arr2(mask: I8x16) -> [u8; 2] {
    unsafe { simd_bitmask(mask) }
}

#[inline(never)]
unsafe fn do_simd_bitmask_u16(mask: I8x16) -> u16 {
    unsafe { simd_bitmask(mask) }
}

#[inline(never)]
unsafe fn do_shuffle_and_reduce(a: I32x4, b: I32x4, mask: I32x4) -> (I32x4, bool, bool, u8) {
    const IDX: U32x4 = U32x4([0, 5, 2, 7]);
    unsafe {
        let shuf: I32x4 = simd_shuffle(a, b, IDX);
        let all = simd_reduce_all(mask);
        let any = simd_reduce_any(mask);
        let bm: u8 = simd_bitmask(mask);
        (shuf, all, any, bm)
    }
}

#[inline(never)]
unsafe fn do_reduce_any(mask: I32x4) -> bool {
    unsafe { simd_reduce_any(mask) }
}

fn main() {
    let arg = std::env::args().nth(1).unwrap_or_else(|| "safe".to_string());
    let a = black_box(I32x4([10, 20, 30, 40]));
    let b = black_box(I32x4([100, 200, 300, 400]));
    let sel = unsafe { do_simd_select(black_box(I32x4([0, -1, 0, -1])), a, b) };
    let sel_bm = unsafe { do_simd_select_bitmask_u8(black_box(0b0101u8), a, b) };
    let a16 = black_box(U8x16([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]));
    let b16 = black_box(U8x16([21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]));
    let sel_arr = unsafe { do_simd_select_bitmask_arr2(black_box([0b0000_0011, 0b0000_0001]), a16, b16) };
    let a10 = black_box(U8x10([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
    let b10 = black_box(U8x10([11, 12, 13, 14, 15, 16, 17, 18, 19, 20]));
    let sel_arr10 = unsafe {
        do_simd_select_bitmask_arr2_len10(black_box([0b1100_1011, 0b1111_1110]), a10, b10)
    };
    let sel_arr10_bit8 = unsafe {
        do_simd_select_bitmask_arr2_len10(black_box([0x00, 0x01]), a10, b10)
    };
    let sel_arr16_bit8 = unsafe {
        do_simd_select_bitmask_arr2(black_box([0x00, 0x01]), a16, b16)
    };
    let m16 = black_box(I8x16([-1, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0]));
    let bm_arr2 = unsafe { do_simd_bitmask_arr2(m16) };
    let bm_u16 = unsafe { do_simd_bitmask_u16(m16) };
    let (shuf, all, any, bm) = unsafe { do_shuffle_and_reduce(a, b, black_box(I32x4([-1, 0, -1, 0]))) };
    println!(
        "SEL={:?} SEL_BM={:?} SEL_ARR={:?} SEL_ARR10={:?} SEL_ARR10_BIT8={:?} SEL_ARR16_BIT8_LANE8={} BM_ARR2={:?} BM_U16={bm_u16:#06x} SHUF={:?} ALL={all} ANY={any} BM={bm:#06b}",
        unsafe { unpack_i32x4(sel) },
        unsafe { unpack_i32x4(sel_bm) },
        unsafe { unpack_u8x16(sel_arr) },
        unsafe { unpack_u8x10(sel_arr10) },
        unsafe { unpack_u8x10(sel_arr10_bit8) },
        unsafe { unpack_u8x16(sel_arr16_bit8) }[8],
        bm_arr2,
        unsafe { unpack_i32x4(shuf) }
    );
    match arg.as_str() {
        "safe" => {}
        "bad_mask_one" => {
            let res = unsafe { do_simd_select(black_box(I32x4([1, 0, 1, 0])), a, b) };
            println!("BAD_MASK_ONE={:?}", unsafe { unpack_i32x4(res) });
        }
        "bad_mask_neg2" => {
            let res = unsafe { do_simd_select(black_box(I32x4([-2, -2, 1, 0])), a, b) };
            println!("BAD_MASK_NEG2={:?}", unsafe { unpack_i32x4(res) });
        }
        "bad_reduce_any_one" => {
            let res = unsafe { do_reduce_any(black_box(I32x4([1, 0, 0, 0]))) };
            println!("BAD_REDUCE_ANY_ONE={res}");
        }
        other => panic!("unknown mode: {other}"),
    }
}
"""

PROBE_C_RS = r"""#![feature(repr_simd, core_intrinsics)]
#![allow(internal_features)]
use core::hint::black_box;
use core::intrinsics::float_to_int_unchecked;
use core::intrinsics::simd::{simd_as, simd_cast, simd_extract};

#[repr(simd)]
#[derive(Copy, Clone)]
struct F32x4([f32; 4]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct I32x4([i32; 4]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct U32x4([u32; 4]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct I8x4([i8; 4]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct U8x4([u8; 4]);

#[inline(never)]
unsafe fn unpack_i32x4_c(v: I32x4) -> [i32; 4] {
    unsafe { [simd_extract(v, 0), simd_extract(v, 1), simd_extract(v, 2), simd_extract(v, 3)] }
}

#[inline(never)]
unsafe fn unpack_u32x4_c(v: U32x4) -> [u32; 4] {
    unsafe { [simd_extract(v, 0), simd_extract(v, 1), simd_extract(v, 2), simd_extract(v, 3)] }
}

#[inline(never)]
unsafe fn unpack_i8x4_c(v: I8x4) -> [i8; 4] {
    unsafe { [simd_extract(v, 0), simd_extract(v, 1), simd_extract(v, 2), simd_extract(v, 3)] }
}

#[inline(never)]
unsafe fn unpack_u8x4_c(v: U8x4) -> [u8; 4] {
    unsafe { [simd_extract(v, 0), simd_extract(v, 1), simd_extract(v, 2), simd_extract(v, 3)] }
}

#[inline(never)]
unsafe fn do_simd_as_i32(v: F32x4) -> I32x4 {
    unsafe { simd_as(v) }
}

#[inline(never)]
unsafe fn do_simd_as_u32(v: F32x4) -> U32x4 {
    unsafe { simd_as(v) }
}

#[inline(never)]
unsafe fn do_simd_cast_i32(v: F32x4) -> I32x4 {
    unsafe { simd_cast(v) }
}

#[inline(never)]
unsafe fn do_simd_cast_i8(v: F32x4) -> I8x4 {
    unsafe { simd_cast(v) }
}

#[inline(never)]
unsafe fn do_simd_cast_u8(v: F32x4) -> U8x4 {
    unsafe { simd_cast(v) }
}

#[inline(never)]
unsafe fn do_scalar_unchecked_i32(x: f32) -> i32 {
    unsafe { float_to_int_unchecked(x) }
}

#[inline(never)]
unsafe fn do_scalar_unchecked_i8(x: f32) -> i8 {
    unsafe { float_to_int_unchecked(x) }
}

#[inline(never)]
unsafe fn do_scalar_unchecked_u8(x: f32) -> u8 {
    unsafe { float_to_int_unchecked(x) }
}

fn main() {
    let arg = std::env::args().nth(1).unwrap_or_else(|| "safe".to_string());
    let as_i = unsafe { do_simd_as_i32(black_box(F32x4([f32::NAN, 1e20, -1e20, 42.9]))) };
    let as_i_inf = unsafe {
        do_simd_as_i32(black_box(F32x4([f32::INFINITY, f32::NEG_INFINITY, -0.999, 2147483648.0])))
    };
    let as_u = unsafe { do_simd_as_u32(black_box(F32x4([-1.5, 1e20, f32::NAN, 42.9]))) };
    let cast_ok = unsafe { do_simd_cast_i32(black_box(F32x4([-10.9, 0.0, 42.9, 100.1]))) };
    let cast_i8_open = unsafe { do_simd_cast_i8(black_box(F32x4([-128.9, 127.9, -0.999, 0.999]))) };
    let cast_u8_open = unsafe { do_simd_cast_u8(black_box(F32x4([-0.999, 255.9, 0.0, 42.9]))) };
    let sc_ok = unsafe { do_scalar_unchecked_i32(black_box(42.9)) };
    let sc_i8 = unsafe { do_scalar_unchecked_i8(black_box(-128.9)) };
    let sc_u8 = unsafe { do_scalar_unchecked_u8(black_box(-0.999)) };
    println!(
        "SIMD_AS_I={:?} SIMD_AS_I_INF={:?} SIMD_AS_U={:?} SIMD_CAST_OK={:?} SIMD_CAST_I8_OPEN={:?} SIMD_CAST_U8_OPEN={:?} SCALAR_OK={sc_ok} SCALAR_I8_OPEN={sc_i8} SCALAR_U8_OPEN={sc_u8}",
        unsafe { unpack_i32x4_c(as_i) },
        unsafe { unpack_i32x4_c(as_i_inf) },
        unsafe { unpack_u32x4_c(as_u) },
        unsafe { unpack_i32x4_c(cast_ok) },
        unsafe { unpack_i8x4_c(cast_i8_open) },
        unsafe { unpack_u8x4_c(cast_u8_open) },
    );
    match arg.as_str() {
        "safe" => {}
        "simd_cast_oob" => {
            let v = unsafe { do_simd_cast_i32(black_box(F32x4([f32::NAN, 1e30, -1e30, 42.9]))) };
            println!("SIMD_CAST_OOB={:?}", unsafe { unpack_i32x4_c(v) });
        }
        "simd_cast_i8_oob" => {
            let v = unsafe { do_simd_cast_i8(black_box(F32x4([-129.0, 0.0, 0.0, 0.0]))) };
            println!("SIMD_CAST_I8_OOB={:?}", unsafe { unpack_i8x4_c(v) });
        }
        "simd_cast_u8_neg1" => {
            let v = unsafe { do_simd_cast_u8(black_box(F32x4([-1.0, 0.0, 0.0, 0.0]))) };
            println!("SIMD_CAST_U8_NEG1={:?}", unsafe { unpack_u8x4_c(v) });
        }
        "scalar_oob" => {
            let v = unsafe { do_scalar_unchecked_i32(black_box(1e30)) };
            println!("SCALAR_OOB={v}");
        }
        "scalar_nan" => {
            let v = unsafe { do_scalar_unchecked_i32(black_box(f32::NAN)) };
            println!("SCALAR_NAN={v}");
        }
        other => panic!("unknown mode: {other}"),
    }
}
"""


def sanitize(text: str) -> str:
    home = str(Path.home())
    text = text.replace(home, "<HOME>")
    text = re.sub(r"/tmp/[^ \n\r\"']+", "<TMPDIR>", text)
    return text.strip()


def run_cmd(cmd: list[str], cwd: Path, extra_env: dict[str, str] | None = None) -> dict[str, object]:
    env = {**RUSTC_ENV, **(extra_env or {})}
    proc = subprocess.run(cmd, cwd=cwd, env=env, text=True, capture_output=True, check=False)
    return {
        "returncode": proc.returncode,
        "stdout": sanitize(proc.stdout),
        "stderr": sanitize(proc.stderr),
    }


def extract_llvm_functions(ll_path: Path, needles: list[str]) -> list[str]:
    text = ll_path.read_text(encoding="utf-8")
    blocks: list[str] = []
    curr: list[str] = []
    in_fn = False
    for line in text.splitlines():
        if line.startswith("define "):
            in_fn = any(n in line for n in needles)
            curr = [line] if in_fn else []
        elif in_fn:
            curr.append(line)
            if line == "}":
                blocks.append("\n".join(curr))
                in_fn = False
                curr = []
    return blocks


def probe_crate(
    tmp_root: Path,
    crate_name: str,
    main_rs: str,
    fn_needles: list[str],
    modes: list[str],
) -> dict[str, object]:
    crate_dir = tmp_root / crate_name
    (crate_dir / "src").mkdir(parents=True)
    (crate_dir / "Cargo.toml").write_text(
        f'[package]\nname = "{crate_name}"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    main_path = crate_dir / "src" / "main.rs"
    main_path.write_text(main_rs, encoding="utf-8")

    out: dict[str, object] = {"llvm_ir": {}, "native_runs": {}, "miri_runs": {}}

    for opt_label, opt_level in (("opt_0", "0"), ("opt_2", "2")):
        ll_path = crate_dir / f"{crate_name}_{opt_label}.ll"
        bin_path = crate_dir / f"{crate_name}_{opt_label}"
        ir_res = run_cmd(
            ["rustc", "--edition=2024", f"-Copt-level={opt_level}", "--emit=llvm-ir", "-o", str(ll_path), str(main_path)],
            crate_dir,
        )
        assert ir_res["returncode"] == 0, f"IR emit failed for {crate_name} {opt_label}: {ir_res}"
        bin_res = run_cmd(
            ["rustc", "--edition=2024", f"-Copt-level={opt_level}", "-o", str(bin_path), str(main_path)],
            crate_dir,
        )
        assert bin_res["returncode"] == 0, f"Binary compile failed for {crate_name} {opt_label}: {bin_res}"
        out["llvm_ir"][opt_label] = {
            "defined_functions": extract_llvm_functions(ll_path, fn_needles),
        }
        out["native_runs"][opt_label] = {}
        for mode in modes:
            out["native_runs"][opt_label][mode] = run_cmd([str(bin_path), mode], crate_dir)

    # Prebuild Miri once cleanly, then run both Stacked Borrows and Tree Borrows.
    for miri_label, miriflags in (
        ("stacked_borrows", ""),
        ("tree_borrows", "-Zmiri-tree-borrows"),
    ):
        for mode in modes:
            extra_env = {"MIRIFLAGS": miriflags} if miriflags else {}
            key = f"{miri_label}__{mode}"
            res = run_cmd(
                ["cargo", "+nightly", "miri", "run", "--offline", "--", mode],
                crate_dir,
                extra_env=extra_env,
            )
            out["miri_runs"][key] = {
                "miriflags": miriflags or "<default Stacked Borrows>",
                "args": [mode],
                **res,
            }
    return out


def main() -> int:
    rustc_ver = subprocess.check_output(["rustc", "--version", "--verbose"], env=RUSTC_ENV, text=True)
    miri_ver = subprocess.check_output(["cargo", "+nightly", "miri", "--version"], env=RUSTC_ENV, text=True)

    with tempfile.TemporaryDirectory(prefix="probe_simd_") as td:
        tmp_root = Path(td)
        results = {
            "rustc_version": rustc_ver.strip(),
            "miri_version": miri_ver.strip(),
            "probes": {
                "a_ctlz_cttz_nonzero_vs_simd": probe_crate(
                    tmp_root,
                    "probe_a_ctlz_poison",
                    PROBE_A_RS,
                    [
                        "call_ctlz_nonzero",
                        "call_cttz_nonzero",
                        "call_ctlz",
                        "call_cttz",
                        "call_simd_ctlz",
                        "call_simd_cttz",
                        "fold_ctlz_nonzero_lt32",
                        "fold_ctlz_safe_lt32",
                    ],
                    ["safe", "ctlz_zero", "cttz_zero"],
                ),
                "b_simd_select_bitmask_shuffle_reduce": probe_crate(
                    tmp_root,
                    "probe_b_simd_select",
                    PROBE_B_RS,
                    [
                        "do_simd_select",
                        "do_simd_select_bitmask_u8",
                        "do_simd_select_bitmask_arr2",
                        "do_simd_select_bitmask_arr2_len10",
                        "do_simd_bitmask_arr2",
                        "do_simd_bitmask_u16",
                        "do_shuffle_and_reduce",
                        "do_reduce_any",
                    ],
                    ["safe", "bad_mask_one", "bad_mask_neg2", "bad_reduce_any_one"],
                ),
                "c_simd_as_vs_cast_and_unchecked": probe_crate(
                    tmp_root,
                    "probe_c_simd_as",
                    PROBE_C_RS,
                    [
                        "do_simd_as_i32",
                        "do_simd_as_u32",
                        "do_simd_cast_i32",
                        "do_simd_cast_i8",
                        "do_simd_cast_u8",
                        "do_scalar_unchecked_i32",
                        "do_scalar_unchecked_i8",
                        "do_scalar_unchecked_u8",
                    ],
                    [
                        "safe",
                        "simd_cast_oob",
                        "simd_cast_i8_oob",
                        "simd_cast_u8_neg1",
                        "scalar_oob",
                        "scalar_nan",
                    ],
                ),
            },
        }

    out_path = Path(__file__).resolve().parent / "probe_results.json"
    out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} ({out_path.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
