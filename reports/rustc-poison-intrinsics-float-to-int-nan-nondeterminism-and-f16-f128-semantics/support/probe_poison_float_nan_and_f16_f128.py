#!/usr/bin/env python3
"""Empirical rustc + LLVM IR + Miri probe for poison-bearing intrinsics,
float-to-int conversions, fast/algebraic float ops, RFC 3514 NaN nondeterminism,
and f16/f128 ABI & Miri boundaries.

Writes machine-readable JSON to `--out` with all host paths and PIDs scrubbed.
Uses only a temporary directory deleted automatically on exit.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def resolve_toolchain() -> tuple[str, str, str, str]:
    rustc = shutil.which("rustc")
    if not rustc:
        cand = Path.home() / ".cargo" / "bin" / "rustc"
        if not cand.exists():
            raise RuntimeError("rustc not found on PATH or in ~/.cargo/bin")
        rustc = str(cand)

    cargo = shutil.which("cargo")
    if not cargo:
        cand = Path.home() / ".cargo" / "bin" / "cargo"
        if not cand.exists():
            raise RuntimeError("cargo not found on PATH or in ~/.cargo/bin")
        cargo = str(cand)

    rustc_ver = subprocess.check_output([rustc, "-vV"], text=True).strip()
    sysroot = subprocess.check_output([rustc, "--print", "sysroot"], text=True).strip()
    miri_bin = str(Path(sysroot) / "bin" / "miri")
    if not Path(miri_bin).exists():
        raise RuntimeError(f"miri binary not found at {miri_bin}")

    miri_sysroot = subprocess.check_output([cargo, "miri", "setup", "--print-sysroot"], text=True).strip()
    miri_ver = subprocess.check_output([miri_bin, "-V"], text=True).strip()
    return rustc, miri_bin, miri_sysroot, f"{rustc_ver}\n{miri_ver}"


def scrub(text: str, td: Path, sysroot: str) -> str:
    out = text.replace(str(td), "<TMP>").replace(sysroot, "<MIRI_SYSROOT>")
    out = re.sub(r"/rustc/[0-9a-f]{40}/", "<RUSTC_SRC>/", out)
    out = re.sub(r"thread 'rustc' \(\d+\)", "thread 'rustc' (<PID>)", out)
    out = re.sub(r"/(?:tmp|var/tmp)/[A-Za-z0-9_./-]+", "<TMP>", out)
    out = re.sub(r"/(?:home|Users)/[^/\s\"']+", "<HOME>", out)
    return out


MIRI_CASES: list[dict[str, Any]] = [
    {
        "name": "float_as_u8_saturating_nan_inf_neg_ok",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let a = black_box(f32::NAN) as u8;
    let b = black_box(f32::INFINITY) as u8;
    let c = black_box(f32::NEG_INFINITY) as u8;
    let d = black_box(-0.9999_f32) as u8;
    println!("SAT_OK {a},{b},{c},{d}");
}
""",
    },
    {
        "name": "float_to_int_unchecked_u8_neg_0_9999_open_interval_ok",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let lo: u8 = unsafe { core::intrinsics::float_to_int_unchecked(black_box(-0.9999_f32)) };
    let hi: u8 = unsafe { core::intrinsics::float_to_int_unchecked(black_box(255.9999_f32)) };
    println!("OPEN_INTERVAL_OK {lo},{hi}");
}
""",
    },
    {
        "name": "float_to_int_unchecked_u8_neg_1_0_ub",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let _v: u8 = unsafe { core::intrinsics::float_to_int_unchecked(black_box(-1.0_f32)) };
}
""",
    },
    {
        "name": "float_to_int_unchecked_u8_256_0_ub",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let _v: u8 = unsafe { core::intrinsics::float_to_int_unchecked(black_box(256.0_f32)) };
}
""",
    },
    {
        "name": "float_to_int_unchecked_i32_max_as_f32_rounds_to_2p31_ub",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let _v: i32 = unsafe { core::intrinsics::float_to_int_unchecked(black_box(i32::MAX as f32)) };
}
""",
    },
    {
        "name": "float_to_int_unchecked_i32_max_representable_f32_0x4effffff_ok",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let v: i32 = unsafe { core::intrinsics::float_to_int_unchecked(black_box(f32::from_bits(0x4eff_ffff))) };
    println!("MAX_F32_I32_OK {v}");
}
""",
    },
    {
        "name": "disjoint_bitor_disjoint_ok",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let v = unsafe { core::intrinsics::disjoint_bitor(black_box(0b1010_u32), black_box(0b0101_u32)) };
    assert_eq!(v, 0b1111_u32);
}
""",
    },
    {
        "name": "disjoint_bitor_overlapping_bit_ub",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let _v = unsafe { core::intrinsics::disjoint_bitor(black_box(0b1010_u32), black_box(0b0010_u32)) };
}
""",
    },
    {
        "name": "exact_div_exact_ok",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let u = unsafe { core::intrinsics::exact_div(black_box(12_u32), black_box(4_u32)) };
    let s = unsafe { core::intrinsics::exact_div(black_box(-12_i32), black_box(4_i32)) };
    assert_eq!((u, s), (3, -3));
}
""",
    },
    {
        "name": "exact_div_nonzero_remainder_ub",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let _v = unsafe { core::intrinsics::exact_div(black_box(13_u32), black_box(4_u32)) };
}
""",
    },
    {
        "name": "exact_div_signed_min_div_neg1_overflow_ub",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let _v = unsafe { core::intrinsics::exact_div(black_box(i8::MIN), black_box(-1_i8)) };
}
""",
    },
    {
        "name": "select_unpredictable_intrinsic_forgets_vs_hint_drops",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use core::cell::Cell;
use std::hint::black_box;
struct DropCounter<'a>(&'a Cell<usize>);
impl Drop for DropCounter<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}
fn main() {
    let c1 = Cell::new(0);
    {
        let _r = core::intrinsics::select_unpredictable(black_box(true), DropCounter(&c1), DropCounter(&c1));
    }
    let c2 = Cell::new(0);
    {
        let _r = core::hint::select_unpredictable(black_box(true), DropCounter(&c2), DropCounter(&c2));
    }
    println!("DROPS intrinsic={} hint={}", c1.get(), c2.get());
}
""",
    },
    {
        "name": "fadd_fast_nan_input_ub",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let _v = unsafe { core::intrinsics::fadd_fast(black_box(1.0_f32), black_box(f32::NAN)) };
}
""",
    },
    {
        "name": "fadd_fast_finite_inputs_infinite_output_ub",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let _v = unsafe { core::intrinsics::fadd_fast(black_box(f32::MAX), black_box(f32::MAX)) };
}
""",
    },
    {
        "name": "fadd_fast_4ulp_nondeterminism_default_miri",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::collections::BTreeSet;
use std::hint::black_box;
fn main() {
    let exact = 3.0_f32.to_bits();
    let mut seen = BTreeSet::new();
    let mut max_ulp: u32 = 0;
    for _ in 0..96 {
        let b = unsafe { core::intrinsics::fadd_fast(black_box(1.0_f32), black_box(2.0_f32)) }.to_bits();
        seen.insert(b);
        max_ulp = max_ulp.max(b.abs_diff(exact));
    }
    println!("FADD_FAST_NONDET distinct={} max_ulp={}", seen.len(), max_ulp);
}
""",
    },
    {
        "name": "fadd_fast_deterministic_floats_exact",
        "extra_flags": ["-Zmiri-deterministic-floats"],
        "code": """#![feature(core_intrinsics)]
use std::collections::BTreeSet;
use std::hint::black_box;
fn main() {
    let mut seen = BTreeSet::new();
    for _ in 0..16 {
        let b = unsafe { core::intrinsics::fadd_fast(black_box(1.0_f32), black_box(2.0_f32)) }.to_bits();
        seen.insert(b);
    }
    println!("FADD_FAST_DET distinct={} exact=0x{:08x}", seen.len(), seen.first().copied().unwrap());
}
""",
    },
    {
        "name": "fadd_algebraic_safe_const_and_runtime_nan_inf_ok",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
const C_NAN: u32 = core::intrinsics::fadd_algebraic(f32::NAN, 1.0_f32).to_bits();
const C_INF: f32 = core::intrinsics::fadd_algebraic(f32::MAX, f32::MAX);
fn main() {
    let r_inf = core::intrinsics::fadd_algebraic(black_box(f32::MAX), black_box(f32::MAX));
    let r_nan = core::intrinsics::fadd_algebraic(black_box(f32::NAN), black_box(1.0_f32));
    assert!(C_INF.is_infinite() && r_inf.is_infinite() && r_nan.is_nan());
    println!("FADD_ALG_OK const_nan=0x{C_NAN:08x}");
}
""",
    },
    {
        "name": "nan_nondeterminism_ctfe_vs_miri_default",
        "extra_flags": [],
        "code": """use std::collections::BTreeSet;
use std::hint::black_box;
const CTFE_NAN: u32 = (0.0_f32 / 0.0_f32).to_bits();
fn main() {
    let mut zdivz = BTreeSet::new();
    for _ in 0..48 {
        zdivz.insert((black_box(0.0_f32) / black_box(0.0_f32)).to_bits());
    }
    let snan = f32::from_bits(0x7f80_0001);
    let mut prop = BTreeSet::new();
    for _ in 0..192 {
        prop.insert((black_box(snan) + black_box(1.0_f32)).to_bits());
    }
    let has_sig = prop.iter().any(|&b| (b & 0x0040_0000) == 0);
    let zlist: Vec<String> = zdivz.iter().map(|b| format!("0x{b:08x}")).collect();
    println!("NAN_NONDET ctfe=0x{CTFE_NAN:08x} zdivz={zlist:?} snan_prop_count={} has_signaling_out={has_sig}", prop.len());
}
""",
    },
    {
        "name": "f16_and_f128_layout_arith_and_casts_miri_ok",
        "extra_flags": [],
        "code": """#![feature(f16, f128)]
use std::hint::black_box;
fn main() {
    assert_eq!(core::mem::size_of::<f16>(), 2);
    assert_eq!(core::mem::size_of::<f128>(), 16);
    let d = (black_box(3.5_f16) as f128) + black_box(10.25_f128);
    assert_eq!(d, 13.75_f128);
    println!("F16_F128_OK d=13.75");
}
""",
    },
    {
        "name": "f128_powi_miri_todo_boundary",
        "extra_flags": [],
        "code": """#![feature(f128)]
use std::hint::black_box;
fn main() {
    let _v = black_box(2.0_f128).powi(black_box(3));
}
""",
    },
]

SUPPLEMENTARY_MIRI_CASES: list[dict[str, Any]] = [
    {
        "name": "unchecked_shl_overflow_ub_vs_wrapping_shl_ok",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let wrapped = black_box(1_u32).wrapping_shl(32);
    assert_eq!(wrapped, 1);
    let _ub = unsafe { core::intrinsics::unchecked_shl(black_box(1_u32), black_box(32_u32)) };
}
""",
    },
    {
        "name": "unchecked_add_signed_overflow_ub",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let _ub = unsafe { core::intrinsics::unchecked_add(black_box(i8::MAX), black_box(1_i8)) };
}
""",
    },
    {
        "name": "unchecked_add_unsigned_overflow_ub",
        "extra_flags": [],
        "code": """#![feature(core_intrinsics)]
use std::hint::black_box;
fn main() {
    let _ub = unsafe { core::intrinsics::unchecked_add(black_box(u8::MAX), black_box(1_u8)) };
}
""",
    },
    {
        "name": "nan_nondeterminism_miri_deterministic_floats",
        "extra_flags": ["-Zmiri-deterministic-floats"],
        "code": """use std::collections::BTreeSet;
use std::hint::black_box;
fn main() {
    let mut zdivz = BTreeSet::new();
    let snan = f32::from_bits(0x7f80_0001);
    let mut prop = BTreeSet::new();
    for _ in 0..32 {
        zdivz.insert((black_box(0.0_f32) / black_box(0.0_f32)).to_bits());
        prop.insert((black_box(snan) + black_box(1.0_f32)).to_bits());
    }
    let zlist: Vec<String> = zdivz.iter().map(|b| format!("0x{b:08x}")).collect();
    let plist: Vec<String> = prop.iter().map(|b| format!("0x{b:08x}")).collect();
    println!("NAN_DET zdivz={zlist:?} snan_prop={plist:?}");
}
""",
    },
]

LLVM_IR_SOURCE = """#![feature(core_intrinsics, f16, f128)]
#![crate_type = "lib"]

#[no_mangle]
pub fn ir_float_as_u8_sat(x: f32) -> u8 { x as u8 }

#[no_mangle]
pub unsafe fn ir_float_to_u8_unchecked(x: f32) -> u8 {
    unsafe { core::intrinsics::float_to_int_unchecked(x) }
}

#[no_mangle]
pub unsafe fn ir_disjoint_bitor_u32(a: u32, b: u32) -> u32 {
    unsafe { core::intrinsics::disjoint_bitor(a, b) }
}

#[no_mangle]
pub unsafe fn ir_exact_sdiv_i32(a: i32, b: i32) -> i32 {
    unsafe { core::intrinsics::exact_div(a, b) }
}

#[no_mangle]
pub unsafe fn ir_exact_udiv_u32(a: u32, b: u32) -> u32 {
    unsafe { core::intrinsics::exact_div(a, b) }
}

#[no_mangle]
pub unsafe fn ir_unchecked_sadd_i32(a: i32, b: i32) -> i32 {
    unsafe { core::intrinsics::unchecked_add(a, b) }
}

#[no_mangle]
pub unsafe fn ir_unchecked_uadd_u32(a: u32, b: u32) -> u32 {
    unsafe { core::intrinsics::unchecked_add(a, b) }
}

#[no_mangle]
pub unsafe fn ir_unchecked_shl_u32(a: u32, b: u32) -> u32 {
    unsafe { core::intrinsics::unchecked_shl(a, b) }
}

#[no_mangle]
pub fn ir_checked_shl_u32(a: u32, b: u32) -> u32 {
    a.wrapping_shl(b)
}

#[no_mangle]
pub unsafe fn ir_fadd_fast_f32(a: f32, b: f32) -> f32 {
    unsafe { core::intrinsics::fadd_fast(a, b) }
}

#[no_mangle]
pub fn ir_fadd_algebraic_f32(a: f32, b: f32) -> f32 {
    core::intrinsics::fadd_algebraic(a, b)
}

#[no_mangle]
pub fn ir_select_unpred_scalar(c: bool, a: u64, b: u64) -> u64 {
    core::intrinsics::select_unpredictable(c, a, b)
}

#[no_mangle]
pub fn ir_select_unpred_pair(c: bool, a: (u64, u64), b: (u64, u64)) -> (u64, u64) {
    core::intrinsics::select_unpredictable(c, a, b)
}

#[no_mangle]
pub fn ir_select_unpred_ref_array(c: bool, a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    core::intrinsics::select_unpredictable(c, a, b)
}

#[no_mangle]
pub extern "C" fn ir_sysv_abi_f16_f128(x: f16, y: f128) -> f128 {
    (x as f128) + y
}
"""

TARGET_IR_FUNCTIONS = [
    "ir_float_as_u8_sat",
    "ir_float_to_u8_unchecked",
    "ir_disjoint_bitor_u32",
    "ir_exact_sdiv_i32",
    "ir_exact_udiv_u32",
    "ir_unchecked_sadd_i32",
    "ir_unchecked_uadd_u32",
    "ir_unchecked_shl_u32",
    "ir_fadd_fast_f32",
    "ir_fadd_algebraic_f32",
    "ir_select_unpred_scalar",
    "ir_select_unpred_pair",
    "ir_select_unpred_ref_array",
    "ir_sysv_abi_f16_f128",
]


def parse_llvm_functions(ll_text: str, names: list[str]) -> dict[str, dict[str, Any]]:
    wanted = set(names)
    parsed: dict[str, dict[str, Any]] = {}
    cur_name: str | None = None
    cur_sig: str = ""
    cur_insns: list[str] = []

    for raw_line in ll_text.splitlines():
        line = raw_line.rstrip()
        if line.startswith("define "):
            match = re.search(r"@([A-Za-z0-9_$.]+)\(", line)
            if match and match.group(1) in wanted:
                cur_name = match.group(1)
                cur_sig = line
                cur_insns = []
            else:
                cur_name = None
        elif cur_name is not None:
            if line == "}":
                parsed[cur_name] = {"signature": cur_sig, "instructions": cur_insns}
                cur_name = None
            else:
                stripped = line.strip()
                if stripped and not stripped.startswith(";"):
                    cur_insns.append(stripped)
    return parsed


def run_miri_cases(
    miri_bin: str,
    miri_sysroot: str,
    cases: list[dict[str, Any]],
    td: Path,
) -> dict[str, dict[str, Any]]:
    results: dict[str, dict[str, Any]] = {}
    for case in cases:
        name = case["name"]
        src = td / f"{name}.rs"
        src.write_text(case["code"], encoding="utf-8")
        cmd = [
            miri_bin,
            "--sysroot",
            miri_sysroot,
            "--edition=2021",
            *case["extra_flags"],
            str(src),
        ]
        proc = subprocess.run(cmd, text=True, capture_output=True, check=False, timeout=180)
        raw_lines = [scrub(line.rstrip(), td, miri_sysroot) for line in proc.stderr.splitlines() if line.strip()]
        error_idx = next(
            (idx for idx, line in enumerate(raw_lines) if line.startswith("error:") or "panicked at" in line),
            None,
        )
        diag_lines = raw_lines[error_idx:] if error_idx is not None else []
        results[name] = {
            "extra_flags": list(case["extra_flags"]),
            "miri_rc": proc.returncode,
            "stdout": scrub(proc.stdout.strip(), td, miri_sysroot),
            "diag_head": diag_lines[:6],
        }
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, help="Output JSON file path")
    args = parser.parse_args()

    rustc, miri_bin, miri_sysroot, version_str = resolve_toolchain()
    with tempfile.TemporaryDirectory() as td_raw:
        td = Path(td_raw)
        miri_matrix = run_miri_cases(miri_bin, miri_sysroot, MIRI_CASES, td)
        supplementary_miri = run_miri_cases(miri_bin, miri_sysroot, SUPPLEMENTARY_MIRI_CASES, td)

        ir_rs = td / "ir_probe.rs"
        ir_ll = td / "ir_probe.ll"
        ir_rs.write_text(LLVM_IR_SOURCE, encoding="utf-8")
        ir_cmd = [
            rustc,
            "--edition=2021",
            "-C",
            "opt-level=2",
            "-C",
            "no-prepopulate-passes",
            "--emit=llvm-ir",
            "-o",
            str(ir_ll),
            str(ir_rs),
        ]
        ir_proc = subprocess.run(ir_cmd, text=True, capture_output=True, check=False, timeout=180)
        if ir_proc.returncode != 0:
            raise RuntimeError(f"LLVM IR compilation failed:\n{ir_proc.stderr}")

        ll_text = ir_ll.read_text(encoding="utf-8")
        llvm_ir_lowering = parse_llvm_functions(ll_text, TARGET_IR_FUNCTIONS)
        supplementary_ir = parse_llvm_functions(ll_text, ["ir_checked_shl_u32"])

    payload = {
        "rustc_version": version_str,
        "ir_compile_flags": [
            "--edition=2021",
            "-C",
            "opt-level=2",
            "-C",
            "no-prepopulate-passes",
            "--emit=llvm-ir",
        ],
        "miri_matrix": miri_matrix,
        "llvm_ir_lowering": llvm_ir_lowering,
        "supplementary": {
            "miri": supplementary_miri,
            "llvm_ir_lowering": supplementary_ir,
        },
    }

    out_path = Path(args.out)
    out_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
