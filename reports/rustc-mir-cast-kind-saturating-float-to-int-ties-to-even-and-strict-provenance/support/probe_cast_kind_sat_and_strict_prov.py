#!/usr/bin/env python3
"""Empirical rustc + LLVM IR + MIR + Miri probe for MIR CastKind lowering,
saturating FloatToInt, IntToFloat ties-to-even, PtrToPtr wide-to-thin,
and PointerExposeProvenance / PointerWithExposedProvenance vs. Strict Provenance.

Uses only Python 3.10+ stdlib and temporary directories deleted on exit.
All host paths, home directories, and toolchain store prefixes are scrubbed.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def resolve_toolchain() -> tuple[str, str, str, str, str]:
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

    miri_sysroot = subprocess.check_output(
        [cargo, "miri", "setup", "--print-sysroot"], text=True
    ).strip()
    miri_ver = subprocess.check_output([miri_bin, "-V"], text=True).strip()

    commit_hash = ""
    for line in rustc_ver.splitlines():
        if line.startswith("commit-hash: "):
            commit_hash = line.split(": ", 1)[1].strip()
            break
    return rustc, miri_bin, miri_sysroot, f"{rustc_ver}\n{miri_ver}", commit_hash


def scrub(text: str, td: Path, sysroot: str) -> str:
    out = text.replace(str(td), "<TMP>").replace(sysroot, "<MIRI_SYSROOT>")
    out = re.sub(r"/rustc/[0-9a-f]{40}/", "<RUSTC_SRC>/", out)
    out = re.sub(r"thread 'rustc' \(\d+\)", "thread 'rustc' (<PID>)", out)
    out = re.sub(r"/(?:tmp|var/tmp)/[A-Za-z0-9_./-]+", "<TMP>", out)
    out = re.sub(r"/(?:home|Users)/[^/\s\"']+", "<HOME>", out)
    return out


LLVM_IR_SOURCE = r"""#![crate_type = "lib"]
#![allow(internal_features)]

#[unsafe(no_mangle)]
pub extern "C" fn cast_i8_u32(x: i8) -> u32 { x as u32 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_i8_u8_u32(x: i8) -> u32 { (x as u8) as u32 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_u32_i8(x: u32) -> i8 { x as i8 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_bool_u32(b: bool) -> u32 { b as u32 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_f64_i32(x: f64) -> i32 { x as i32 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_f64_u32(x: f64) -> u32 { x as u32 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_f32_i8(x: f32) -> i8 { x as i8 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_f32_u8(x: f32) -> u8 { x as u8 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_i32_f32(x: i32) -> f32 { x as f32 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_u32_f32(x: u32) -> f32 { x as f32 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_u128_f32(x: u128) -> f32 { x as f32 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_f64_f32(x: f64) -> f32 { x as f32 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_f32_f64(x: f32) -> f64 { x as f64 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_ptr_to_ptr(p: *const u32) -> *const u8 { p as *const u8 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_wide_to_thin(p: *const [u32]) -> *const u32 { p as *const u32 }

#[unsafe(no_mangle)]
pub fn cast_wide_to_thin_rust_abi(p: *const [u32]) -> *const u32 { p as *const u32 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_fn_ptr_to_ptr(f: extern "C" fn() -> u32) -> *const () { f as *const () }

#[unsafe(no_mangle)]
pub extern "C" fn cast_ptr_expose(p: *const u32) -> usize { p as usize }

#[unsafe(no_mangle)]
pub extern "C" fn cast_ptr_with_exposed(a: usize) -> *const u32 { a as *const u32 }

#[unsafe(no_mangle)]
pub extern "C" fn cast_ptr_addr_strict(p: *const u32) -> usize { p.addr() }

#[unsafe(no_mangle)]
pub extern "C" fn cast_ptr_with_addr_strict(p: *const u32, a: usize) -> *const u32 {
    p.with_addr(a)
}

#[unsafe(no_mangle)]
pub extern "C" fn cast_without_provenance_strict(a: usize) -> *const u32 {
    core::ptr::without_provenance(a)
}
"""

TARGET_IR_FUNCTIONS = [
    "cast_i8_u32",
    "cast_i8_u8_u32",
    "cast_u32_i8",
    "cast_bool_u32",
    "cast_f64_i32",
    "cast_f64_u32",
    "cast_f32_i8",
    "cast_f32_u8",
    "cast_i32_f32",
    "cast_u32_f32",
    "cast_u128_f32",
    "cast_f64_f32",
    "cast_f32_f64",
    "cast_ptr_to_ptr",
    "cast_wide_to_thin",
    "cast_wide_to_thin_rust_abi",
    "cast_fn_ptr_to_ptr",
    "cast_ptr_expose",
    "cast_ptr_with_exposed",
    "cast_ptr_addr_strict",
    "cast_ptr_with_addr_strict",
    "cast_without_provenance_strict",
]


def parse_llvm_functions(ll_text: str, names: list[str]) -> dict[str, dict[str, Any]]:
    wanted = set(names)
    parsed: dict[str, dict[str, Any]] = {}
    cur_name: str | None = None
    cur_sig = ""
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


def parse_mir_cast_lines(mir_text: str, names: list[str]) -> dict[str, list[str]]:
    wanted = set(names)
    out: dict[str, list[str]] = {}
    cur_fn: str | None = None
    for raw_line in mir_text.splitlines():
        m = re.match(r"^fn ([A-Za-z0-9_]+)\(", raw_line)
        if m:
            fn_name = m.group(1)
            cur_fn = fn_name if fn_name in wanted else None
            if cur_fn:
                out.setdefault(cur_fn, [])
            continue
        if cur_fn is not None:
            if raw_line == "}":
                cur_fn = None
                continue
            s = raw_line.strip()
            if " as " in s and ("(" in s):
                out[cur_fn].append(s)
    return out


NUMERIC_EXEC_SOURCE = r"""use core::fmt::Debug;
use std::hint::black_box;

extern "C" fn helper_fn() -> u32 { 77 }

fn main() {
    // 1. IntToInt sign/zero extension and truncation
    let neg_i8 = black_box(-1_i8);
    let i8_to_u32 = neg_i8 as u32;
    let i8_u8_u32 = (neg_i8 as u8) as u32;
    let u32_trunc_pos_i8 = black_box(0x1234_5678_u32) as i8;
    let u32_trunc_neg_i8 = black_box(0x1234_56ff_u32) as i8;
    let i16_trunc_u8 = black_box(-1_i16) as u8;
    let u32_max_i32 = black_box(u32::MAX) as i32;
    let bool_t_u32 = black_box(true) as u32;
    let bool_f_i32 = black_box(false) as i32;

    // 2. FloatToInt saturating total semantics (zero UB)
    let nan_to_i32 = black_box(f64::NAN) as i32;
    let neg_nan_to_i32 = black_box(-f64::NAN) as i32;
    let nan_to_u32 = black_box(f64::NAN) as u32;
    let snan_f32_to_i32 = black_box(f32::from_bits(0x7f80_0001)) as i32;
    let inf_to_u32 = black_box(f64::INFINITY) as u32;
    let inf_to_i32 = black_box(f64::INFINITY) as i32;
    let neg_inf_to_u32 = black_box(f64::NEG_INFINITY) as u32;
    let neg_inf_to_i32 = black_box(f64::NEG_INFINITY) as i32;
    let neg_one_to_u32 = black_box(-1.0_f64) as u32;
    let neg_frac_to_u32 = black_box(-0.999_f64) as u32;
    let neg_frac_to_i32 = black_box(-0.999_f64) as i32;
    let two_p31_f32_to_i32 = black_box(2147483648.0_f32) as i32;
    let below_min_f32_to_i32 = black_box(-2147483904.0_f32) as i32;
    let trunc_pos_f64 = black_box(42.9_f64) as i32;
    let trunc_neg_f64 = black_box(-42.9_f64) as i32;
    let clamp_u8_hi = black_box(256.0_f64) as u8;
    let clamp_i8_lo = black_box(-129.0_f64) as i8;
    let subnormal_to_i32 = black_box(f64::MIN_POSITIVE / 2.0) as i32;

    // 3. IntToFloat IEEE-754 roundTiesToEven & u128 overflow
    let tie_even_down = black_box((1_u32 << 24) + 1) as f32;
    let exact_plus2 = black_box((1_u32 << 24) + 2) as f32;
    let tie_even_up = black_box((1_u32 << 24) + 3) as f32;
    let exact_plus4 = black_box((1_u32 << 24) + 4) as f32;
    let i32_max_f32 = black_box(i32::MAX) as f32;
    let u128_max_f32 = black_box(u128::MAX) as f32;
    let i128_min_f32 = black_box(i128::MIN) as f32;

    // 4. FloatToFloat
    let f64_tie_to_f32 = black_box(16777217.0_f64) as f32;
    let f64_ovf_to_f32 = black_box(1e300_f64) as f32;

    // 5. PtrToPtr wide-to-thin and FnPtrToPtr
    let arr = [10_u32, 20, 30];
    let wide_slice: *const [u32] = &arr;
    let thin_slice: *const u32 = wide_slice as *const u32;
    let wide_slice_val = unsafe { *thin_slice };

    let x: u32 = 42;
    let wide_dyn: *const dyn Debug = &x;
    let thin_dyn: *const u32 = wide_dyn as *const u32;
    let wide_dyn_val = unsafe { *thin_dyn };

    let fn_ptr: extern "C" fn() -> u32 = helper_fn;
    let erased_fn: *const () = fn_ptr as *const ();
    let roundtrip_fn: extern "C" fn() -> u32 = unsafe { core::mem::transmute(erased_fn) };
    let fn_res = roundtrip_fn();

    println!("i8_to_u32={i8_to_u32:#x}");
    println!("i8_u8_u32={i8_u8_u32}");
    println!("u32_trunc_pos_i8={u32_trunc_pos_i8}");
    println!("u32_trunc_neg_i8={u32_trunc_neg_i8}");
    println!("i16_trunc_u8={i16_trunc_u8}");
    println!("u32_max_i32={u32_max_i32}");
    println!("bool_t_u32={bool_t_u32} bool_f_i32={bool_f_i32}");
    println!("nan_to_i32={nan_to_i32} neg_nan_to_i32={neg_nan_to_i32} nan_to_u32={nan_to_u32} snan_f32_to_i32={snan_f32_to_i32}");
    println!("inf_to_u32={inf_to_u32} inf_to_i32={inf_to_i32} neg_inf_to_u32={neg_inf_to_u32} neg_inf_to_i32={neg_inf_to_i32}");
    println!("neg_one_to_u32={neg_one_to_u32} neg_frac_to_u32={neg_frac_to_u32} neg_frac_to_i32={neg_frac_to_i32}");
    println!("two_p31_f32_to_i32={two_p31_f32_to_i32} below_min_f32_to_i32={below_min_f32_to_i32}");
    println!("trunc_pos_f64={trunc_pos_f64} trunc_neg_f64={trunc_neg_f64} clamp_u8_hi={clamp_u8_hi} clamp_i8_lo={clamp_i8_lo} subnormal_to_i32={subnormal_to_i32}");
    println!("tie_even_down={tie_even_down:.1} (0x{:08x}) exact_plus2={exact_plus2:.1} (0x{:08x}) tie_even_up={tie_even_up:.1} (0x{:08x}) exact_plus4={exact_plus4:.1} (0x{:08x})",
        tie_even_down.to_bits(), exact_plus2.to_bits(), tie_even_up.to_bits(), exact_plus4.to_bits());
    println!("i32_max_f32={i32_max_f32:.1} (0x{:08x}) u128_max_f32_inf={} (0x{:08x}) i128_min_f32_bits=0x{:08x}",
        i32_max_f32.to_bits(), u128_max_f32.is_infinite(), u128_max_f32.to_bits(), i128_min_f32.to_bits());
    println!("f64_tie_to_f32={f64_tie_to_f32:.1} (0x{:08x}) f64_ovf_to_f32_inf={}",
        f64_tie_to_f32.to_bits(), f64_ovf_to_f32.is_infinite());
    println!("wide_slice_val={wide_slice_val} wide_dyn_val={wide_dyn_val} fn_res={fn_res}");
}
"""


PROVENANCE_CASES: list[dict[str, str]] = [
    {
        "id": "expose_and_with_exposed_cast",
        "code": """fn main() {
    let x: u32 = 42;
    let p: *const u32 = &x;
    let addr: usize = p as usize;
    let q: *const u32 = addr as *const u32;
    let v = unsafe { *q };
    println!("EXPOSE_PROV_OK={v}");
}
""",
    },
    {
        "id": "expose_fn_and_with_exposed_fn",
        "code": """fn main() {
    let x: u32 = 42;
    let p: *const u32 = &x;
    let addr: usize = p.expose_provenance();
    let q: *const u32 = core::ptr::with_exposed_provenance(addr);
    let v = unsafe { *q };
    println!("EXPOSE_FN_OK={v}");
}
""",
    },
    {
        "id": "expose_only_no_int_to_ptr",
        "code": """fn main() {
    let x: u32 = 42;
    let p: *const u32 = &x;
    let addr: usize = p as usize;
    assert_ne!(addr, 0);
    println!("EXPOSE_ONLY_OK");
}
""",
    },
    {
        "id": "strict_provenance_addr_with_addr",
        "code": """fn main() {
    let arr: [u32; 2] = [10, 42];
    let p: *const u32 = arr.as_ptr();
    let a: usize = p.addr();
    let q: *const u32 = p.with_addr(a + 4);
    let v = unsafe { *q };
    println!("STRICT_PROV_OK={v}");
}
""",
    },
    {
        "id": "addr_without_expose_then_int_to_ptr_ub",
        "code": """fn main() {
    let x: u32 = 42;
    let p: *const u32 = &x;
    let a: usize = p.addr();
    let q: *const u32 = a as *const u32;
    let v = unsafe { *q };
    println!("UNREACHABLE={v}");
}
""",
    },
    {
        "id": "without_provenance_deref_ub",
        "code": """fn main() {
    let x: u32 = 42;
    let a: usize = (&raw const x).addr();
    let q: *const u32 = core::ptr::without_provenance(a);
    let v = unsafe { *q };
    println!("UNREACHABLE={v}");
}
""",
    },
    {
        "id": "without_provenance_zst_ok",
        "code": """fn main() {
    let q: *const () = core::ptr::without_provenance(0x1000);
    unsafe { *q };
    println!("WITHOUT_PROV_ZST_OK");
}
""",
    },
    {
        "id": "wildcard_unexposed_target_alloc_ub",
        "code": """fn main() {
    let x: u32 = 11;
    let y: u32 = 22;
    let _exposed_x: usize = (&raw const x) as usize;
    let y_addr: usize = (&raw const y).addr();
    let q: *const u32 = y_addr as *const u32;
    let v = unsafe { *q };
    println!("UNREACHABLE={v}");
}
""",
    },
    {
        "id": "wildcard_wrapping_offset_to_exposed_alloc_ok",
        "code": """fn main() {
    let x: u32 = 11;
    let y: u32 = 22;
    let x_addr: usize = (&raw const x).addr();
    let y_addr: usize = (&raw const y) as usize;
    let diff: isize = (y_addr as isize).wrapping_sub(x_addr as isize);
    let q_wild: *const u8 = x_addr as *const u8;
    let q_shifted: *const u32 = q_wild.wrapping_byte_offset(diff).cast();
    let v = unsafe { *q_shifted };
    println!("WILDCARD_SHIFT_OK={v}");
}
""",
    },
]

MIRI_MODES: list[tuple[str, list[str]]] = [
    ("default", []),
    ("strict_provenance", ["-Zmiri-strict-provenance"]),
    ("permissive_provenance", ["-Zmiri-permissive-provenance"]),
    ("tree_borrows", ["-Zmiri-tree-borrows"]),
]


def run_miri_cmd(
    miri_bin: str,
    miri_sysroot: str,
    src_path: Path,
    extra_flags: list[str],
    td: Path,
) -> dict[str, Any]:
    cmd = [
        miri_bin,
        "--sysroot",
        miri_sysroot,
        "--edition=2024",
        *extra_flags,
        str(src_path),
    ]
    proc = subprocess.run(cmd, text=True, capture_output=True, check=False, timeout=180)
    stderr_clean = "\n".join(
        scrub(line.rstrip(), td, miri_sysroot)
        for line in proc.stderr.splitlines()
        if line.strip()
    )
    return {
        "miriflags": extra_flags,
        "returncode": proc.returncode,
        "stdout": scrub(proc.stdout.strip(), td, miri_sysroot),
        "stderr": stderr_clean,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "pos_out",
        nargs="?",
        help="Optional positional output JSON path",
    )
    parser.add_argument(
        "--out",
        dest="flag_out",
        help="Output JSON file path",
    )
    args = parser.parse_args()
    out_target = args.flag_out or args.pos_out

    rustc, miri_bin, miri_sysroot, version_str, commit_hash = resolve_toolchain()
    with tempfile.TemporaryDirectory() as td_raw:
        td = Path(td_raw)

        # Part A: LLVM IR (post-O2 and pre-pass) + MIR dump
        ir_rs = td / "cast_lib.rs"
        ir_ll_o2 = td / "cast_lib_o2.ll"
        ir_ll_nopass = td / "cast_lib_nopass.ll"
        ir_mir = td / "cast_lib.mir"
        ir_rs.write_text(LLVM_IR_SOURCE, encoding="utf-8")

        for extra, out_ll in [
            (["-C", "opt-level=2"], ir_ll_o2),
            (["-C", "opt-level=2", "-C", "no-prepopulate-passes"], ir_ll_nopass),
        ]:
            proc = subprocess.run(
                [rustc, "--edition=2024", *extra, "--emit=llvm-ir", "-o", str(out_ll), str(ir_rs)],
                text=True,
                capture_output=True,
                check=False,
                timeout=180,
            )
            if proc.returncode != 0:
                raise RuntimeError(f"LLVM IR compile failed ({extra}):\n{proc.stderr}")

        mir_proc = subprocess.run(
            [rustc, "--edition=2024", "-C", "opt-level=2", "--emit=mir", "-o", str(ir_mir), str(ir_rs)],
            text=True,
            capture_output=True,
            check=False,
            timeout=180,
        )
        if mir_proc.returncode != 0:
            raise RuntimeError(f"MIR emit failed:\n{mir_proc.stderr}")

        llvm_ir_o2 = parse_llvm_functions(ir_ll_o2.read_text(encoding="utf-8"), TARGET_IR_FUNCTIONS)
        llvm_ir_nopass = parse_llvm_functions(
            ir_ll_nopass.read_text(encoding="utf-8"), TARGET_IR_FUNCTIONS
        )
        mir_casts = parse_mir_cast_lines(ir_mir.read_text(encoding="utf-8"), TARGET_IR_FUNCTIONS)

        # Part B: Native O0/O2 + Miri numeric cast matrix
        num_rs = td / "num_probe.rs"
        num_bin_o2 = td / "num_probe_o2"
        num_bin_o0 = td / "num_probe_o0"
        num_rs.write_text(NUMERIC_EXEC_SOURCE, encoding="utf-8")

        c_o2 = subprocess.run(
            [rustc, "--edition=2024", "-C", "opt-level=2", "-o", str(num_bin_o2), str(num_rs)],
            text=True,
            capture_output=True,
            check=False,
            timeout=180,
        )
        if c_o2.returncode != 0:
            raise RuntimeError(f"Native O2 compile failed:\n{c_o2.stderr}")
        r_o2 = subprocess.run([str(num_bin_o2)], text=True, capture_output=True, check=False, timeout=60)

        c_o0 = subprocess.run(
            [rustc, "--edition=2024", "-C", "opt-level=0", "-o", str(num_bin_o0), str(num_rs)],
            text=True,
            capture_output=True,
            check=False,
            timeout=180,
        )
        if c_o0.returncode != 0:
            raise RuntimeError(f"Native O0 compile failed:\n{c_o0.stderr}")
        r_o0 = subprocess.run([str(num_bin_o0)], text=True, capture_output=True, check=False, timeout=60)

        num_miri_default = run_miri_cmd(miri_bin, miri_sysroot, num_rs, [], td)
        num_miri_det = run_miri_cmd(
            miri_bin, miri_sysroot, num_rs, ["-Zmiri-deterministic-floats"], td
        )

        if r_o2.returncode != 0 or r_o0.returncode != 0 or num_miri_default["returncode"] != 0:
            raise RuntimeError("Numeric cast probe failed unexpectedly")
        if r_o2.stdout.strip() != r_o0.stdout.strip() or r_o2.stdout.strip() != num_miri_default["stdout"]:
            raise RuntimeError(
                "Divergence across O0, O2, and Miri numeric cast outputs:\n"
                f"O2:\n{r_o2.stdout}\nO0:\n{r_o0.stdout}\nMiri:\n{num_miri_default['stdout']}"
            )

        # Part C: Pointer provenance & Strict Provenance matrix
        prov_results: dict[str, dict[str, Any]] = {}
        for case in PROVENANCE_CASES:
            cid = case["id"]
            src_path = td / f"{cid}.rs"
            src_path.write_text(case["code"], encoding="utf-8")
            prov_results[cid] = {}
            for mode_name, flags in MIRI_MODES:
                prov_results[cid][mode_name] = run_miri_cmd(
                    miri_bin, miri_sysroot, src_path, flags, td
                )

    payload = {
        "probe_suite": "mir_cast_kind_saturating_float_to_int_ties_to_even_and_strict_provenance",
        "rust_commit_sha": commit_hash,
        "toolchain_version": version_str,
        "experiments": {
            "a_llvm_ir_and_mir_casts": {
                "o2_flags": ["--edition=2024", "-C", "opt-level=2", "--emit=llvm-ir"],
                "nopass_flags": [
                    "--edition=2024",
                    "-C",
                    "opt-level=2",
                    "-C",
                    "no-prepopulate-passes",
                    "--emit=llvm-ir",
                ],
                "mir_flags": ["--edition=2024", "-C", "opt-level=2", "--emit=mir"],
                "llvm_ir_o2": llvm_ir_o2,
                "llvm_ir_nopass": llvm_ir_nopass,
                "mir_casts": mir_casts,
            },
            "b_numeric_and_ptr_casts_native_vs_miri": {
                "native_o2_returncode": r_o2.returncode,
                "native_o0_returncode": r_o0.returncode,
                "native_stdout": r_o2.stdout.strip(),
                "miri_default": num_miri_default,
                "miri_deterministic_floats": num_miri_det,
                "all_outputs_identical": (
                    r_o2.stdout.strip()
                    == r_o0.stdout.strip()
                    == num_miri_default["stdout"]
                    == num_miri_det["stdout"]
                ),
            },
            "c_pointer_provenance_miri_matrix": prov_results,
        },
    }

    rendered = json.dumps(payload, indent=2) + "\n"
    if out_target:
        Path(out_target).write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
