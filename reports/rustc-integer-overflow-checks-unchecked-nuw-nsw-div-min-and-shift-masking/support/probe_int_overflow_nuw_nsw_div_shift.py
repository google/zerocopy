#!/usr/bin/env python3
"""Empirical compiler, LLVM IR, x86-64 asm, MIR, and Miri probe for Rust integer
overflow checks, unconditional Div/Rem MIN/-1 guards, unchecked nuw/nsw ops, and
shift bit-width masking.

Runs cleanly inside temporary directories (with tempfile.TemporaryDirectory()),
requiring only an installed nightly rustc (with Miri for the Miri suite).
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any


SLUG = "rustc-integer-overflow-checks-unchecked-nuw-nsw-div-min-and-shift-masking"
HOME_STR = str(Path.home())


def _sanitize(text: str, tmp_dir: str | None = None) -> str:
    if tmp_dir:
        text = text.replace(tmp_dir, "<tmp>")
    if HOME_STR:
        text = text.replace(HOME_STR, "<home>")
    return text.strip()


def _run(
    cmd: list[str],
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    tmp_dir: str | None = None,
) -> dict[str, Any]:
    proc = subprocess.run(
        cmd,
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
        timeout=120,
    )
    return {
        "command": " ".join(cmd),
        "returncode": proc.returncode,
        "stdout": _sanitize(proc.stdout, tmp_dir),
        "stderr": _sanitize(proc.stderr, tmp_dir),
    }


def _probe_native_bin(source: str, extra_args: list[str]) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        src_path = td_path / "probe.rs"
        bin_path = td_path / "probe_bin"
        src_path.write_text(source, encoding="utf-8")
        compile_cmd = [
            "rustc",
            "--edition=2024",
            *extra_args,
            str(src_path),
            "-o",
            str(bin_path),
        ]
        c_res = _run(compile_cmd, cwd=td_path, tmp_dir=td)
        result: dict[str, Any] = {
            "edition": "2024",
            "extra_args": extra_args,
            "compile_returncode": c_res["returncode"],
            "compile_stdout": c_res["stdout"],
            "compile_stderr": c_res["stderr"],
        }
        if c_res["returncode"] == 0:
            r_res = _run([str(bin_path)], cwd=td_path, tmp_dir=td)
            result["run_returncode"] = r_res["returncode"]
            result["run_stdout"] = r_res["stdout"]
            result["run_stderr"] = r_res["stderr"]
        return result


def _probe_miri(source: str, rustflags: str | None = None) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        (td_path / "Cargo.toml").write_text(
            '[package]\nname = "miri_probe"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        src_dir = td_path / "src"
        src_dir.mkdir()
        (src_dir / "main.rs").write_text(source, encoding="utf-8")
        env = os.environ.copy()
        if rustflags is not None:
            env["RUSTFLAGS"] = rustflags
        else:
            env.pop("RUSTFLAGS", None)
        res = _run(
            ["cargo", "+nightly", "miri", "run", "--offline"],
            cwd=td_path,
            env=env,
            tmp_dir=td,
        )
        return {
            "edition": "2024",
            "command": "cargo +nightly miri run --offline",
            "rustflags": rustflags,
            "returncode": res["returncode"],
            "stdout": res["stdout"],
            "stderr": res["stderr"],
        }


def _extract_llvm_ir_fns(ir_text: str, fn_names: list[str]) -> dict[str, list[str]]:
    lines = ir_text.splitlines()
    found: dict[str, list[str]] = {}
    for name in fn_names:
        marker = f"@{name}("
        captured: list[str] = []
        in_fn = False
        for line in lines:
            if not in_fn:
                if line.startswith("define ") and marker in line:
                    in_fn = True
                    captured.append(line)
            else:
                captured.append(line)
                if line.strip() == "}":
                    break
        found[name] = captured
    return found


def _extract_asm_fns(asm_text: str, fn_names: list[str]) -> dict[str, list[str]]:
    lines = asm_text.splitlines()
    found: dict[str, list[str]] = {}
    for name in fn_names:
        label = f"{name}:"
        captured: list[str] = []
        in_fn = False
        for line in lines:
            if not in_fn:
                if line.strip() == label:
                    in_fn = True
                    captured.append(line)
            else:
                captured.append(line)
                if ".size" in line and name in line:
                    break
                if len(captured) > 120:
                    break
        found[name] = captured
    return found


def _extract_mir_fns(mir_text: str, fn_names: list[str]) -> dict[str, list[str]]:
    lines = mir_text.splitlines()
    found: dict[str, list[str]] = {}
    for name in fn_names:
        marker = f"fn {name}("
        captured: list[str] = []
        in_fn = False
        brace_depth = 0
        for line in lines:
            if not in_fn:
                if marker in line and line.lstrip().startswith("fn "):
                    in_fn = True
                    brace_depth += line.count("{") - line.count("}")
                    captured.append(line)
            else:
                captured.append(line)
                brace_depth += line.count("{") - line.count("}")
                if brace_depth <= 0:
                    break
        found[name] = captured
    return found


def run_suite() -> dict[str, Any]:
    rustc_vv = _run(["rustc", "-vV"])
    miri_ver = _run(["cargo", "+nightly", "miri", "--version"])
    cargo_ver = _run(["cargo", "--version"])

    rust_commit = None
    llvm_version = None
    host_triple = None
    for line in rustc_vv["stdout"].splitlines():
        if line.startswith("commit-hash:"):
            rust_commit = line.split(":", 1)[1].strip()
        elif line.startswith("LLVM version:"):
            llvm_version = line.split(":", 1)[1].strip()
        elif line.startswith("host:"):
            host_triple = line.split(":", 1)[1].strip()

    # Suite A: -C overflow-checks=on vs off across native and Miri + MIR dump
    u8_add_src = """fn main() {
    let a = std::hint::black_box(255u8);
    let b = std::hint::black_box(1u8);
    let c = a + b;
    println!("ADD_U8={c}");
}
"""
    i8_add_src = """fn main() {
    let a = std::hint::black_box(127i8);
    let b = std::hint::black_box(1i8);
    let c = a + b;
    println!("ADD_I8={c}");
}
"""
    u8_sub_src = """fn main() {
    let a = std::hint::black_box(0u8);
    let b = std::hint::black_box(1u8);
    let c = a - b;
    println!("SUB_U8={c}");
}
"""
    u8_mul_src = """fn main() {
    let a = std::hint::black_box(16u8);
    let b = std::hint::black_box(16u8);
    let c = a * b;
    println!("MUL_U8={c}");
}
"""
    i8_neg_src = """fn main() {
    let a = std::hint::black_box(i8::MIN);
    let c = -a;
    println!("NEG_I8={c}");
}
"""
    u32_shl_32_src = """fn main() {
    let a = std::hint::black_box(1u32);
    let b = std::hint::black_box(32u32);
    let c = a << b;
    println!("SHL_U32={c}");
}
"""
    i32_shr_32_src = """fn main() {
    let a = std::hint::black_box(-8i32);
    let b = std::hint::black_box(32u32);
    let c = a >> b;
    println!("SHR_I32={c}");
}
"""

    mir_lib_src = """#[unsafe(no_mangle)]
pub fn mir_add_i32(a: i32, b: i32) -> i32 {
    a + b
}

#[unsafe(no_mangle)]
pub fn mir_neg_i32(a: i32) -> i32 {
    -a
}

#[unsafe(no_mangle)]
pub fn mir_shl_u32(a: u32, b: u32) -> u32 {
    a << b
}

#[unsafe(no_mangle)]
pub fn mir_div_i32(a: i32, b: i32) -> i32 {
    a / b
}

#[unsafe(no_mangle)]
pub fn mir_rem_i32(a: i32, b: i32) -> i32 {
    a % b
}
"""
    mir_fns = ["mir_add_i32", "mir_neg_i32", "mir_shl_u32", "mir_div_i32", "mir_rem_i32"]
    mir_dumps: dict[str, Any] = {}
    for label, flags in [
        ("overflow_checks_on", ["-Coverflow-checks=on", "-Copt-level=0"]),
        ("overflow_checks_off", ["-Coverflow-checks=off", "-Copt-level=0"]),
    ]:
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            src_path = td_path / "mir_probe.rs"
            mir_path = td_path / "mir_probe.mir"
            src_path.write_text(mir_lib_src, encoding="utf-8")
            c_res = _run(
                [
                    "rustc",
                    "--edition=2024",
                    "--crate-type=lib",
                    *flags,
                    "--emit=mir",
                    str(src_path),
                    "-o",
                    str(mir_path),
                ],
                cwd=td_path,
                tmp_dir=td,
            )
            mir_text = mir_path.read_text(encoding="utf-8") if mir_path.exists() else ""
            mir_dumps[label] = {
                "extra_args": flags,
                "compile_returncode": c_res["returncode"],
                "mir_by_fn": _extract_mir_fns(mir_text, mir_fns),
            }

    suite_a = {
        "u8_add": {
            "native_on": _probe_native_bin(u8_add_src, ["-Coverflow-checks=on"]),
            "native_off": _probe_native_bin(u8_add_src, ["-Coverflow-checks=off"]),
            "miri_on": _probe_miri(u8_add_src, "-Coverflow-checks=on"),
            "miri_off": _probe_miri(u8_add_src, "-Coverflow-checks=off"),
        },
        "i8_add": {
            "native_on": _probe_native_bin(i8_add_src, ["-Coverflow-checks=on"]),
            "native_off": _probe_native_bin(i8_add_src, ["-Coverflow-checks=off"]),
            "miri_on": _probe_miri(i8_add_src, "-Coverflow-checks=on"),
            "miri_off": _probe_miri(i8_add_src, "-Coverflow-checks=off"),
        },
        "u8_sub": {
            "native_on": _probe_native_bin(u8_sub_src, ["-Coverflow-checks=on"]),
            "native_off": _probe_native_bin(u8_sub_src, ["-Coverflow-checks=off"]),
        },
        "u8_mul": {
            "native_on": _probe_native_bin(u8_mul_src, ["-Coverflow-checks=on"]),
            "native_off": _probe_native_bin(u8_mul_src, ["-Coverflow-checks=off"]),
        },
        "i8_neg_min": {
            "native_on": _probe_native_bin(i8_neg_src, ["-Coverflow-checks=on"]),
            "native_off": _probe_native_bin(i8_neg_src, ["-Coverflow-checks=off"]),
            "miri_on": _probe_miri(i8_neg_src, "-Coverflow-checks=on"),
            "miri_off": _probe_miri(i8_neg_src, "-Coverflow-checks=off"),
        },
        "u32_shl_32": {
            "native_on": _probe_native_bin(u32_shl_32_src, ["-Coverflow-checks=on"]),
            "native_off": _probe_native_bin(u32_shl_32_src, ["-Coverflow-checks=off"]),
            "miri_on": _probe_miri(u32_shl_32_src, "-Coverflow-checks=on"),
            "miri_off": _probe_miri(u32_shl_32_src, "-Coverflow-checks=off"),
        },
        "i32_shr_32": {
            "native_on": _probe_native_bin(i32_shr_32_src, ["-Coverflow-checks=on"]),
            "native_off": _probe_native_bin(i32_shr_32_src, ["-Coverflow-checks=off"]),
        },
        "mir_dumps": mir_dumps,
    }

    # Suite B: Mandatory Div/Rem MIN/-1 and /0 panics + shift masking under -Coverflow-checks=off -Copt-level=2
    div_min_src = """fn main() {
    let a = std::hint::black_box(i32::MIN);
    let b = std::hint::black_box(-1i32);
    let c = a / b;
    println!("DIV_RES={c}");
}
"""
    rem_min_src = """fn main() {
    let a = std::hint::black_box(i32::MIN);
    let b = std::hint::black_box(-1i32);
    let c = a % b;
    println!("REM_RES={c}");
}
"""
    div_zero_src = """fn main() {
    let a = std::hint::black_box(1i32);
    let b = std::hint::black_box(0i32);
    let c = a / b;
    println!("DIV0_RES={c}");
}
"""
    rem_zero_src = """fn main() {
    let a = std::hint::black_box(1i32);
    let b = std::hint::black_box(0i32);
    let c = a % b;
    println!("REM0_RES={c}");
}
"""
    div_min_widths_src = """fn main() {
    let r8 = std::panic::catch_unwind(|| std::hint::black_box(i8::MIN) / std::hint::black_box(-1i8));
    let r16 = std::panic::catch_unwind(|| std::hint::black_box(i16::MIN) / std::hint::black_box(-1i16));
    let r32 = std::panic::catch_unwind(|| std::hint::black_box(i32::MIN) / std::hint::black_box(-1i32));
    let r64 = std::panic::catch_unwind(|| std::hint::black_box(i64::MIN) / std::hint::black_box(-1i64));
    let r128 = std::panic::catch_unwind(|| std::hint::black_box(i128::MIN) / std::hint::black_box(-1i128));
    println!("PANIC_STATUS=({}, {}, {}, {}, {})", r8.is_err(), r16.is_err(), r32.is_err(), r64.is_err(), r128.is_err());
}
"""
    shift_mixed_neg_rhs_src = """fn main() {
    let a = std::hint::black_box(1u32);
    let b = std::hint::black_box(-1i8);
    let c = a << b;
    let d = std::hint::black_box(-8i8) >> std::hint::black_box(9u32);
    println!("SHL_NEG_I8={c:#010x} SHR_I8_9={d}");
}
"""
    off_opt2 = ["-Coverflow-checks=off", "-Copt-level=2"]
    suite_b = {
        "div_i32_min_neg1_off_opt2": _probe_native_bin(div_min_src, off_opt2),
        "div_i32_min_neg1_miri_off": _probe_miri(div_min_src, "-Coverflow-checks=off"),
        "rem_i32_min_neg1_off_opt2": _probe_native_bin(rem_min_src, off_opt2),
        "rem_i32_min_neg1_miri_off": _probe_miri(rem_min_src, "-Coverflow-checks=off"),
        "div_i32_zero_off_opt2": _probe_native_bin(div_zero_src, off_opt2),
        "rem_i32_zero_off_opt2": _probe_native_bin(rem_zero_src, off_opt2),
        "div_min_all_signed_widths_off_opt2": _probe_native_bin(div_min_widths_src, off_opt2),
        "shift_mixed_signed_rhs_off_opt2": _probe_native_bin(shift_mixed_neg_rhs_src, off_opt2),
        "shift_mixed_signed_rhs_miri_off": _probe_miri(shift_mixed_neg_rhs_src, "-Coverflow-checks=off"),
    }

    # Suite C: LLVM IR and x86-64 asm emission
    ir_lib_src = """#[unsafe(no_mangle)]
pub extern "C" fn safe_add_wrapping_when_off(a: i32, b: i32) -> i32 {
    a + b
}

#[unsafe(no_mangle)]
pub extern "C" fn i32_unchecked_add_nsw(a: i32, b: i32) -> i32 {
    unsafe { a.unchecked_add(b) }
}

#[unsafe(no_mangle)]
pub extern "C" fn u32_unchecked_add_nuw(a: u32, b: u32) -> u32 {
    unsafe { a.unchecked_add(b) }
}

#[unsafe(no_mangle)]
pub extern "C" fn i32_unchecked_sub_nsw(a: i32, b: i32) -> i32 {
    unsafe { a.unchecked_sub(b) }
}

#[unsafe(no_mangle)]
pub extern "C" fn u32_unchecked_sub_nuw(a: u32, b: u32) -> u32 {
    unsafe { a.unchecked_sub(b) }
}

#[unsafe(no_mangle)]
pub extern "C" fn i32_unchecked_mul_nsw(a: i32, b: i32) -> i32 {
    unsafe { a.unchecked_mul(b) }
}

#[unsafe(no_mangle)]
pub extern "C" fn u32_unchecked_mul_nuw(a: u32, b: u32) -> u32 {
    unsafe { a.unchecked_mul(b) }
}

#[unsafe(no_mangle)]
pub extern "C" fn safe_i32_div_always_checked(a: i32, b: i32) -> i32 {
    a / b
}

#[unsafe(no_mangle)]
pub extern "C" fn safe_i32_rem_always_checked(a: i32, b: i32) -> i32 {
    a % b
}

#[unsafe(no_mangle)]
pub extern "C" fn safe_shl_masked_when_off(a: i32, b: u32) -> i32 {
    a << b
}

#[unsafe(no_mangle)]
pub extern "C" fn safe_u8_shl_masked(a: u8, b: u32) -> u8 {
    a << b
}

#[unsafe(no_mangle)]
pub extern "C" fn safe_u32_shl_i8_masked(a: u32, b: i8) -> u32 {
    a << b
}

#[unsafe(no_mangle)]
pub extern "C" fn u32_unchecked_shl_raw(a: u32, b: u32) -> u32 {
    unsafe { a.unchecked_shl(b) }
}

#[unsafe(no_mangle)]
pub extern "C" fn i32_unchecked_shr_raw(a: i32, b: u32) -> i32 {
    unsafe { a.unchecked_shr(b) }
}

#[unsafe(no_mangle)]
pub extern "C" fn u32_unchecked_shr_raw(a: u32, b: u32) -> u32 {
    unsafe { a.unchecked_shr(b) }
}

#[unsafe(no_mangle)]
pub extern "C" fn nsw_allows_sgt_fold(x: i32) -> bool {
    if x > 0 {
        unsafe { x.unchecked_add(1) > 0 }
    } else {
        true
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wrapping_preserves_sgt_cmp(x: i32) -> bool {
    if x > 0 {
        (x + 1) > 0
    } else {
        true
    }
}
"""
    ir_fn_names = [
        "safe_add_wrapping_when_off",
        "i32_unchecked_add_nsw",
        "u32_unchecked_add_nuw",
        "i32_unchecked_sub_nsw",
        "u32_unchecked_sub_nuw",
        "i32_unchecked_mul_nsw",
        "u32_unchecked_mul_nuw",
        "safe_i32_div_always_checked",
        "safe_i32_rem_always_checked",
        "safe_shl_masked_when_off",
        "safe_u8_shl_masked",
        "safe_u32_shl_i8_masked",
        "u32_unchecked_shl_raw",
        "i32_unchecked_shr_raw",
        "u32_unchecked_shr_raw",
        "nsw_allows_sgt_fold",
        "wrapping_preserves_sgt_cmp",
    ]
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        src_path = td_path / "ir_probe.rs"
        ll_path = td_path / "ir_probe.ll"
        s_path = td_path / "ir_probe.s"
        src_path.write_text(ir_lib_src, encoding="utf-8")
        ll_res = _run(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                "-Copt-level=2",
                "-Coverflow-checks=off",
                "--emit=llvm-ir",
                str(src_path),
                "-o",
                str(ll_path),
            ],
            cwd=td_path,
            tmp_dir=td,
        )
        asm_res = _run(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                "-Copt-level=2",
                "-Coverflow-checks=off",
                "--emit=asm",
                str(src_path),
                "-o",
                str(s_path),
            ],
            cwd=td_path,
            tmp_dir=td,
        )
        ll_text = ll_path.read_text(encoding="utf-8") if ll_path.exists() else ""
        asm_text = s_path.read_text(encoding="utf-8") if s_path.exists() else ""
        llvm_ir_by_fn = _extract_llvm_ir_fns(ll_text, ir_fn_names)
        asm_by_fn = _extract_asm_fns(
            asm_text,
            [
                "safe_i32_div_always_checked",
                "safe_shl_masked_when_off",
                "u32_unchecked_shl_raw",
                "nsw_allows_sgt_fold",
                "wrapping_preserves_sgt_cmp",
            ],
        )

    # Also inspect debug-assertions=on vs off on unchecked_add (assert_unsafe_precondition!)
    dbg_cmp_src = """#[unsafe(no_mangle)]
pub extern "C" fn probe_u32_unchecked_add(a: u32, b: u32) -> u32 {
    unsafe { a.unchecked_add(b) }
}
"""
    dbg_ir_compare: dict[str, Any] = {}
    for dbg_flag in ["on", "off"]:
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            src_path = td_path / "dbg_probe.rs"
            ll_path = td_path / "dbg_probe.ll"
            src_path.write_text(dbg_cmp_src, encoding="utf-8")
            c_res = _run(
                [
                    "rustc",
                    "--edition=2024",
                    "--crate-type=lib",
                    "-Copt-level=2",
                    f"-Cdebug-assertions={dbg_flag}",
                    "--emit=llvm-ir",
                    str(src_path),
                    "-o",
                    str(ll_path),
                ],
                cwd=td_path,
                tmp_dir=td,
            )
            ll_text = ll_path.read_text(encoding="utf-8") if ll_path.exists() else ""
            dbg_ir_compare[f"debug_assertions_{dbg_flag}"] = {
                "compile_returncode": c_res["returncode"],
                "llvm_ir_by_fn": _extract_llvm_ir_fns(ll_text, ["probe_u32_unchecked_add"]),
            }

    # Also test native execution of nsw_allows_sgt_fold(i32::MAX) vs wrapping_preserves_sgt_cmp(i32::MAX)
    nsw_fold_bin_src = """#[inline(never)]
fn nsw_cmp(x: i32) -> bool {
    if x > 0 { unsafe { x.unchecked_add(1) > 0 } } else { true }
}
#[inline(never)]
fn wrap_cmp(x: i32) -> bool {
    if x > 0 { (x + 1) > 0 } else { true }
}
fn main() {
    let x = std::hint::black_box(i32::MAX);
    println!("NSW_CMP={} WRAP_CMP={}", nsw_cmp(x), wrap_cmp(x));
}
"""
    suite_c = {
        "llvm_ir_opt2_overflow_off": {
            "edition": "2024",
            "extra_args": ["-Copt-level=2", "-Coverflow-checks=off", "--emit=llvm-ir"],
            "compile_returncode": ll_res["returncode"],
            "llvm_ir_by_fn": llvm_ir_by_fn,
        },
        "asm_opt2_overflow_off": {
            "edition": "2024",
            "extra_args": ["-Copt-level=2", "-Coverflow-checks=off", "--emit=asm"],
            "compile_returncode": asm_res["returncode"],
            "asm_by_fn": asm_by_fn,
        },
        "debug_assertions_unchecked_add_ir": dbg_ir_compare,
        "native_nsw_fold_at_i32_max": _probe_native_bin(nsw_fold_bin_src, off_opt2),
    }

    # Suite D: Miri UB & debug-assertions native precondition comparison
    miri_cases = {
        "u32_unchecked_add_overflow_unused_ub": "fn main() { let _ = unsafe { std::hint::black_box(u32::MAX).unchecked_add(1) }; }\n",
        "i32_unchecked_add_overflow_ub": "fn main() { let r = unsafe { std::hint::black_box(i32::MAX).unchecked_add(1) }; println!(\"{r}\"); }\n",
        "u32_unchecked_sub_underflow_ub": "fn main() { let r = unsafe { std::hint::black_box(0u32).unchecked_sub(1) }; println!(\"{r}\"); }\n",
        "i32_unchecked_sub_underflow_ub": "fn main() { let r = unsafe { std::hint::black_box(i32::MIN).unchecked_sub(1) }; println!(\"{r}\"); }\n",
        "u32_unchecked_mul_overflow_ub": "fn main() { let r = unsafe { std::hint::black_box(u32::MAX).unchecked_mul(2) }; println!(\"{r}\"); }\n",
        "i32_unchecked_mul_min_neg1_ub": "fn main() { let r = unsafe { std::hint::black_box(i32::MIN).unchecked_mul(-1) }; println!(\"{r}\"); }\n",
        "u32_unchecked_shl_32_ub": "fn main() { let r = unsafe { std::hint::black_box(1u32).unchecked_shl(32) }; println!(\"{r}\"); }\n",
        "i32_unchecked_shr_32_ub": "fn main() { let r = unsafe { std::hint::black_box(1i32).unchecked_shr(32) }; println!(\"{r}\"); }\n",
        "u32_unchecked_shl_31_valid": "fn main() { let r = unsafe { std::hint::black_box(1u32).unchecked_shl(31) }; println!(\"SHL31={r:#010x}\"); }\n",
        "i32_checked_div_min_neg1_none": "fn main() { let r = std::hint::black_box(i32::MIN).checked_div(std::hint::black_box(-1)); println!(\"CHECKED_DIV={r:?}\"); }\n",
    }
    miri_results = {name: _probe_miri(src) for name, src in miri_cases.items()}
    un_dbg_src = miri_cases["u32_unchecked_add_overflow_unused_ub"]
    suite_d = {
        "miri_unchecked_ub_and_controls": miri_results,
        "native_unchecked_add_debug_assertions_on": _probe_native_bin(un_dbg_src, ["-Cdebug-assertions=on"]),
        "native_unchecked_add_debug_assertions_off": _probe_native_bin(un_dbg_src, ["-Cdebug-assertions=off"]),
    }

    return {
        "probe_id": "rustc-integer-overflow-nuw-nsw-div-shift",
        "package_slug": SLUG,
        "observed_at": _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%d"),
        "environment": {
            "rustc_version": rustc_vv["stdout"],
            "rustc_commit_hash": rust_commit,
            "llvm_version": llvm_version,
            "host_triple": host_triple,
            "cargo_version": cargo_ver["stdout"],
            "miri_version": miri_ver["stdout"],
        },
        "experiments": {
            "a_overflow_checks_on_vs_off_and_mir": suite_a,
            "b_mandatory_div_rem_guards_and_shift_masking": suite_b,
            "c_llvm_ir_and_asm_nuw_nsw_div_shift": suite_c,
            "d_miri_unchecked_ub_and_debug_assertions": suite_d,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    default_out = Path(__file__).resolve().parent / "probe_results.json"
    parser.add_argument("--out", type=Path, default=default_out, help="Output JSON path")
    args = parser.parse_args()
    results = run_suite()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out} ({args.out.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
