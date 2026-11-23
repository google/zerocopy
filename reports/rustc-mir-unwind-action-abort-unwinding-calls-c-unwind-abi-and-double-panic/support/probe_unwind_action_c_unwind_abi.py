#!/usr/bin/env python3
"""Reproducible live rustc probe for MIR UnwindAction, AbortUnwindingCalls,
extern "C" vs extern "C-unwind" ABI boundaries, double-panic InCleanup
termination, -Cpanic=abort cleanup erasure, and LLVM call/invoke/nounwind lowering.

All compilations and executions occur inside `tempfile.TemporaryDirectory()`.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
from typing import Any


PROBE_LIB_RS = r"""
pub struct Bomb;

impl Drop for Bomb {
    #[inline(never)]
    fn drop(&mut self) {
        std::hint::black_box(0u8);
    }
}

pub struct DropLogger;

impl Drop for DropLogger {
    #[inline(never)]
    fn drop(&mut self) {
        eprintln!("DROP_RAN_BEFORE_TERMINATE");
    }
}

#[inline(never)]
pub fn helper_may_panic() {
    if std::hint::black_box(false) {
        panic!("helper panic");
    }
}

#[inline(never)]
pub extern "C" fn c_abi_panics(cond: bool) {
    if cond {
        panic!("c abi cannot unwind");
    }
}

#[inline(never)]
pub extern "C-unwind" fn c_unwind_abi_panics(cond: bool) {
    if cond {
        panic!("c-unwind abi may unwind");
    }
}

#[inline(never)]
pub fn trigger_double_panic() {
    let _b = Bomb;
    helper_may_panic();
}

#[inline(never)]
pub fn may_drop(b: Bomb) {
    drop(b);
    c_unwind_abi_panics(true);
}

#[inline(never)]
pub extern "C" fn c_abi_with_drop_calls_c_unwind(cond: bool) {
    let _g = DropLogger;
    c_unwind_abi_panics(cond);
}

unsafe extern "C-unwind" {
    fn external_c_unwind_callee();
}

#[inline(never)]
pub fn call_foreign_c_unwind() {
    unsafe { external_c_unwind_callee() };
}

#[inline(never)]
pub fn call_indirect_c_unwind(f: extern "C-unwind" fn(bool), cond: bool) {
    f(cond);
}
"""


EXEC_CASES: dict[str, tuple[str, list[str]]] = {
    "c_unwind_caught_by_catch_unwind": (
        r"""
#[inline(never)]
extern "C-unwind" fn panicking_c_unwind() {
    panic!("unwinding across C-unwind boundary");
}

fn main() {
    let res = std::panic::catch_unwind(|| {
        panicking_c_unwind();
    });
    assert!(res.is_err());
    println!("CAUGHT_C_UNWIND=1");
}
""",
        ["-Cpanic=unwind"],
    ),
    "extern_c_panic_aborts_process": (
        r"""
#[inline(never)]
extern "C" fn panicking_c_abi() {
    panic!("cannot unwind out of extern C");
}

fn main() {
    let _ = std::panic::catch_unwind(|| {
        panicking_c_abi();
    });
    println!("UNREACHABLE_AFTER_C_PANIC");
}
""",
        ["-Cpanic=unwind"],
    ),
    "extern_c_with_drop_runs_drop_before_abort": (
        r"""
struct DropLogger;
impl Drop for DropLogger {
    #[inline(never)]
    fn drop(&mut self) {
        eprintln!("DROP_RAN_IN_C_ABI");
    }
}

#[inline(never)]
extern "C-unwind" fn panicking_c_unwind() {
    panic!("unwinding from C-unwind into extern C");
}

#[inline(never)]
extern "C" fn c_abi_with_drop() {
    let _g = DropLogger;
    panicking_c_unwind();
}

fn main() {
    let _ = std::panic::catch_unwind(|| {
        c_abi_with_drop();
    });
    println!("UNREACHABLE_AFTER_C_DROP_ABORT");
}
""",
        ["-Cpanic=unwind"],
    ),
    "double_panic_in_cleanup_aborts_process": (
        r"""
struct Bomb;
impl Drop for Bomb {
    #[inline(never)]
    fn drop(&mut self) {
        panic!("second panic inside drop");
    }
}

fn main() {
    let _ = std::panic::catch_unwind(|| {
        let _b = Bomb;
        panic!("first panic before drop");
    });
    println!("UNREACHABLE_AFTER_DOUBLE_PANIC");
}
""",
        ["-Cpanic=unwind"],
    ),
    "panic_abort_flag_aborts_process": (
        r"""
#[inline(never)]
extern "C-unwind" fn c_unwind_under_abort() {
    panic!("panic under -Cpanic=abort");
}

fn main() {
    c_unwind_under_abort();
}
""",
        ["-Cpanic=abort"],
    ),
}


TARGET_FUNCTIONS = [
    "c_abi_panics",
    "c_unwind_abi_panics",
    "trigger_double_panic",
    "may_drop",
    "c_abi_with_drop_calls_c_unwind",
    "call_foreign_c_unwind",
    "call_indirect_c_unwind",
]


def run_cmd(cmd: list[str], cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        text=True,
        capture_output=True,
        check=False,
    )


def sanitize_tmp(text: str, tmp_root: Path) -> str:
    return text.replace(str(tmp_root), "<tmp>")


def extract_llvm_functions(ll_text: str, targets: list[str]) -> dict[str, Any]:
    lines = ll_text.splitlines()
    functions: dict[str, str] = {}
    referenced_attr_ids: set[str] = set()

    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("; Function Attrs:") or line.startswith("define "):
            start = i
            if line.startswith("; Function Attrs:") and i + 1 < len(lines) and lines[i + 1].startswith("define "):
                i += 1
                header = lines[i]
            else:
                header = line
            matched_name = None
            for t in targets:
                if f"{len(t)}{t}" in header or f"@{t}(" in header:
                    matched_name = t
                    break
            if header.startswith("define "):
                while i < len(lines) and lines[i] != "}":
                    i += 1
                body = "\n".join(lines[start : i + 1])
                if matched_name is not None:
                    functions[matched_name] = body
                    for m in re.finditer(r"(#\d+)\b", body):
                        referenced_attr_ids.add(m.group(1))
        i += 1

    panic_decls = [
        line
        for line in lines
        if line.startswith("declare ")
        and ("panic_cannot_unwind" in line or "panic_in_cleanup" in line or "external_c_unwind_callee" in line)
    ]
    for decl in panic_decls:
        for m in re.finditer(r"(#\d+)\b", decl):
            referenced_attr_ids.add(m.group(1))

    attrs = [
        line
        for line in lines
        if line.startswith("attributes ")
        and any(line.startswith(f"attributes {aid} =") for aid in referenced_attr_ids)
    ]
    return {
        "functions": functions,
        "panic_and_foreign_decls": panic_decls,
        "attributes": attrs,
    }


def collect_mir_dumps(mir_dir: Path, targets: list[str]) -> dict[str, str]:
    dumps: dict[str, str] = {}
    if not mir_dir.is_dir():
        return dumps
    for path in sorted(mir_dir.iterdir()):
        if not path.is_file() or "AbortUnwindingCalls" not in path.name:
            continue
        if any(f".{t}." in path.name for t in targets):
            dumps[path.name] = path.read_text(encoding="utf-8")
    return dumps


def run_ir_matrix(rustc: str, root: Path) -> dict[str, Any]:
    modes: dict[str, list[str]] = {
        "panic_unwind_mode": ["-Cpanic=unwind"],
        "panic_abort_mode": ["-Cpanic=abort", "-Zpanic_abort_tests"],
        "panic_abort_plain": ["-Cpanic=abort"],
    }
    matrix: dict[str, Any] = {}
    for mode_name, extra_args in modes.items():
        mode_dir = root / mode_name
        mode_dir.mkdir(parents=True, exist_ok=True)
        src = mode_dir / "probe.rs"
        src.write_text(PROBE_LIB_RS, encoding="utf-8")
        mir_dir = mode_dir / "mir_dump"
        mir_dir.mkdir()

        mir_cmd = [
            rustc,
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=probe",
            "-Copt-level=0",
            "-Zmir-opt-level=0",
            "-Zdump-mir=AbortUnwindingCalls",
            f"-Zdump-mir-dir={mir_dir}",
            "--emit=mir",
            "-o",
            str(mode_dir / "probe.mir"),
            str(src),
            *extra_args,
        ]
        mir_res = run_cmd(mir_cmd)

        ll_path = mode_dir / "probe.ll"
        ll_cmd = [
            rustc,
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=probe",
            "-Copt-level=0",
            "-Cdebuginfo=0",
            "--emit=llvm-ir",
            "-o",
            str(ll_path),
            str(src),
            *extra_args,
        ]
        ll_res = run_cmd(ll_cmd)

        ll_extracted: dict[str, Any] = {}
        if ll_res.returncode == 0 and ll_path.is_file():
            ll_extracted = extract_llvm_functions(
                ll_path.read_text(encoding="utf-8"),
                TARGET_FUNCTIONS,
            )

        matrix[mode_name] = {
            "extra_args": extra_args,
            "mir_compile_rc": mir_res.returncode,
            "mir_compile_stderr": sanitize_tmp(mir_res.stderr, root),
            "mir_dumps_abort_unwinding_calls": collect_mir_dumps(mir_dir, TARGET_FUNCTIONS),
            "llvm_compile_rc": ll_res.returncode,
            "llvm_compile_stderr": sanitize_tmp(ll_res.stderr, root),
            "llvm_ir_extracted": ll_extracted,
        }
    return matrix


def run_exec_cases(rustc: str, root: Path) -> dict[str, Any]:
    results: dict[str, Any] = {}
    for case_name, (code, extra_args) in EXEC_CASES.items():
        case_dir = root / f"exec_{case_name}"
        case_dir.mkdir(parents=True, exist_ok=True)
        src = case_dir / "probe.rs"
        exe = case_dir / "probe_bin"
        src.write_text(code, encoding="utf-8")

        comp = run_cmd(
            [
                rustc,
                "--edition=2024",
                "-Copt-level=0",
                "-o",
                str(exe),
                str(src),
                *extra_args,
            ]
        )
        entry: dict[str, Any] = {
            "extra_args": extra_args,
            "compile_returncode": comp.returncode,
            "compile_stderr": sanitize_tmp(comp.stderr, case_dir),
        }
        if comp.returncode == 0 and exe.is_file():
            run = run_cmd([str(exe)])
            entry["run_returncode"] = run.returncode
            if run.returncode < 0:
                try:
                    entry["signal_name"] = signal.Signals(-run.returncode).name
                except ValueError:
                    entry["signal_name"] = f"SIG{-run.returncode}"
            entry["run_stdout"] = run.stdout.strip()
            entry["run_stderr"] = sanitize_tmp(run.stderr.strip(), case_dir)
        results[case_name] = entry
    return results


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rustc", default="rustc", help="Path to rustc binary")
    parser.add_argument(
        "--output",
        default=str(Path(__file__).resolve().parent / "probe_results.json"),
        help="Path to write JSON probe results",
    )
    args = parser.parse_args(argv)

    ver = run_cmd([args.rustc, "--version", "--verbose"])
    if ver.returncode != 0:
        print(f"rustc --version --verbose failed: {ver.stderr}", file=sys.stderr)
        return 1

    with tempfile.TemporaryDirectory(prefix="unwind_probe_") as tmp:
        tmp_path = Path(tmp)
        payload = {
            "observed_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "rustc_version": ver.stdout.strip(),
            "experiments": {
                "a_mir_and_llvm_ir_unwind_matrix": run_ir_matrix(args.rustc, tmp_path),
                "b_native_catch_unwind_vs_c_abi_abort": run_exec_cases(args.rustc, tmp_path),
            },
        }

    out_path = Path(args.output)
    out_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {out_path} ({out_path.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
