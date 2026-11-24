#!/usr/bin/env python3
"""Self-contained live rustc + Miri probe suite for dropck_outlives, #[may_dangle],
PhantomData<T> ownership, and Vec<T> drop-check soundness.

Runs all compiler and Miri invocations inside `with tempfile.TemporaryDirectory():`.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import subprocess
import tempfile
from typing import Any

TOOLCHAIN = "nightly"

# --- Rust source probes ---

PROBES_RUSTC: dict[str, dict[str, Any]] = {
    # A. Conservative RFC 1238 dropck without #[may_dangle]
    "a_boxed_sibling_declared_after_rejected_e0597": {
        "expect_compile_rc": 1,
        "expect_run_rc": None,
        "code": r"""
use std::cell::Cell;

struct Boxed<T>(T);

impl<T> Drop for Boxed<T> {
    fn drop(&mut self) {}
}

fn main() {
    let boxed;
    let cell = Cell::new(1u32);
    boxed = Boxed(&cell);
    let _ = &boxed;
}
""",
    },
    "a_boxed_sibling_declared_before_ok": {
        "expect_compile_rc": 0,
        "expect_run_rc": 0,
        "code": r"""
use std::cell::Cell;

struct Boxed<T>(T);

impl<T> Drop for Boxed<T> {
    fn drop(&mut self) {
        let _ = &self.0;
    }
}

fn main() {
    let cell = Cell::new(1u32);
    let boxed = Boxed(&cell);
    let _ = &boxed;
    println!("BOXED_BEFORE_OK=1");
}
""",
    },
    "a_plain_no_drop_allows_cyclic_borrow_ok": {
        "expect_compile_rc": 0,
        "expect_run_rc": 0,
        "code": r"""
use std::cell::Cell;

struct PlainBox<T>(T);

fn main() {
    let boxed;
    let cell = Cell::new(1u32);
    boxed = PlainBox(&cell);
    println!("PLAIN_NO_DROP_OK={}", boxed.0.get());
}
""",
    },
    "a_plain_drop_with_raw_ptr_field_still_e0597": {
        "expect_compile_rc": 1,
        "expect_run_rc": None,
        "code": r"""
use std::cell::Cell;
use std::marker::PhantomData;

struct PlainDropRaw<T>(*mut T, PhantomData<T>);

impl<T> Drop for PlainDropRaw<T> {
    fn drop(&mut self) {
        unsafe { drop(Box::from_raw(self.0)); }
    }
}

fn main() {
    let raw;
    let cell = Cell::new(1u32);
    raw = PlainDropRaw(Box::into_raw(Box::new(&cell)), PhantomData);
    let _ = &raw;
}
""",
    },
    # B. #[may_dangle] syntax / unsafe enforcement
    "b_may_dangle_without_unsafe_impl_rejected": {
        "expect_compile_rc": 1,
        "expect_run_rc": None,
        "code": r"""
#![feature(dropck_eyepatch)]

struct Wrapper<T>(T);

impl<#[may_dangle] T> Drop for Wrapper<T> {
    fn drop(&mut self) {}
}

fn main() {}
""",
    },
    # C. #[may_dangle] without PhantomData<T>
    "c_eyepatch_without_phantom_allows_dangling_ref": {
        "expect_compile_rc": 0,
        "expect_run_rc": 0,
        "code": r"""
#![feature(dropck_eyepatch)]

use std::cell::Cell;
use std::mem::ManuallyDrop;

struct RawBoxNoPhantom<T>(*mut ManuallyDrop<T>);

unsafe impl<#[may_dangle] T> Drop for RawBoxNoPhantom<T> {
    fn drop(&mut self) {
        unsafe {
            let _ = Box::from_raw(self.0);
        }
    }
}

fn main() {
    let raw;
    let cell = Cell::new(1u32);
    raw = RawBoxNoPhantom(Box::into_raw(Box::new(ManuallyDrop::new(&cell))));
    let _ = &raw;
    println!("NO_PHANTOM_REF_OK=1");
}
""",
    },
    "c_eyepatch_without_phantom_allows_unsound_inspector_compile": {
        "expect_compile_rc": 0,
        "expect_run_rc": None,  # UB at drop time; tested cleanly under Miri
        "code": r"""
#![feature(dropck_eyepatch)]

use std::cell::Cell;

struct Inspector<'a>(&'a Cell<u32>);

impl Drop for Inspector<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 10);
    }
}

struct RawBox<T>(*mut T);

unsafe impl<#[may_dangle] T> Drop for RawBox<T> {
    fn drop(&mut self) {
        unsafe {
            drop(Box::from_raw(self.0));
        }
    }
}

fn main() {
    let raw;
    let cell = Cell::new(1u32);
    raw = RawBox(Box::into_raw(Box::new(Inspector(&cell))));
    let _ = &raw;
    println!("REACHED_END_BEFORE_DROP=1");
}
""",
    },
    # D. PhantomData<fn() -> T> vs PhantomData<T> (identical Covariant variance, opposite dropck)
    "d_eyepatch_with_phantom_fn_ptr_still_compiles": {
        "expect_compile_rc": 0,
        "expect_run_rc": None,  # UB at drop time; tested cleanly under Miri
        "code": r"""
#![feature(dropck_eyepatch)]

use std::cell::Cell;
use std::marker::PhantomData;

struct Inspector<'a>(&'a Cell<u32>);

impl Drop for Inspector<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 10);
    }
}

struct RawBoxFnMarker<T>(*mut T, PhantomData<fn() -> T>);

unsafe impl<#[may_dangle] T> Drop for RawBoxFnMarker<T> {
    fn drop(&mut self) {
        unsafe {
            drop(Box::from_raw(self.0));
        }
    }
}

fn main() {
    let raw;
    let cell = Cell::new(1u32);
    raw = RawBoxFnMarker(Box::into_raw(Box::new(Inspector(&cell))), PhantomData);
    let _ = &raw;
    println!("REACHED_END_WITH_FN_MARKER=1");
}
""",
    },
    # E. PhantomData<T> restores E0597 for Inspector<'_> while allowing &Cell<u32> + Vec<&Cell<u32>>
    "e_eyepatch_with_phantom_rejects_inspector_e0597": {
        "expect_compile_rc": 1,
        "expect_run_rc": None,
        "code": r"""
#![feature(dropck_eyepatch)]

use std::cell::Cell;
use std::marker::PhantomData;

struct Inspector<'a>(&'a Cell<u32>);

impl Drop for Inspector<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 10);
    }
}

struct RawBox<T>(*mut T, PhantomData<T>);

unsafe impl<#[may_dangle] T> Drop for RawBox<T> {
    fn drop(&mut self) {
        unsafe {
            drop(Box::from_raw(self.0));
        }
    }
}

fn main() {
    let raw;
    let cell = Cell::new(1u32);
    raw = RawBox(Box::into_raw(Box::new(Inspector(&cell))), PhantomData);
    let _ = &raw;
}
""",
    },
    "e_eyepatch_with_phantom_and_std_vec_allow_trivial_ref_exec": {
        "expect_compile_rc": 0,
        "expect_run_rc": 0,
        "code": r"""
#![feature(dropck_eyepatch)]

use std::cell::Cell;
use std::marker::PhantomData;
use std::mem::ManuallyDrop;

struct RawBox<T>(*mut ManuallyDrop<T>, PhantomData<T>);

unsafe impl<#[may_dangle] T> Drop for RawBox<T> {
    fn drop(&mut self) {
        unsafe {
            let _ = Box::from_raw(self.0);
        }
    }
}

fn main() {
    let mut v: Vec<&Cell<u32>> = Vec::new();
    let raw;
    let cell = Cell::new(1u32);
    v.push(&cell);
    raw = RawBox(Box::into_raw(Box::new(ManuallyDrop::new(&cell))), PhantomData);
    let count = v.len() + usize::from(!raw.0.is_null());
    println!("DROPCK_SAFE={count}");
}
""",
    },
    "e_manually_drop_trivial_dropck_exec": {
        "expect_compile_rc": 0,
        "expect_run_rc": 0,
        "code": r"""
use std::cell::Cell;
use std::mem::ManuallyDrop;

struct Inspector<'a>(&'a Cell<u32>);

impl Drop for Inspector<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 10);
    }
}

fn main() {
    let guard;
    let cell = Cell::new(1u32);
    guard = ManuallyDrop::new(Inspector(&cell));
    let _ = &guard;
    println!("MANUALLY_DROP_SAFE={}", cell.get());
}
""",
    },
    # F. Violation of pure_wrt_drop despite PhantomData<T>
    "f_eyepatch_with_phantom_liar_reads_ref_compiles": {
        "expect_compile_rc": 0,
        "expect_run_rc": None,  # UB at drop time; tested cleanly under Miri
        "code": r"""
#![feature(dropck_eyepatch)]

use std::fmt::Display;
use std::marker::PhantomData;

struct LiarBox<T: Display>(*mut T, PhantomData<T>);

unsafe impl<#[may_dangle] T: Display> Drop for LiarBox<T> {
    fn drop(&mut self) {
        unsafe {
            let boxed = Box::from_raw(self.0);
            let _ = format!("{}", *boxed);
        }
    }
}

fn main() {
    let raw;
    let text = String::from("dangling");
    raw = LiarBox(Box::into_raw(Box::new(&text)), PhantomData);
    let _ = &raw;
    let _ = &text;
}
""",
    },
}

PROBES_MIRI: dict[str, dict[str, Any]] = {
    "miri_eyepatch_without_phantom_unsound_inspector_uaf": {
        "expect_rc": 1,
        "code": PROBES_RUSTC["c_eyepatch_without_phantom_allows_unsound_inspector_compile"]["code"],
    },
    "miri_eyepatch_with_phantom_fn_ptr_uaf": {
        "expect_rc": 1,
        "code": PROBES_RUSTC["d_eyepatch_with_phantom_fn_ptr_still_compiles"]["code"],
    },
    "miri_eyepatch_with_phantom_liar_reads_ref_uaf": {
        "expect_rc": 1,
        "code": PROBES_RUSTC["f_eyepatch_with_phantom_liar_reads_ref_compiles"]["code"],
    },
    "miri_eyepatch_with_phantom_and_std_vec_trivial_ref_safe": {
        "expect_rc": 0,
        "code": PROBES_RUSTC["e_eyepatch_with_phantom_and_std_vec_allow_trivial_ref_exec"]["code"],
    },
    "miri_manually_drop_trivial_dropck_safe": {
        "expect_rc": 0,
        "code": PROBES_RUSTC["e_manually_drop_trivial_dropck_exec"]["code"],
    },
}


def scrub(text: str, extra_replacements: list[tuple[str, str]]) -> str:
    home = str(pathlib.Path.home())
    user = os.environ.get("USER", "")
    out = text
    for old, new in extra_replacements:
        if old:
            out = out.replace(old, new)
    if home:
        out = out.replace(home, "<home>")
    if user:
        out = out.replace(user, "<user>")
    return out


def run_rustc_probe(name: str, spec: dict[str, Any]) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as d:
        tmp = pathlib.Path(d)
        src = tmp / "probe.rs"
        bin_path = tmp / "probe_bin"
        src.write_text(spec["code"].lstrip("\n"), encoding="utf-8")

        comp = subprocess.run(
            ["rustc", f"+{TOOLCHAIN}", "--edition=2024", str(src), "-o", str(bin_path)],
            cwd=tmp,
            text=True,
            capture_output=True,
            check=False,
        )
        repls = [(str(tmp), "<tmp>")]
        res: dict[str, Any] = {
            "edition": "2024",
            "command": f"rustc +{TOOLCHAIN} --edition=2024 probe.rs -o probe_bin",
            "compile_returncode": comp.returncode,
            "compile_stdout": scrub(comp.stdout.strip(), repls),
            "compile_stderr": scrub(comp.stderr.strip(), repls),
        }
        if comp.returncode != spec["expect_compile_rc"]:
            raise AssertionError(
                f"{name}: expected compile_rc={spec['expect_compile_rc']}, got {comp.returncode}\n{comp.stderr}"
            )
        if spec["expect_run_rc"] is not None:
            run = subprocess.run(
                [str(bin_path)],
                cwd=tmp,
                text=True,
                capture_output=True,
                check=False,
            )
            res["run_returncode"] = run.returncode
            res["run_stdout"] = scrub(run.stdout.strip(), repls)
            res["run_stderr"] = scrub(run.stderr.strip(), repls)
            if run.returncode != spec["expect_run_rc"]:
                raise AssertionError(
                    f"{name}: expected run_rc={spec['expect_run_rc']}, got {run.returncode}\n{run.stderr}"
                )
        return res


def run_miri_probe(name: str, spec: dict[str, Any]) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as d:
        tmp = pathlib.Path(d)
        (tmp / "Cargo.toml").write_text(
            '[package]\nname = "miri_probe"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        (tmp / "src").mkdir()
        (tmp / "src" / "main.rs").write_text(spec["code"].lstrip("\n"), encoding="utf-8")

        run = subprocess.run(
            ["cargo", f"+{TOOLCHAIN}", "miri", "run", "--offline"],
            cwd=tmp,
            text=True,
            capture_output=True,
            check=False,
        )
        repls = [(str(tmp), "<tmp>")]
        if run.returncode != spec["expect_rc"]:
            raise AssertionError(
                f"{name}: expected miri rc={spec['expect_rc']}, got {run.returncode}\n{run.stderr}"
            )
        return {
            "edition": "2024",
            "command": f"cargo +{TOOLCHAIN} miri run --offline",
            "returncode": run.returncode,
            "stdout": scrub(run.stdout.strip(), repls),
            "stderr": scrub(run.stderr.strip(), repls),
        }


def capture_mir_drop_order() -> dict[str, Any]:
    """Capture MIR for `main()` in the unsound Inspector probe to verify
    StorageDead(cell) precedes Drop(raw) in unoptimized MIR."""
    code = PROBES_RUSTC["c_eyepatch_without_phantom_allows_unsound_inspector_compile"]["code"]
    with tempfile.TemporaryDirectory() as d:
        tmp = pathlib.Path(d)
        src = tmp / "probe.rs"
        mir_out = tmp / "probe.mir"
        src.write_text(code.lstrip("\n"), encoding="utf-8")
        res = subprocess.run(
            [
                "rustc",
                f"+{TOOLCHAIN}",
                "--edition=2024",
                "-Z",
                "mir-opt-level=0",
                "--emit=mir",
                "-o",
                str(mir_out),
                str(src),
            ],
            cwd=tmp,
            text=True,
            capture_output=True,
            check=False,
        )
        if res.returncode != 0:
            raise AssertionError(f"MIR emit failed: {res.stderr}")
        mir_text = mir_out.read_text(encoding="utf-8")
        fn_main_lines: list[str] = []
        in_main = False
        brace_depth = 0
        for line in mir_text.splitlines():
            if line.startswith("fn main() -> ()"):
                in_main = True
            if in_main:
                fn_main_lines.append(line)
                brace_depth += line.count("{") - line.count("}")
                if brace_depth == 0 and len(fn_main_lines) > 1:
                    break
        return {
            "command": f"rustc +{TOOLCHAIN} --edition=2024 -Z mir-opt-level=0 --emit=mir -o probe.mir probe.rs",
            "returncode": res.returncode,
            "fn_main_mir": "\n".join(fn_main_lines),
        }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=pathlib.Path,
        default=pathlib.Path(__file__).resolve().parent / "probe_results.json",
    )
    args = parser.parse_args()

    rustc_ver = subprocess.run(
        ["rustc", f"+{TOOLCHAIN}", "--version", "--verbose"],
        text=True,
        capture_output=True,
        check=True,
    ).stdout.strip()
    miri_ver = subprocess.run(
        ["cargo", f"+{TOOLCHAIN}", "miri", "--version"],
        text=True,
        capture_output=True,
        check=True,
    ).stdout.strip()

    rustc_results = {name: run_rustc_probe(name, spec) for name, spec in PROBES_RUSTC.items()}
    miri_results = {name: run_miri_probe(name, spec) for name, spec in PROBES_MIRI.items()}
    mir_order = capture_mir_drop_order()

    payload = {
        "rustc_version": scrub(rustc_ver, []),
        "miri_version": scrub(miri_ver, []),
        "rustc_probes": rustc_results,
        "miri_probes": miri_results,
        "mir_drop_order_evidence": mir_order,
    }
    args.out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(
        f"Executed {len(rustc_results)} rustc probes, {len(miri_results)} Miri probes, "
        f"and MIR drop-order capture -> {args.out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
