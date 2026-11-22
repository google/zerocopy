#!/usr/bin/env python3
"""Differential rustc probe for const_trait_impl, const_destruct, and adt_const_params.

Executes a 16-case matrix (9 baseline cases ct_01..ct_09 matching the 1.102-nightly
baseline plus 7 discriminating cases ct_10..ct_16 covering syntax evolution,
BoundConstness lattice ordering, const Drop confluence, ManuallyDrop, and
float/raw-pointer CTFE pathologies) across `-Z next-solver=globally` and
`-Z next-solver=no`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

ERROR_CODE_RE = re.compile(r"error\[(E\d{4})\]")


CASES: dict[str, dict[str, Any]] = {
    "ct_01_const_trait_bracket_const_bound_ctfe_and_runtime": {
        "expect_compile": True,
        "code": r"""
#![feature(const_trait_impl)]

pub const trait Combine {
    fn combine(self, other: Self) -> Self;
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ConstVal(pub u32);

const impl Combine for ConstVal {
    fn combine(self, other: Self) -> Self {
        ConstVal(self.0 + other.0)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NonConst(pub u32);

impl Combine for NonConst {
    fn combine(self, other: Self) -> Self {
        NonConst(self.0 + other.0)
    }
}

pub const fn apply<T: [const] Combine>(a: T, b: T) -> T {
    a.combine(b)
}

pub const CTFE: ConstVal = apply(ConstVal(20), ConstVal(22));

fn main() {
    let rt_const = apply(ConstVal(20), ConstVal(22));
    let rt_nonconst = apply(NonConst(20), NonConst(22));
    print!("CTFE={} RT_CONST={} RT_NONCONST={}", CTFE.0, rt_const.0, rt_nonconst.0);
}
""".lstrip(),
    },
    "ct_02_non_const_impl_rejected_in_const_context": {
        "expect_compile": False,
        "code": r"""
#![feature(const_trait_impl)]

pub const trait Combine {
    fn combine(self, other: Self) -> Self;
}

#[derive(Copy, Clone)]
pub struct NonConst(pub u32);

impl Combine for NonConst {
    fn combine(self, other: Self) -> Self {
        NonConst(self.0 + other.0)
    }
}

pub const fn apply<T: [const] Combine>(a: T, b: T) -> T { a.combine(b) }
pub const BAD: NonConst = apply(NonConst(1), NonConst(2));

fn main() {}
""".lstrip(),
    },
    "ct_03_generic_const_fn_drop_without_const_destruct_rejected": {
        "expect_compile": False,
        "code": r"""
pub const fn drop_generic_in_const<T>(_x: T) {}

fn main() {}
""".lstrip(),
    },
    "ct_04_generic_const_fn_with_const_destruct_accepted": {
        "expect_compile": True,
        "code": r"""
#![feature(const_trait_impl, const_destruct)]

use std::marker::Destruct;

pub const fn drop_generic_in_const<T: [const] Destruct>(_x: T) -> u32 {
    77
}

pub struct ConstDroppable(pub u32);
const impl Drop for ConstDroppable {
    fn drop(&mut self) {}
}

pub struct NonConstDroppable(pub u32);
impl Drop for NonConstDroppable {
    fn drop(&mut self) {}
}

pub const CTFE_OK: u32 = drop_generic_in_const(ConstDroppable(1));

fn main() {
    let rt = drop_generic_in_const(NonConstDroppable(2));
    print!("CONST_DESTRUCT_OK={} RT={}", CTFE_OK, rt);
}
""".lstrip(),
    },
    "ct_05_conflicting_const_and_nonconst_impl_coherence_rejected": {
        "expect_compile": False,
        "code": r"""
#![feature(const_trait_impl)]
pub const trait MyOp { fn op(self) -> u32; }
const impl MyOp for u32 { fn op(self) -> u32 { 1 } }
impl MyOp for u32 { fn op(self) -> u32 { 2 } }
fn main() {}
""".lstrip(),
    },
    "ct_06_adt_const_params_structural_eq_accepted": {
        "expect_compile": True,
        "code": r"""
#![feature(adt_const_params)]

use std::marker::ConstParamTy;

#[derive(PartialEq, Eq, ConstParamTy)]
pub enum Mode {
    Fast,
    Checked,
}

#[derive(PartialEq, Eq, ConstParamTy)]
pub struct Config {
    pub mode: Mode,
    pub stride: u8,
}

pub const FAST_CFG: Config = Config { mode: Mode::Fast, stride: 4 };
pub const CHECKED_CFG: Config = Config { mode: Mode::Checked, stride: 1 };

pub fn eval<const C: Config>(x: u32) -> u32 {
    match C.mode {
        Mode::Fast => x * (C.stride as u32),
        Mode::Checked => C.stride as u32,
    }
}

fn main() {
    print!("FAST={} CHECKED={}", eval::<FAST_CFG>(10), eval::<CHECKED_CFG>(10));
}
""".lstrip(),
    },
    "ct_07_adt_const_params_float_field_rejected": {
        "expect_compile": False,
        "code": r"""
#![feature(adt_const_params)]
use std::marker::ConstParamTy;

#[derive(PartialEq, Eq, ConstParamTy)]
pub struct BadFloatParam(pub f32);

fn main() {}
""".lstrip(),
    },
    "ct_08_adt_const_params_raw_ptr_rejected": {
        "expect_compile": False,
        "code": r"""
#![feature(adt_const_params)]
use std::marker::ConstParamTy;

#[derive(PartialEq, Eq, ConstParamTy)]
pub struct BadPtrParam(pub *const u8);

fn main() {}
""".lstrip(),
    },
    "ct_09_unsized_const_params_slice_str_valtree": {
        "expect_compile": True,
        "code": r"""
#![feature(adt_const_params, unsized_const_params)]

pub struct Route<const PATH: &'static str>;

impl<const PATH: &'static str> Route<PATH> {
    pub const fn len() -> usize {
        PATH.len()
    }
}

fn main() {
    print!("LEN_API={} LEN_ROOT={}", Route::<"/api/v1/x">::len(), Route::<"/">::len());
}
""".lstrip(),
    },
    "ct_10_legacy_impl_const_syntax_evolution": {
        "expect_compile": True,
        "code": r"""
#![feature(const_trait_impl)]

pub const trait LegacyOp {
    fn tag(self) -> u32;
}

impl const LegacyOp for u32 {
    fn tag(self) -> u32 {
        self + 5
    }
}

pub const fn run_tag<T: [const] LegacyOp>(x: T) -> u32 {
    x.tag()
}

pub const C: u32 = run_tag(10u32);

fn main() {
    print!("LEGACY_IMPL_CONST={}", C);
}
""".lstrip(),
    },
    "ct_11_always_const_bound_rejects_nonconst_at_runtime": {
        "expect_compile": False,
        "code": r"""
#![feature(const_trait_impl)]

pub const trait Op {
    fn op(self) -> u32;
}

pub struct RuntimeOnly(pub u32);
impl Op for RuntimeOnly {
    fn op(self) -> u32 { self.0 }
}

pub fn require_always_const<T: const Op>(x: T) -> u32 {
    x.op()
}

fn main() {
    let _ = require_always_const(RuntimeOnly(7));
}
""".lstrip(),
    },
    "ct_12_maybe_bound_cannot_satisfy_always_const_goal": {
        "expect_compile": False,
        "code": r"""
#![feature(const_trait_impl)]

pub const trait Op {
    fn op(self) -> u32;
}

pub const fn need_always<T: const Op>(x: T) -> u32 {
    x.op()
}

pub const fn only_maybe<T: [const] Op>(x: T) -> u32 {
    need_always(x)
}

fn main() {}
""".lstrip(),
    },
    "ct_13_nonconst_drop_rejected_in_const_item_with_const_destruct": {
        "expect_compile": False,
        "code": r"""
#![feature(const_trait_impl, const_destruct)]

use std::marker::Destruct;

pub struct NonConstDrop(pub u32);
impl Drop for NonConstDrop {
    fn drop(&mut self) {}
}

pub const fn drop_any<T: [const] Destruct>(_x: T) -> u32 {
    1
}

pub const BAD_DROP: u32 = drop_any(NonConstDrop(9));

fn main() {}
""".lstrip(),
    },
    "ct_14_const_drop_executes_confluently_in_ctfe_and_runtime": {
        "expect_compile": True,
        "code": r"""
#![feature(const_trait_impl, const_destruct)]

pub struct DropMut<'a> {
    pub slot: &'a mut u32,
    pub delta: u32,
}

const impl<'a> Drop for DropMut<'a> {
    fn drop(&mut self) {
        *self.slot += self.delta;
    }
}

pub const fn run_with_drop(init: u32) -> u32 {
    let mut acc = init;
    {
        let _guard = DropMut { slot: &mut acc, delta: 57 };
    }
    acc
}

pub const CTFE_DROP: u32 = run_with_drop(42);

fn main() {
    let rt_drop = run_with_drop(42);
    print!("CTFE_DROP={} RT_DROP={}", CTFE_DROP, rt_drop);
}
""".lstrip(),
    },
    "ct_15_manually_drop_trivially_const_destruct": {
        "expect_compile": True,
        "code": r"""
#![feature(const_trait_impl, const_destruct)]

use std::mem::ManuallyDrop;

pub struct NonConstDrop(pub u32);
impl Drop for NonConstDrop {
    fn drop(&mut self) {}
}

pub const fn accept_manually_drop<T>(x: ManuallyDrop<T>) -> u32 {
    let _ = x;
    13
}

pub const MD_CTFE: u32 = accept_manually_drop(ManuallyDrop::new(NonConstDrop(5)));

fn main() {
    let md_rt = accept_manually_drop(ManuallyDrop::new(NonConstDrop(5)));
    print!("MD_CTFE={} MD_RT={}", MD_CTFE, md_rt);
}
""".lstrip(),
    },
    "ct_16_ctfe_raw_ptr_comparison_rejected": {
        "expect_compile": False,
        "code": r"""
static A: u8 = 1;
static B: u8 = 2;

pub const PTR_EQ: bool = (&A as *const u8) == (&B as *const u8);

fn main() {
    println!("{}", PTR_EQ);
}
""".lstrip(),
    },
    "ct_17_float_signed_zero_and_nan_structural_mismatch": {
        "expect_compile": True,
        "code": r"""
pub const POS_ZERO: f32 = 0.0;
pub const NEG_ZERO: f32 = -0.0;
pub const NAN_VAL: f32 = f32::NAN;

pub const EQ_ZEROS: bool = POS_ZERO == NEG_ZERO;
pub const BITS_EQ_ZEROS: bool = POS_ZERO.to_bits() == NEG_ZERO.to_bits();
pub const NAN_EQ_SELF: bool = NAN_VAL == NAN_VAL;

fn main() {
    print!(
        "EQ_ZEROS={} BITS_EQ_ZEROS={} POS_BITS={:#010x} NEG_BITS={:#010x} NAN_EQ_SELF={}",
        EQ_ZEROS,
        BITS_EQ_ZEROS,
        POS_ZERO.to_bits(),
        NEG_ZERO.to_bits(),
        NAN_EQ_SELF,
    );
}
""".lstrip(),
    },
    "ct_18_legacy_tilde_const_bound_still_parsed_as_maybe": {
        "expect_compile": True,
        "code": r"""
#![feature(const_trait_impl)]

pub const trait TildeOp {
    fn double(self) -> u32;
}

const impl TildeOp for u32 {
    fn double(self) -> u32 {
        self * 2
    }
}

pub const fn apply_tilde<T: ~const TildeOp>(x: T) -> u32 {
    x.double()
}

pub const RES: u32 = apply_tilde(21u32);

fn main() {
    print!("TILDE_CONST={}", RES);
}
""".lstrip(),
    },
}


def find_rustc() -> str:
    env_rustc = os.environ.get("RUSTC")
    if env_rustc:
        return env_rustc
    cargo_rustc = Path.home() / ".cargo" / "bin" / "rustc"
    if cargo_rustc.exists():
        return str(cargo_rustc)
    return "rustc"


def sanitize_stderr(stderr: str, src_path: Path) -> str:
    text = stderr.replace(str(src_path), "<tmp>")
    text = re.sub(r"[^\s]+/lib/rustlib/src/rust/", "<sysroot>/", text)
    text = text.replace(str(Path.home()), "<home>")
    lines = text.splitlines()
    return "\n".join(lines[:35]) + ("\n" if lines else "")


def run_case(rustc: str, name: str, code: str, solver_flags: list[str], edition: str) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix=f"ctrait_{name}_") as td:
        td_path = Path(td)
        src = td_path / "main.rs"
        bin_path = td_path / "out_bin"
        src.write_text(code, encoding="utf-8")

        cmd = [rustc, f"--edition={edition}", *solver_flags, str(src), "-o", str(bin_path)]
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        error_codes = sorted(set(ERROR_CODE_RE.findall(proc.stderr)))
        entry: dict[str, Any] = {
            "flags": solver_flags,
            "rc": proc.returncode,
            "error_codes": error_codes,
            "stderr_head": sanitize_stderr(proc.stderr, src),
        }
        if proc.returncode == 0 and bin_path.exists():
            run_proc = subprocess.run([str(bin_path)], capture_output=True, text=True, timeout=30)
            entry["run_rc"] = run_proc.returncode
            entry["run_stdout"] = run_proc.stdout
        return entry


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, help="Optional JSON output path")
    parser.add_argument("--edition", default="2024", help="Rust edition (default: 2024)")
    args = parser.parse_args()

    rustc = find_rustc()
    ver = subprocess.run([rustc, "--version", "--verbose"], capture_output=True, text=True, check=True)
    results: dict[str, Any] = {
        "rustc_version": ver.stdout.strip(),
        "edition": args.edition,
        "solver_divergences": [],
        "cases": {},
    }

    solvers = [
        ("next_solver", ["-Z", "next-solver=globally"]),
        ("old_solver", ["-Z", "next-solver=no"]),
    ]

    for case_name, spec in CASES.items():
        case_out: dict[str, Any] = {}
        for label, flags in solvers:
            case_out[label] = run_case(rustc, case_name, spec["code"], flags, args.edition)
        ns = case_out["next_solver"]
        os_ = case_out["old_solver"]
        if (
            ns["rc"] != os_["rc"]
            or ns["error_codes"] != os_["error_codes"]
            or ns.get("run_stdout") != os_.get("run_stdout")
        ):
            results["solver_divergences"].append(
                {
                    "case": case_name,
                    "next_solver": {"rc": ns["rc"], "error_codes": ns["error_codes"]},
                    "old_solver": {"rc": os_["rc"], "error_codes": os_["error_codes"]},
                }
            )
        results["cases"][case_name] = case_out

    payload = json.dumps(results, indent=2) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(payload, encoding="utf-8")
    else:
        sys.stdout.write(payload)

    print(
        f"Executed {len(CASES)} cases x 2 solvers; divergences={len(results['solver_divergences'])}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
