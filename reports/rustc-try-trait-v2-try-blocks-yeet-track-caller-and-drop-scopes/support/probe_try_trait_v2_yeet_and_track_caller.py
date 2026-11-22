#!/usr/bin/env python3
"""Live rustc, MIR, LLVM IR, and Miri probe for Try Trait v2, try blocks,
do yeet, #[track_caller] forwarding, Infallible/!, and Edition 2021 vs 2024
tail temporary drop scopes.

Usage:
    python3 probe_try_trait_v2_yeet_and_track_caller.py [--out <path.json>]
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


def run_cmd(
    cmd: list[str],
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 180,
) -> subprocess.CompletedProcess[str]:
    merged_env = os.environ.copy()
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    if cargo_bin not in merged_env.get("PATH", "").split(":"):
        merged_env["PATH"] = f"{cargo_bin}:{merged_env.get('PATH', '')}"
    if env:
        merged_env.update(env)
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=merged_env,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )


def scrub(text: str, sysroot_src: str, tmpdir: str) -> str:
    out = text.replace(sysroot_src, "<RUST_SYSROOT_SRC>")
    out = out.replace(tmpdir, "<TMP>")
    out = re.sub(r"/rustc/[0-9a-f]{40}/", "<RUST_SYSROOT_SRC>/", out)
    return out


def probe1_track_caller(sysroot_src: str) -> dict[str, Any]:
    main_rs = """#![feature(try_trait_v2, try_trait_v2_residual, try_trait_v2_yeet, try_blocks, try_blocks_heterogeneous, yeet_expr)]

use std::ops::{ControlFlow, FromResidual, Residual, Try, Yeet};
use std::panic::Location;

#[derive(Debug)]
struct SubErr(u32);

#[derive(Debug)]
struct TrackedErr {
    code: u32,
    loc: &'static Location<'static>,
}

impl From<SubErr> for TrackedErr {
    #[track_caller]
    fn from(e: SubErr) -> Self {
        TrackedErr {
            code: e.0,
            loc: Location::caller(),
        }
    }
}

#[derive(Debug)]
enum MyTry<T> {
    Ok(T),
    Err(u32, &'static Location<'static>),
}

#[derive(Debug)]
struct MyResidual(u32);

impl<T> Try for MyTry<T> {
    type Output = T;
    type Residual = MyResidual;

    fn from_output(output: Self::Output) -> Self {
        MyTry::Ok(output)
    }

    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            MyTry::Ok(v) => ControlFlow::Continue(v),
            MyTry::Err(c, _) => ControlFlow::Break(MyResidual(c)),
        }
    }
}

impl<T> FromResidual<MyResidual> for MyTry<T> {
    #[track_caller]
    fn from_residual(r: MyResidual) -> Self {
        MyTry::Err(r.0, Location::caller())
    }
}

impl<T> Residual<T> for MyResidual {
    type TryType = MyTry<T>;
}

impl<T> FromResidual<Yeet<SubErr>> for MyTry<T> {
    #[track_caller]
    fn from_residual(Yeet(e): Yeet<SubErr>) -> Self {
        MyTry::Err(e.0, Location::caller())
    }
}

#[inline(never)]
fn mk_sub_err() -> Result<u32, SubErr> {
    Err(SubErr(7))
}

#[inline(never)]
fn mk_my_err() -> MyTry<u32> {
    MyTry::Err(9, Location::caller())
}

#[inline(never)]
fn case_fn_result_qmark() -> (u32, Result<u32, TrackedErr>) {
    let expected = line!() + 1;
    let res = (|| -> Result<u32, TrackedErr> {
        let v = mk_sub_err()?;
        Ok(v)
    })();
    (expected + 1, res)
}

#[inline(never)]
fn case_hetero_result_qmark() -> (u32, Result<u32, TrackedErr>) {
    let expected = line!() + 2;
    let res = try bikeshed Result<u32, TrackedErr> {
        mk_sub_err()?
    };
    (expected, res)
}

#[inline(never)]
fn case_homo_custom_qmark() -> (u32, MyTry<u32>) {
    let expected = line!() + 2;
    let res = try {
        mk_my_err()?
    };
    (expected, res)
}

#[inline(never)]
fn case_hetero_custom_qmark() -> (u32, MyTry<u32>) {
    let expected = line!() + 2;
    let res = try bikeshed MyTry<u32> {
        mk_my_err()?
    };
    (expected, res)
}

#[inline(never)]
fn case_fn_result_yeet() -> (u32, Result<u32, TrackedErr>) {
    let expected = line!() + 2;
    let res = (|| -> Result<u32, TrackedErr> {
        do yeet SubErr(11)
    })();
    (expected, res)
}

#[inline(never)]
fn case_homo_result_yeet() -> (u32, Result<u32, TrackedErr>) {
    let expected = line!() + 2;
    let res: Result<u32, TrackedErr> = try {
        do yeet SubErr(12)
    };
    (expected, res)
}

#[inline(never)]
fn case_hetero_result_yeet() -> (u32, Result<u32, TrackedErr>) {
    let expected = line!() + 2;
    let res = try bikeshed Result<u32, TrackedErr> {
        do yeet SubErr(13)
    };
    (expected, res)
}

#[inline(never)]
fn case_fn_custom_yeet() -> (u32, MyTry<u32>) {
    let expected = line!() + 2;
    let res = (|| -> MyTry<u32> {
        do yeet SubErr(14)
    })();
    (expected, res)
}

#[inline(never)]
fn case_homo_custom_yeet() -> (u32, MyTry<u32>) {
    let expected = line!() + 2;
    let res: MyTry<u32> = try {
        do yeet SubErr(15)
    };
    (expected, res)
}

#[inline(never)]
fn case_hetero_custom_yeet() -> (u32, MyTry<u32>) {
    let expected = line!() + 2;
    let res = try bikeshed MyTry<u32> {
        do yeet SubErr(16)
    };
    (expected, res)
}

fn report(name: &str, expected: u32, loc: &'static Location<'static>) {
    let got_file = loc.file();
    let got_line = loc.line();
    let in_user = got_file.ends_with("src/main.rs");
    let exact_line = in_user && got_line == expected;
    println!(
        "CASE={name} in_user={in_user} exact_line={exact_line} got_file={got_file} got_line={got_line} expected_line={expected}"
    );
}

fn main() {
    let (exp, r) = case_fn_result_qmark();
    report("fn_result_qmark", exp, r.unwrap_err().loc);

    let (exp, r) = case_hetero_result_qmark();
    report("hetero_result_qmark", exp, r.unwrap_err().loc);

    let (exp, r) = case_homo_custom_qmark();
    let MyTry::Err(_, loc) = r else { panic!() };
    report("homo_custom_qmark", exp, loc);

    let (exp, r) = case_hetero_custom_qmark();
    let MyTry::Err(_, loc) = r else { panic!() };
    report("hetero_custom_qmark", exp, loc);

    let (exp, r) = case_fn_result_yeet();
    report("fn_result_yeet", exp, r.unwrap_err().loc);

    let (exp, r) = case_homo_result_yeet();
    report("homo_result_yeet", exp, r.unwrap_err().loc);

    let (exp, r) = case_hetero_result_yeet();
    report("hetero_result_yeet", exp, r.unwrap_err().loc);

    let (exp, r) = case_fn_custom_yeet();
    let MyTry::Err(_, loc) = r else { panic!() };
    report("fn_custom_yeet", exp, loc);

    let (exp, r) = case_homo_custom_yeet();
    let MyTry::Err(_, loc) = r else { panic!() };
    report("homo_custom_yeet", exp, loc);

    let (exp, r) = case_hetero_custom_yeet();
    let MyTry::Err(_, loc) = r else { panic!() };
    report("hetero_custom_yeet", exp, loc);
}
"""
    with tempfile.TemporaryDirectory(prefix="probe_tc_") as td:
        root = Path(td)
        (root / "src").mkdir()
        (root / "Cargo.toml").write_text(
            '[package]\nname = "probe_tc"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        (root / "src" / "main.rs").write_text(main_rs, encoding="utf-8")

        dev = run_cmd(["cargo", "run", "--quiet"], cwd=root)
        rel = run_cmd(["cargo", "run", "--quiet", "--release"], cwd=root)
        miri = run_cmd(
            ["cargo", "miri", "run", "--quiet"],
            cwd=root,
            env={"MIRIFLAGS": "-Zmiri-tree-borrows"},
            timeout=240,
        )

        def clean_lines(s: str) -> list[str]:
            return [scrub(line, sysroot_src, td) for line in s.strip().splitlines() if line.strip()]

        return {
            "dev_rc": dev.returncode,
            "dev_stdout": clean_lines(dev.stdout),
            "dev_stderr_head": scrub(dev.stderr, sysroot_src, td)[:500] if dev.returncode != 0 else "",
            "release_rc": rel.returncode,
            "release_stdout": clean_lines(rel.stdout),
            "release_stderr_head": scrub(rel.stderr, sysroot_src, td)[:500] if rel.returncode != 0 else "",
            "miri_tb_rc": miri.returncode,
            "miri_tb_stdout": clean_lines(miri.stdout),
            "miri_tb_stderr_head": scrub(miri.stderr, sysroot_src, td)[:500] if miri.returncode != 0 else "",
        }


def probe2_scope_and_conversion(sysroot_src: str) -> dict[str, Any]:
    cases: dict[str, tuple[str, bool]] = {
        "homo_unannotated_ok": (
            """#![feature(try_blocks)]
fn main() {
    let x = try {
        let a = Some(41u32)?;
        a + 1
    };
    assert_eq!(x, Some(42));
}
""",
            True,
        ),
        "homo_from_conv_rejected": (
            """#![feature(try_blocks)]
struct SubErr;
struct SuperErr;
impl From<SubErr> for SuperErr { fn from(_: SubErr) -> Self { SuperErr } }
fn main() {
    let _x: Result<u32, SuperErr> = try { Err::<u32, SubErr>(SubErr)? };
}
""",
            False,
        ),
        "homo_yeet_from_conv_accepted": (
            """#![feature(try_blocks, yeet_expr)]
struct SubErr(u32);
struct SuperErr(u32);
impl From<SubErr> for SuperErr { fn from(e: SubErr) -> Self { SuperErr(e.0) } }
fn main() {
    let x: Result<u32, SuperErr> = try {
        if true { do yeet SubErr(77); }
        0u32
    };
    match x {
        Err(SuperErr(v)) => println!("HOMO_YEET_CONV_OK={v}"),
        _ => panic!(),
    }
}
""",
            True,
        ),
        "homo_yeet_unannotated_rejected": (
            """#![feature(try_blocks, yeet_expr)]
fn main() {
    let _x = try {
        if true { do yeet 1u8; }
        0u32
    };
}
""",
            False,
        ),
        "hetero_bikeshed_from_conv_accepted": (
            """#![feature(try_blocks_heterogeneous)]
struct SubErr(u32);
struct SuperErr(u32);
impl From<SubErr> for SuperErr { fn from(e: SubErr) -> Self { SuperErr(e.0) } }
fn main() {
    let x = try bikeshed Result<u32, SuperErr> {
        Err::<u32, SubErr>(SubErr(107))?
    };
    match x {
        Err(SuperErr(v)) => println!("HETERO_BIKESHED_CONV_OK={v}"),
        _ => panic!(),
    }
}
""",
            True,
        ),
        "infallible_alias_never_no_blanket_from": (
            """use core::convert::Infallible;
fn f(r: Result<u64, Infallible>) {
    let _out: Result<u64, u32> = (|| Ok(r?))();
}
fn main() {
    f(Ok(1));
}
""",
            False,
        ),
        "infallible_is_never_type_identity_check": (
            """#![feature(never_type)]
use core::convert::Infallible;
trait Same<T> {}
impl<T> Same<T> for T {}
fn assert_same<A: Same<B>, B>() {}
fn main() {
    assert_same::<Infallible, !>();
}
""",
            True,
        ),
        "const_try_missing_const_trait_impl_rejected": (
            """#![feature(const_try, const_try_residual, try_blocks)]
const fn add_opt(a: Option<u32>, b: Option<u32>) -> Option<u32> {
    try { a? + b? }
}
const RES: Option<u32> = add_opt(Some(10), Some(32));
fn main() { assert_eq!(RES, Some(42)); }
""",
            True,
        ),
        "const_try_with_const_trait_impl_accepted": (
            """#![feature(const_trait_impl, const_try, const_try_residual, try_blocks)]
const fn add_opt(a: Option<u32>, b: Option<u32>) -> Option<u32> {
    try { a? + b? }
}
const RES: Option<u32> = add_opt(Some(10), Some(32));
fn main() {
    assert_eq!(RES, Some(42));
    println!("CONST_TRY_OK={}", RES.unwrap());
}
""",
            True,
        ),
        "const_yeet_rejected_non_const_from_yeet": (
            """#![feature(const_trait_impl, const_try, const_try_residual, try_blocks, yeet_expr)]
const fn yeet_opt() -> Option<u32> {
    if true { do yeet; }
    Some(1)
}
const RES: Option<u32> = yeet_opt();
fn main() { assert_eq!(RES, None); }
""",
            False,
        ),
    }

    results: dict[str, Any] = {}
    with tempfile.TemporaryDirectory(prefix="probe_scope_") as td:
        tpath = Path(td)
        for name, (src, should_run) in cases.items():
            rs = tpath / f"{name}.rs"
            bin_path = tpath / name
            rs.write_text(src, encoding="utf-8")
            comp = run_cmd(["rustc", "--edition=2024", str(rs), "-o", str(bin_path)])
            entry: dict[str, Any] = {
                "compile_rc": comp.returncode,
                "stderr_head": scrub(comp.stderr.strip(), sysroot_src, td)[:900],
            }
            if comp.returncode == 0 and should_run:
                run = run_cmd([str(bin_path)])
                entry["run_rc"] = run.returncode
                entry["stdout"] = run.stdout.strip()
            results[name] = entry
    return results


def probe3_edition_drop_order(sysroot_src: str) -> dict[str, Any]:
    drop_src = """#![feature(try_blocks, try_blocks_heterogeneous)]
use std::cell::RefCell;

thread_local! {
    static LOG: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
}

fn push(tag: &'static str) {
    LOG.with(|l| l.borrow_mut().push(tag));
}

fn take_log() -> Vec<&'static str> {
    LOG.with(|l| std::mem::take(&mut *l.borrow_mut()))
}

struct Guard(&'static str, u32);
impl Drop for Guard {
    fn drop(&mut self) {
        push(self.0);
    }
}
impl Guard {
    fn ok(tag: &'static str, v: u32) -> Result<u32, &'static str> {
        let _g = Guard(tag, v);
        Ok(v)
    }
    fn val(&self) -> u32 {
        self.1
    }
}

fn mk_scrut_ok() -> (Guard, Result<u32, &'static str>) {
    (Guard("scrut_tmp", 10), Ok(10))
}
fn mk_scrut_err() -> (Guard, Result<u32, &'static str>) {
    (Guard("scrut_tmp", 0), Err("boom"))
}
fn mk_rhs() -> (Guard, u32) {
    (Guard("rhs_tmp", 6), 6)
}

fn test_qmark_ok() -> Result<u32, &'static str> {
    let _fn_local = Guard("fn_local", 0);
    let x = mk_scrut_ok().1? + mk_rhs().1;
    push("stmt_done");
    Ok(x)
}

fn test_qmark_err() -> Result<u32, &'static str> {
    let _fn_local = Guard("fn_local", 0);
    let x = mk_scrut_err().1? + mk_rhs().1;
    push("stmt_done");
    Ok(x)
}

fn test_try_tail_ok() -> Result<u32, &'static str> {
    try {
        let _blk_local = Guard("blk_local", 0);
        let a = Guard::ok("qmark_tmp", 10)?;
        a + Guard("tail_tmp", 1).val()
    }
}

fn test_try_tail_tuple() -> Result<u32, &'static str> {
    try {
        let _blk_local = Guard("blk_local", 0);
        (Guard("tail_tuple_tmp", 0), 42u32).1
    }
}

fn test_hetero_try_tail_ok() -> Result<u32, &'static str> {
    try bikeshed Result<u32, &'static str> {
        let _blk_local = Guard("blk_local", 0);
        let a = Guard::ok("qmark_tmp", 10)?;
        a + Guard("tail_tmp", 1).val()
    }
}

fn main() {
    let _ = take_log();
    let r = test_qmark_ok();
    println!("qmark_ok res={r:?} drops={:?}", take_log());

    let r = test_qmark_err();
    println!("qmark_err res={r:?} drops={:?}", take_log());

    let r = test_try_tail_ok();
    println!("try_tail_ok res={r:?} drops={:?}", take_log());

    let r = test_try_tail_tuple();
    println!("try_tail_tuple res={r:?} drops={:?}", take_log());

    let r = test_hetero_try_tail_ok();
    println!("hetero_try_tail_ok res={r:?} drops={:?}", take_log());
}
"""

    refcell_homo_src = """#![feature(try_blocks)]
use std::cell::RefCell;
fn main() {
    let r: Result<u32, ()> = try {
        let c = RefCell::new(41u32);
        *c.borrow() + 1
    };
    assert_eq!(r, Ok(42));
}
"""

    refcell_hetero_src = """#![feature(try_blocks_heterogeneous)]
use std::cell::RefCell;
fn main() {
    let r = try bikeshed Result<u32, ()> {
        let c = RefCell::new(41u32);
        *c.borrow() + 1
    };
    assert_eq!(r, Ok(42));
}
"""

    out: dict[str, Any] = {}
    with tempfile.TemporaryDirectory(prefix="probe_drop_") as td:
        tpath = Path(td)
        for ed in ("2021", "2024"):
            rs = tpath / f"drop_{ed}.rs"
            bp = tpath / f"drop_{ed}"
            rs.write_text(drop_src, encoding="utf-8")
            c = run_cmd(["rustc", f"--edition={ed}", str(rs), "-o", str(bp)])
            entry: dict[str, Any] = {"compile_rc": c.returncode}
            if c.returncode == 0:
                r = run_cmd([str(bp)])
                entry["run_rc"] = r.returncode
                entry["lines"] = [line for line in r.stdout.strip().splitlines() if line.strip()]
            else:
                entry["compile_stderr"] = scrub(c.stderr, sysroot_src, td)[:600]

            btry = tpath / f"btry_{ed}.rs"
            btry_bin = tpath / f"btry_{ed}"
            btry.write_text(refcell_homo_src, encoding="utf-8")
            bc = run_cmd(["rustc", f"--edition={ed}", str(btry), "-o", str(btry_bin)])
            entry["try_tail_refcell_borrow_rc"] = bc.returncode
            entry["try_tail_refcell_borrow_stderr"] = scrub(bc.stderr.strip(), sysroot_src, td)[:500]
            if bc.returncode == 0:
                br = run_cmd([str(btry_bin)])
                entry["try_tail_refcell_borrow_run_rc"] = br.returncode

            htry = tpath / f"htry_{ed}.rs"
            htry_bin = tpath / f"htry_{ed}"
            htry.write_text(refcell_hetero_src, encoding="utf-8")
            hc = run_cmd(["rustc", f"--edition={ed}", str(htry), "-o", str(htry_bin)])
            entry["hetero_try_tail_refcell_borrow_rc"] = hc.returncode
            entry["hetero_try_tail_refcell_borrow_stderr"] = scrub(hc.stderr.strip(), sysroot_src, td)[:500]
            if hc.returncode == 0:
                hr = run_cmd([str(htry_bin)])
                entry["hetero_try_tail_refcell_borrow_run_rc"] = hr.returncode

            out[f"edition_{ed}"] = entry
    return out


def analyze_mir_file(path: Path) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")
    bb_count = len(re.findall(r"^\s+bb\d+:", text, flags=re.MULTILINE))
    switch_count = len(re.findall(r"\bswitchInt\(", text))
    unreachable_count = len(re.findall(r"^\s+unreachable;\s*$", text, flags=re.MULTILINE))
    # Count BOTH total substring hits (including inlined scope comments) AND live call terminators
    call_lines = [ln for ln in text.splitlines() if " = " in ln and "->" in ln]
    return {
        "file": path.name,
        "bb_count": bb_count,
        "switchInt_count": switch_count,
        "unreachable_count": unreachable_count,
        "residual_into_try_type_mentions": text.count("residual_into_try_type"),
        "residual_into_try_type_live_calls": sum(1 for ln in call_lines if "residual_into_try_type" in ln),
        "from_residual_mentions": text.count("from_residual"),
        "from_residual_live_calls": sum(1 for ln in call_lines if "from_residual" in ln),
        "branch_mentions": text.count("::branch("),
        "branch_live_calls": sum(1 for ln in call_lines if "::branch(" in ln),
    }


def extract_llvm_fn(ll_text: str, fn_name: str) -> list[str]:
    lines = ll_text.splitlines()
    out: list[str] = []
    capturing = False
    for ln in lines:
        if not capturing and ln.startswith("define ") and f"@{fn_name}(" in ln:
            capturing = True
        if capturing:
            out.append(ln)
            if ln.strip() == "}":
                break
    return out


def probe4_const_mir_and_llvm(sysroot_src: str) -> dict[str, Any]:
    lib_rs = """#![crate_type = "lib"]
#![feature(const_trait_impl, const_convert, const_try, const_try_residual, try_blocks)]

use core::convert::Infallible;
use core::num::NonZeroU64;

#[repr(C)]
pub struct CustomErr(pub u32);

const impl From<Infallible> for CustomErr {
    fn from(x: Infallible) -> Self {
        match x {}
    }
}

#[unsafe(no_mangle)]
pub const fn qmark_infallible(r: Result<u64, Infallible>) -> Result<u64, CustomErr> {
    let v = r?;
    Ok(v.wrapping_add(1))
}

#[unsafe(no_mangle)]
pub const fn qmark_infallible_same(r: Result<u64, Infallible>) -> Result<u64, Infallible> {
    let v = r?;
    Ok(v.wrapping_add(1))
}

#[unsafe(no_mangle)]
pub const fn qmark_opt_nonzero(x: Option<NonZeroU64>) -> Option<NonZeroU64> {
    let v = x?;
    NonZeroU64::new(v.get() | 1)
}

#[unsafe(no_mangle)]
pub const fn homo_try_opt_u64(x: Option<u64>, y: Option<u64>) -> Option<u64> {
    try {
        x?.wrapping_add(y?)
    }
}

pub const CONST_CHECK_INFALLIBLE: Result<u64, CustomErr> = qmark_infallible(Ok(41));
pub const CONST_CHECK_INFALLIBLE_SAME: Result<u64, Infallible> = qmark_infallible_same(Ok(41));
pub const CONST_CHECK_NONZERO: Option<NonZeroU64> = qmark_opt_nonzero(NonZeroU64::new(4));
pub const CONST_CHECK_HOMO_TRY: Option<u64> = homo_try_opt_u64(Some(19), Some(23));
"""
    fns = ("qmark_infallible", "qmark_infallible_same", "qmark_opt_nonzero", "homo_try_opt_u64")
    dump_pat = "|".join(fns)
    with tempfile.TemporaryDirectory(prefix="probe_mir_") as td:
        tpath = Path(td)
        rs = tpath / "lib.rs"
        rs.write_text(lib_rs, encoding="utf-8")
        mir_o0 = tpath / "mir_o0"
        mir_o2 = tpath / "mir_o2"
        mir_o0.mkdir()
        mir_o2.mkdir()

        c0 = run_cmd([
            "rustc",
            "--edition=2024",
            "--crate-name", "lib",
            "-C", "opt-level=0",
            "-Z", f"dump-mir={dump_pat}",
            "-Z", f"dump-mir-dir={mir_o0}",
            "-Z", "dump-mir-graphviz=no",
            str(rs),
            "--out-dir", str(tpath / "out0"),
        ])
        (tpath / "out2").mkdir()
        c2 = run_cmd([
            "rustc",
            "--edition=2024",
            "--crate-name", "lib",
            "-C", "opt-level=2",
            "--emit=llvm-ir",
            "-Z", f"dump-mir={dump_pat}",
            "-Z", f"dump-mir-dir={mir_o2}",
            "-Z", "dump-mir-graphviz=no",
            str(rs),
            "-o", str(tpath / "out2" / "lib.ll"),
        ])

        mir_summary: dict[str, Any] = {}
        for fn in fns:
            post_files = sorted(mir_o0.glob(f"lib.{fn}.*.runtime-post-cleanup.after.mir"))
            opt_files = sorted(mir_o2.glob(f"lib.{fn}.*.runtime-optimized.after.mir"))
            mir_summary[fn] = {
                "postcleanup_mir_opt0": analyze_mir_file(post_files[-1]) if post_files else None,
                "optimized_mir_opt2": analyze_mir_file(opt_files[-1]) if opt_files else None,
            }

        ll_text = (tpath / "out2" / "lib.ll").read_text(encoding="utf-8") if c2.returncode == 0 else ""
        llvm_ir = {fn: extract_llvm_fn(ll_text, fn) for fn in fns}
        return {
            "compile_o0_rc": c0.returncode,
            "compile_o0_stderr": scrub(c0.stderr, sysroot_src, td)[:500] if c0.returncode != 0 else "",
            "compile_o2_rc": c2.returncode,
            "compile_o2_stderr": scrub(c2.stderr, sysroot_src, td)[:500] if c2.returncode != 0 else "",
            "mir_postcleanup_vs_optimized": mir_summary,
            "llvm_o2_ir": llvm_ir,
        }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, help="Optional JSON output file path")
    args = parser.parse_args()

    rustc_vv = run_cmd(["rustc", "-vV"]).stdout.strip()
    sysroot = run_cmd(["rustc", "--print", "sysroot"]).stdout.strip()
    sysroot_src = f"{sysroot}/lib/rustlib/src/rust"
    miri_ver = run_cmd(["cargo", "miri", "--version"]).stdout.strip()

    report = {
        "toolchain": {
            "rustc_vV": rustc_vv,
            "miri_version": miri_ver,
        },
        "probe1_track_caller_matrix": probe1_track_caller(sysroot_src),
        "probe2_scope_inference_and_conversion_matrix": probe2_scope_and_conversion(sysroot_src),
        "probe3_edition_drop_order": probe3_edition_drop_order(sysroot_src),
        "probe4_const_try_mir_and_llvm": probe4_const_mir_and_llvm(sysroot_src),
    }

    rendered = json.dumps(report, indent=2) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
