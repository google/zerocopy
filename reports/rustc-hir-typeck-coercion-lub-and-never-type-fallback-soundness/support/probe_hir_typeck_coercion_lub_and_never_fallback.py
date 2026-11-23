#!/usr/bin/env python3
"""Live differential probe for rustc_hir_typeck Coerce/CoerceMany LUB
coercions, never-type (!) fallback across Editions 2021 and 2024,
never_type_fallback_flowing_into_unsafe graph reachability, place-read
gating (`expr_guaranteed_to_constitute_read_for_never`), and native/Miri
runtime semantics.

Every compilation, MIR/LLVM-IR dump, native execution, and Miri check is
executed live against the active rustc/Miri toolchain with zero hardcoded
results.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any


def _resolve_tool(name: str, explicit: str | None) -> str:
    if explicit:
        return explicit
    found = shutil.which(name)
    if found:
        return found
    cargo_bin = Path.home() / ".cargo" / "bin" / name
    if cargo_bin.exists():
        return str(cargo_bin)
    return name


def _run(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )


def _sanitize(text: str, tmp_dir: Path) -> str:
    home = str(Path.home())
    user = Path.home().name
    out = text.replace(str(tmp_dir), "<TMP>")
    if home:
        out = out.replace(home, "<HOME>")
    if user:
        out = out.replace(f"/home/{user}", "<HOME>").replace(user, "<USER>")
    out = re.sub(r"/rustc(?:-dev)?/[0-9a-f]{7,40}/", "<RUSTC_SRC>/", out)
    out = re.sub(r"/x20/[^\s\"']+", "<X20_PATH>", out)
    return out


def _compile_only(
    rustc: str,
    tmp_dir: Path,
    name: str,
    code: str,
    *,
    edition: str,
    crate_type: str = "lib",
    extra_args: list[str] | None = None,
) -> dict[str, Any]:
    src = tmp_dir / f"{name}.rs"
    out = tmp_dir / f"{name}.out"
    src.write_text(code, encoding="utf-8")
    cmd = [
        rustc,
        f"--edition={edition}",
        f"--crate-type={crate_type}",
        str(src),
        "-o",
        str(out),
    ]
    if extra_args:
        cmd.extend(extra_args)
    res = _run(cmd, cwd=tmp_dir)
    return {
        "edition": edition,
        "rc": res.returncode,
        "stdout": _sanitize(res.stdout, tmp_dir).strip(),
        "stderr": _sanitize(res.stderr, tmp_dir).strip(),
    }


def _emit_mir_and_ir(
    rustc: str,
    tmp_dir: Path,
    name: str,
    code: str,
    *,
    edition: str,
    opt_level: str = "0",
) -> dict[str, Any]:
    src = tmp_dir / f"{name}.rs"
    mir_path = tmp_dir / f"{name}.mir"
    ll_path = tmp_dir / f"{name}.ll"
    src.write_text(code, encoding="utf-8")

    mir_res = _run(
        [
            rustc,
            f"--edition={edition}",
            "--crate-type=lib",
            f"-Copt-level={opt_level}",
            "--emit=mir",
            str(src),
            "-o",
            str(mir_path),
        ],
        cwd=tmp_dir,
    )
    ll_res = _run(
        [
            rustc,
            f"--edition={edition}",
            "--crate-type=lib",
            f"-Copt-level={opt_level}",
            "--emit=llvm-ir",
            str(src),
            "-o",
            str(ll_path),
        ],
        cwd=tmp_dir,
    )
    mir_text = _sanitize(mir_path.read_text(encoding="utf-8"), tmp_dir) if mir_path.exists() else ""
    ll_text = _sanitize(ll_path.read_text(encoding="utf-8"), tmp_dir) if ll_path.exists() else ""
    return {
        "mir_rc": mir_res.returncode,
        "mir_stderr": _sanitize(mir_res.stderr, tmp_dir).strip(),
        "mir_text": mir_text,
        "ll_rc": ll_res.returncode,
        "ll_text": ll_text,
    }


def _extract_mir_fn(mir_text: str, fn_name: str) -> str:
    m = re.search(
        rf"fn {re.escape(fn_name)}\([^\n]*\n(?:[ \t].*\n|\n)*^\}}",
        mir_text,
        flags=re.M,
    )
    return m.group(0).strip() if m else ""


def _compile_and_run_native(
    rustc: str,
    tmp_dir: Path,
    name: str,
    code: str,
    *,
    edition: str,
    opt_level: str = "2",
    arg_sets: list[list[str]] | None = None,
) -> dict[str, Any]:
    src = tmp_dir / f"{name}.rs"
    exe = tmp_dir / f"{name}_bin"
    src.write_text(code, encoding="utf-8")
    comp = _run(
        [rustc, f"--edition={edition}", f"-Copt-level={opt_level}", str(src), "-o", str(exe)],
        cwd=tmp_dir,
    )
    result: dict[str, Any] = {
        "edition": edition,
        "opt_level": opt_level,
        "compile_rc": comp.returncode,
        "compile_stderr": _sanitize(comp.stderr, tmp_dir).strip(),
        "runs": {},
    }
    if comp.returncode != 0:
        return result

    for args in (arg_sets if arg_sets is not None else [[]]):
        key = "_".join(args) if args else "default"
        run = _run([str(exe), *args], cwd=tmp_dir)
        result["runs"][key] = {
            "args": args,
            "rc": run.returncode,
            "stdout": _sanitize(run.stdout, tmp_dir).strip(),
            "stderr": _sanitize(run.stderr, tmp_dir).strip(),
        }
    return result


def _prepare_miri_env(cargo: str, tmp_dir: Path, explicit_sysroot: str | None) -> dict[str, str]:
    env = dict(os.environ)
    cargo_bin = str(Path(cargo).parent)
    if cargo_bin and cargo_bin not in env.get("PATH", ""):
        env["PATH"] = f"{cargo_bin}:{env.get('PATH', '')}"
    if explicit_sysroot:
        env["MIRI_SYSROOT"] = explicit_sysroot
        return env
    if env.get("MIRI_SYSROOT"):
        return env
    probe_dir = tmp_dir / "_miri_setup_probe"
    (probe_dir / "src").mkdir(parents=True, exist_ok=True)
    (probe_dir / "Cargo.toml").write_text(
        '[package]\nname = "miri_setup_probe"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    (probe_dir / "src" / "main.rs").write_text("fn main() {}\n", encoding="utf-8")
    test = _run([cargo, "miri", "setup"], cwd=probe_dir, env=env, timeout=240)
    if test.returncode == 0:
        return env

    home_cargo = Path.home() / ".cargo"
    if (home_cargo / "registry").is_dir():
        alt_home = tmp_dir / "_alt_cargo_home"
        alt_home.mkdir(parents=True, exist_ok=True)
        os.symlink(home_cargo / "registry", alt_home / "registry")
        if (home_cargo / "bin").is_dir():
            os.symlink(home_cargo / "bin", alt_home / "bin")
        (alt_home / "config.toml").write_text("[net]\noffline = true\n", encoding="utf-8")
        sysroot = tmp_dir / "_miri_sysroot"
        sysroot.mkdir(parents=True, exist_ok=True)
        env["CARGO_HOME"] = str(alt_home)
        env["MIRI_SYSROOT"] = str(sysroot)
        setup = _run([cargo, "miri", "setup"], cwd=probe_dir, env=env, timeout=300)
        if setup.returncode != 0:
            raise RuntimeError(f"cargo miri setup failed:\n{setup.stderr}")
        return env
    raise RuntimeError(f"cargo miri setup failed:\n{test.stderr}")


def _run_miri(
    cargo: str,
    tmp_dir: Path,
    name: str,
    code: str,
    *,
    edition: str,
    miri_env: dict[str, str],
    miri_flags: str | None = None,
    args: list[str] | None = None,
) -> dict[str, Any]:
    proj = tmp_dir / f"miri_{name}"
    (proj / "src").mkdir(parents=True, exist_ok=True)
    (proj / "Cargo.toml").write_text(
        f'[package]\nname = "miri_{name}"\nversion = "0.1.0"\nedition = "{edition}"\n',
        encoding="utf-8",
    )
    (proj / "src" / "main.rs").write_text(code, encoding="utf-8")
    env = dict(miri_env)
    if miri_flags:
        existing = env.get("MIRIFLAGS", "").strip()
        env["MIRIFLAGS"] = f"{existing} {miri_flags}".strip()
    cmd = [cargo, "miri", "run", "-q"]
    if args:
        cmd.append("--")
        cmd.extend(args)
    res = _run(cmd, cwd=proj, env=env)
    return {
        "edition": edition,
        "miriflags": miri_flags or "<default Stacked Borrows>",
        "args": args or [],
        "rc": res.returncode,
        "stdout": _sanitize(res.stdout, proj).strip(),
        "stderr": _sanitize(res.stderr, proj).strip(),
    }


# ---------------------------------------------------------------------------
# Part A: Never-Type Fallback & never_type_fallback_flowing_into_unsafe
# ---------------------------------------------------------------------------

PROG_POLY_AND_ZEROED_UNFEATURED = r"""
trait Poly {
    fn tag() -> &'static str;
}

impl Poly for () {
    fn tag() -> &'static str { "unit" }
}

impl Poly for ! {
    fn tag() -> &'static str { "never" }
}

fn make<T: Poly>() -> (&'static str, Option<T>) {
    (T::tag(), None)
}

#[inline(never)]
pub fn probe_fallback() -> &'static str {
    let (t, o) = make();
    if false {
        let _x = if true { return "early"; } else { o.unwrap() };
    }
    t
}

#[inline(never)]
#[allow(never_type_fallback_flowing_into_unsafe)]
pub fn probe_never_zeroed_live(do_ub: bool) -> &'static str {
    if do_ub {
        let _x = if false { return "early"; } else { unsafe { core::mem::zeroed() } };
    }
    "ok"
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "safe".to_string());
    let tag = probe_fallback();
    let res = probe_never_zeroed_live(mode == "ub");
    println!("TAG={tag} RES={res}");
}
"""

PROG_POLY_AND_ZEROED_FEATURE_NEVER = (
    "#![feature(never_type)]\n" + PROG_POLY_AND_ZEROED_UNFEATURED.rstrip() + "\n"
)

# Stable-syntax probe (no `!` in user surface): triggers fallback purely via
# diverging `if`/`loop` + `Default::default()` vs `core::mem::zeroed()`.
PROG_DEFAULT_DENY_UNSAFE_DIRECT = r"""
pub fn trigger_direct() {
    let _x = if false { return; } else { unsafe { core::mem::zeroed() } };
}
"""

PROG_DEFAULT_DENY_UNSAFE_GRAPH_HOP = r"""
pub fn trigger_indirect_hop(cond: bool) {
    let a = if cond { return; } else { Default::default() };
    let b = if !cond { a } else { unsafe { core::mem::zeroed() } };
    let _ = b;
}

pub fn trigger_two_hop_coercion(cond: bool) {
    let v0 = if cond { return; } else { loop {} };
    let v1 = if !cond { v0 } else { Default::default() };
    let v2 = if cond { v1 } else { unsafe { core::mem::zeroed() } };
    let _ = v2;
}
"""

PROG_DEPENDENCY_ON_UNIT = r"""
trait OnlyUnit {
    fn tag(&self) -> u32;
}
impl OnlyUnit for () {
    fn tag(&self) -> u32 { 7 }
}

fn take<T: OnlyUnit>(_x: T) -> u32 { 7 }

pub fn needs_unit(cond: bool) -> u32 {
    let x = if cond { return 1; } else { Default::default() };
    take(x)
}
"""

PROG_NEVER_ALL_DIVERGING_AND_PLACE_READ = r"""
#![feature(never_type)]

#[inline(never)]
pub fn all_diverge_if(c: bool) -> ! {
    let x = if c { return loop {} } else { panic!("arm2") };
    x
}

#[inline(never)]
#[allow(unsafe_op_in_unsafe_fn)]
pub unsafe fn place_deref_wildcard(p: *const !) -> u32 {
    let _ = *p;
    42
}

#[inline(never)]
#[allow(unsafe_op_in_unsafe_fn)]
pub unsafe fn place_match_wildcard(p: *const !) -> u32 {
    match *p {
        _ => 43,
    }
}

#[inline(never)]
#[allow(unsafe_op_in_unsafe_fn)]
pub unsafe fn place_block_deref(p: *const !) -> u32 {
    let _ = { *p };
    44
}

#[inline(never)]
#[allow(unsafe_op_in_unsafe_fn)]
pub unsafe fn place_deref_read_unit(p: *const !) -> u32 {
    let _x: () = *p;
    45
}

fn main() {
    let dummy: u8 = 0;
    let p: *const ! = (&dummy as *const u8).cast();
    let mode = std::env::args().nth(1).unwrap_or_else(|| "wild".to_string());
    let v = match mode.as_str() {
        "wild" => unsafe { place_deref_wildcard(p) },
        "match_wild" => unsafe { place_match_wildcard(p) },
        "block_deref" => unsafe { place_block_deref(p) },
        "read" => unsafe { place_deref_read_unit(p) },
        other => panic!("unknown mode {other}"),
    };
    println!("MODE={mode} VAL={v}");
}
"""


# ---------------------------------------------------------------------------
# Part B: CoerceMany LUB Coercions & Order Sensitivity
# ---------------------------------------------------------------------------

PROG_COERCE_MANY_LUB = r"""
#[inline(never)]
fn safe_fn(x: u32) -> u32 { x + 10 }

#[inline(never)]
unsafe fn unsafe_fn(x: u32) -> u32 { x + 20 }

#[inline(never)]
pub fn lub_ref_mut_shared(cond: bool, a: &mut u32, b: &u32) -> u32 {
    let r = if cond { a } else { b };
    *r
}

#[inline(never)]
pub fn lub_ref_shared_mut(cond: bool, a: &u32, b: &mut u32) -> u32 {
    let r = if cond { a } else { b };
    *r
}

#[inline(never)]
pub fn lub_array_slices() -> [&'static [u8]; 2] {
    [&[1u8, 2], &[3, 4, 5]]
}

#[inline(never)]
pub fn lub_array_mut_and_shared_unsize<'a>(a: &'a mut [u8; 2], b: &'a [u8; 3]) -> [&'a [u8]; 2] {
    [a, b]
}

#[inline(never)]
pub fn lub_if_mut_unsize<'a>(cond: bool, a: &'a mut [u8; 2], b: &'a [u8; 3]) -> &'a [u8] {
    if cond { a } else { b }
}

#[inline(never)]
pub fn lub_two_closures(cond: bool, v: u32) -> u32 {
    let f = if cond { |x: u32| x + 1 } else { |x: u32| x + 2 };
    f(v)
}

#[inline(never)]
pub fn lub_same_closure_stays_unreified(cond: bool, v: u32) -> u32 {
    let c = |x: u32| x + 3;
    let f = if cond { c } else { c };
    f(v)
}

#[inline(never)]
pub fn lub_safe_unsafe_fndef(cond: bool, v: u32) -> u32 {
    let f = if cond { safe_fn } else { unsafe_fn };
    unsafe { f(v) }
}

#[inline(never)]
pub fn lub_safe_unsafe_fnptr(cond: bool, v: u32) -> u32 {
    let p_safe: fn(u32) -> u32 = safe_fn;
    let p_unsafe: unsafe fn(u32) -> u32 = unsafe_fn;
    let f = if cond { p_safe } else { p_unsafe };
    unsafe { f(v) }
}

#[inline(never)]
pub fn lub_raw_mut_to_const(cond: bool, a: *mut u32, b: *const u32) -> u32 {
    let p = if cond { a } else { b };
    unsafe { *p }
}

#[inline(never)]
pub fn lub_block_shared_first(cond: bool, mut x: u32, y: u32) -> u32 {
    let r = 'blk: {
        if cond {
            break 'blk &y;
        }
        &mut x
    };
    *r
}

#[inline(never)]
pub fn lub_loop_shared_first(cond: bool, mut x: u32, y: u32) -> u32 {
    let s = loop {
        if cond {
            break &y;
        }
        break &mut x;
    };
    *s
}

fn main() {
    let mut a = 5u32;
    let b = 7u32;
    let r1 = lub_ref_mut_shared(true, &mut a, &b);
    let r2 = lub_ref_shared_mut(false, &b, &mut a);
    let slices = lub_array_slices();
    let mut marr = [10u8, 20];
    let mut marr2 = [10u8, 20];
    let sarr = [30u8, 40, 50];
    let mslices = lub_array_mut_and_shared_unsize(&mut marr, &sarr);
    let if_unsize = lub_if_mut_unsize(true, &mut marr2, &sarr);
    let clos = lub_two_closures(true, 11);
    let same_clos = lub_same_closure_stays_unreified(false, 11);
    let fn_def = lub_safe_unsafe_fndef(false, 10);
    let fn_ptr = lub_safe_unsafe_fnptr(true, 10);
    let raw = lub_raw_mut_to_const(true, &mut a as *mut u32, &b as *const u32);
    let blk = lub_block_shared_first(false, 5, 9);
    let lp = lub_loop_shared_first(false, 5, 9);
    assert_eq!(r1, 5);
    assert_eq!(r2, 5);
    assert_eq!((slices[0].len(), slices[1].len()), (2, 3));
    assert_eq!((mslices[0].len(), mslices[1].len()), (2, 3));
    assert_eq!(if_unsize.len(), 2);
    assert_eq!(clos, 12);
    assert_eq!(same_clos, 14);
    assert_eq!(fn_def, 30);
    assert_eq!(fn_ptr, 20);
    assert_eq!(raw, 5);
    assert_eq!(blk, 5);
    assert_eq!(lp, 5);
    println!(
        "REF=({r1},{r2}) SLICES=({},{}) MSLICES=({},{}) CLOS=({clos},{same_clos}) FN=({fn_def},{fn_ptr}) RAW={raw} BLK={blk} LP={lp}",
        slices[0].len(),
        slices[1].len(),
        mslices[0].len(),
        mslices[1].len(),
    );
}
"""

PROG_ORDER_SENSITIVE_CALL_FAIL = r"""
fn pick<T>(a: T, _b: T) -> T { a }

pub fn bad_order() {
    let mut x = 7i32;
    let y = 7i32;
    let _ = pick(&mut x, &y);
}
"""

PROG_ORDER_SENSITIVE_CALL_OK = r"""
fn pick<T>(a: T, _b: T) -> T { a }

pub fn good_order() -> i32 {
    let mut x = 7i32;
    let y = 7i32;
    *pick(&y, &mut x)
}
"""

PROG_LOOP_LET_MUT_FIRST_FAIL = r"""
pub fn loop_mut_first_in_let(cond: bool, mut x: u32, y: u32) -> u32 {
    let r = loop {
        if cond {
            break &mut x;
        }
        break &y;
    };
    *r
}
"""

PROG_BLOCK_LET_MUT_FIRST_FAIL = r"""
pub fn block_mut_first_in_let(cond: bool, mut x: u32, y: u32) -> u32 {
    let r = 'blk: {
        if cond {
            break 'blk &mut x;
        }
        &y
    };
    *r
}
"""

PROG_LOOP_AND_BLOCK_STMT_NO_EXPECTATION_OK = r"""
pub fn stmt_no_let_pin(cond: bool, mut x: u32, y: u32) {
    let a = &mut x;
    let b = &y;
    loop {
        if cond { break a; }
        break b;
    };
    'blk: {
        if cond { break 'blk a; }
        b
    };
}
"""

PROG_CLOS_UPVAR_REJECTED = r"""
pub fn capturing_lub(cond: bool, k: u32) -> u32 {
    let f = if cond { |x: u32| x + k } else { |x: u32| x + 1 };
    f(10)
}
"""

PROG_ARRAY_LUB_NO_HINT_FAIL = r"""
pub fn no_hint_if(cond: bool) {
    let _s = if cond { &[1u8, 2] } else { &[3, 4, 5] };
}

pub fn no_hint_arr() {
    let _a = [&[1u8, 2], &[3, 4, 5]];
}
"""


def run_all(rustc: str, cargo: str, miri_sysroot: str | None) -> dict[str, Any]:
    rustc_ver = _run([rustc, "--version", "--verbose"])
    miri_ver = _run([cargo, "miri", "--version"])
    if rustc_ver.returncode != 0:
        raise RuntimeError(f"rustc --version failed: {rustc_ver.stderr}")
    if miri_ver.returncode != 0:
        raise RuntimeError(f"cargo miri --version failed: {miri_ver.stderr}")

    results: dict[str, Any] = {
        "observed_at": _dt.date.today().isoformat(),
        "rustc_version": rustc_ver.stdout.strip(),
        "miri_version": miri_ver.stdout.strip(),
        "part_a_never_fallback": {},
        "part_b_coerce_many_lub": {},
    }

    with tempfile.TemporaryDirectory(prefix="probe_coerce_lub_") as td:
        tmp = Path(td)
        miri_env = _prepare_miri_env(cargo, tmp, miri_sysroot)

        # Part A across both editions
        for edition in ("2021", "2024"):
            ed_key = f"edition_{edition}"
            unfeatured_compile = _compile_only(
                rustc,
                tmp,
                f"a_unfeatured_{edition}",
                PROG_POLY_AND_ZEROED_UNFEATURED,
                edition=edition,
                crate_type="bin",
            )
            native_opt2 = _compile_and_run_native(
                rustc,
                tmp,
                f"a_poly_zeroed_{edition}",
                PROG_POLY_AND_ZEROED_FEATURE_NEVER,
                edition=edition,
                opt_level="2",
                arg_sets=[["safe"], ["ub"]],
            )
            native_opt0 = _compile_and_run_native(
                rustc,
                tmp,
                f"a_poly_zeroed_o0_{edition}",
                PROG_POLY_AND_ZEROED_FEATURE_NEVER,
                edition=edition,
                opt_level="0",
                arg_sets=[["safe"], ["ub"]],
            )
            mir_ir_o0 = _emit_mir_and_ir(
                rustc,
                tmp,
                f"a_mir_{edition}",
                PROG_POLY_AND_ZEROED_FEATURE_NEVER,
                edition=edition,
                opt_level="0",
            )
            mir_excerpts = {
                fn: _extract_mir_fn(mir_ir_o0["mir_text"], fn)
                for fn in ("probe_fallback", "probe_never_zeroed_live")
            }
            miri_runs = {}
            for mode in ("safe", "ub"):
                miri_runs[f"stacked_borrows__{mode}"] = _run_miri(
                    cargo,
                    tmp,
                    f"a_sb_{edition}_{mode}",
                    PROG_POLY_AND_ZEROED_FEATURE_NEVER,
                    edition=edition,
                    miri_env=miri_env,
                    args=[mode],
                )
                miri_runs[f"tree_borrows__{mode}"] = _run_miri(
                    cargo,
                    tmp,
                    f"a_tb_{edition}_{mode}",
                    PROG_POLY_AND_ZEROED_FEATURE_NEVER,
                    edition=edition,
                    miri_env=miri_env,
                    miri_flags="-Zmiri-tree-borrows",
                    args=[mode],
                )

            deny_direct = _compile_only(
                rustc, tmp, f"a_deny_direct_{edition}", PROG_DEFAULT_DENY_UNSAFE_DIRECT, edition=edition
            )
            deny_graph = _compile_only(
                rustc, tmp, f"a_deny_graph_{edition}", PROG_DEFAULT_DENY_UNSAFE_GRAPH_HOP, edition=edition
            )
            dep_unit = _compile_only(
                rustc, tmp, f"a_dep_unit_{edition}", PROG_DEPENDENCY_ON_UNIT, edition=edition
            )
            place_read_mir = _emit_mir_and_ir(
                rustc,
                tmp,
                f"a_place_read_{edition}",
                PROG_NEVER_ALL_DIVERGING_AND_PLACE_READ,
                edition=edition,
                opt_level="0",
            )
            place_read_native = _compile_and_run_native(
                rustc,
                tmp,
                f"a_place_read_bin_{edition}",
                PROG_NEVER_ALL_DIVERGING_AND_PLACE_READ,
                edition=edition,
                opt_level="0",
                arg_sets=[["wild"], ["match_wild"], ["block_deref"], ["read"]],
            )
            place_read_miri = {
                f"stacked_borrows__{m}": _run_miri(
                    cargo,
                    tmp,
                    f"a_pr_sb_{m}_{edition}",
                    PROG_NEVER_ALL_DIVERGING_AND_PLACE_READ,
                    edition=edition,
                    miri_env=miri_env,
                    args=[m],
                )
                for m in ("wild", "match_wild", "block_deref", "read")
            }

            results["part_a_never_fallback"][ed_key] = {
                "edition": edition,
                "unfeatured_never_compile": unfeatured_compile,
                "feature_never_native_opt2": native_opt2,
                "feature_never_native_opt0": native_opt0,
                "feature_never_mir_excerpts": mir_excerpts,
                "feature_never_miri_runs": miri_runs,
                "default_deny_unsafe_direct": deny_direct,
                "default_deny_unsafe_graph_hop": deny_graph,
                "dependency_on_unit_lint": dep_unit,
                "all_diverging_and_place_read_mir": {
                    "all_diverge_if": _extract_mir_fn(place_read_mir["mir_text"], "all_diverge_if"),
                    "place_deref_wildcard": _extract_mir_fn(
                        place_read_mir["mir_text"], "place_deref_wildcard"
                    ),
                    "place_match_wildcard": _extract_mir_fn(
                        place_read_mir["mir_text"], "place_match_wildcard"
                    ),
                    "place_block_deref": _extract_mir_fn(
                        place_read_mir["mir_text"], "place_block_deref"
                    ),
                    "place_deref_read_unit": _extract_mir_fn(
                        place_read_mir["mir_text"], "place_deref_read_unit"
                    ),
                },
                "place_read_native_opt0": place_read_native,
                "place_read_miri": place_read_miri,
            }

        # Part B: CoerceMany LUB across both editions
        for edition in ("2021", "2024"):
            ed_key = f"edition_{edition}"
            native_opt2 = _compile_and_run_native(
                rustc,
                tmp,
                f"b_lub_{edition}",
                PROG_COERCE_MANY_LUB,
                edition=edition,
                opt_level="2",
            )
            mir_ir_o0 = _emit_mir_and_ir(
                rustc,
                tmp,
                f"b_lub_mir_{edition}",
                PROG_COERCE_MANY_LUB,
                edition=edition,
                opt_level="0",
            )
            lub_fns = [
                "lub_ref_mut_shared",
                "lub_ref_shared_mut",
                "lub_array_slices",
                "lub_array_mut_and_shared_unsize",
                "lub_if_mut_unsize",
                "lub_two_closures",
                "lub_same_closure_stays_unreified",
                "lub_safe_unsafe_fndef",
                "lub_safe_unsafe_fnptr",
                "lub_raw_mut_to_const",
                "lub_block_shared_first",
                "lub_loop_shared_first",
            ]
            mir_excerpts = {fn: _extract_mir_fn(mir_ir_o0["mir_text"], fn) for fn in lub_fns}
            miri_runs = {
                "stacked_borrows": _run_miri(
                    cargo, tmp, f"b_sb_{edition}", PROG_COERCE_MANY_LUB, edition=edition, miri_env=miri_env
                ),
                "tree_borrows": _run_miri(
                    cargo,
                    tmp,
                    f"b_tb_{edition}",
                    PROG_COERCE_MANY_LUB,
                    edition=edition,
                    miri_env=miri_env,
                    miri_flags="-Zmiri-tree-borrows",
                ),
            }
            order_fail = _compile_only(
                rustc, tmp, f"b_order_fail_{edition}", PROG_ORDER_SENSITIVE_CALL_FAIL, edition=edition
            )
            order_ok = _compile_only(
                rustc, tmp, f"b_order_ok_{edition}", PROG_ORDER_SENSITIVE_CALL_OK, edition=edition
            )
            loop_let_fail = _compile_only(
                rustc, tmp, f"b_loop_let_fail_{edition}", PROG_LOOP_LET_MUT_FIRST_FAIL, edition=edition
            )
            block_let_fail = _compile_only(
                rustc, tmp, f"b_block_let_fail_{edition}", PROG_BLOCK_LET_MUT_FIRST_FAIL, edition=edition
            )
            stmt_no_exp_ok = _compile_only(
                rustc,
                tmp,
                f"b_stmt_no_exp_ok_{edition}",
                PROG_LOOP_AND_BLOCK_STMT_NO_EXPECTATION_OK,
                edition=edition,
            )
            clos_upvar_err = _compile_only(
                rustc, tmp, f"b_clos_upvar_{edition}", PROG_CLOS_UPVAR_REJECTED, edition=edition
            )
            arr_no_hint_err = _compile_only(
                rustc, tmp, f"b_arr_no_hint_{edition}", PROG_ARRAY_LUB_NO_HINT_FAIL, edition=edition
            )

            results["part_b_coerce_many_lub"][ed_key] = {
                "edition": edition,
                "native_opt2": native_opt2,
                "mir_excerpts": mir_excerpts,
                "miri_runs": miri_runs,
                "call_arg_order_fail": order_fail,
                "call_arg_order_ok": order_ok,
                "loop_let_mut_first_fail": loop_let_fail,
                "block_let_mut_first_fail": block_let_fail,
                "loop_and_block_stmt_no_expectation_ok": stmt_no_exp_ok,
                "capturing_closure_lub_rejected": clos_upvar_err,
                "array_lub_without_slice_hint_rejected": arr_no_hint_err,
            }

    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rustc", default=_resolve_tool("rustc", None))
    parser.add_argument("--cargo", default=_resolve_tool("cargo", None))
    parser.add_argument("--miri-sysroot", default=os.environ.get("MIRI_SYSROOT"))
    parser.add_argument("--out", default="-", help="Output JSON path or '-' for stdout")
    args = parser.parse_args()

    data = run_all(args.rustc, args.cargo, args.miri_sysroot)
    payload = json.dumps(data, indent=2, ensure_ascii=True) + "\n"
    if args.out == "-":
        print(payload, end="")
    else:
        Path(args.out).write_text(payload, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
