#!/usr/bin/env python3
"""Live rustc + Miri differential probe for never patterns, guard patterns,
postfix match, PlaceValidity, and rustc_pattern_analysis exhaustiveness.

Runs every compiler, MIR-dump, native-execution, and Miri case via real
subprocesses with zero hardcoded results. Paths are normalized to `<tmp>` so
the output JSON is portable and contains no host-local paths.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _env_with_cargo() -> dict[str, str]:
    env = os.environ.copy()
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    path_parts = env.get("PATH", "").split(os.pathsep) if env.get("PATH") else []
    if cargo_bin not in path_parts:
        env["PATH"] = os.pathsep.join([cargo_bin] + path_parts)
    return env


def _normalize(text: str, tmp_dir: str) -> str:
    out = text.replace(tmp_dir, "<tmp>")
    # Strip any absolute home directory prefixes if present in toolchain messages.
    home = str(Path.home())
    if home:
        out = out.replace(home, "<home>")
    return out


def _extract_error_codes(stderr: str) -> list[str]:
    return sorted(set(re.findall(r"error\[(E\d{4})\]", stderr)))


def _run(
    cmd: list[str],
    *,
    env: dict[str, str],
    cwd: str | None = None,
    timeout: int = 60,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def _find_miri_binary_and_sysroot(env: dict[str, str]) -> tuple[str | None, str | None]:
    rc_sys = _run(["rustc", "--print", "sysroot"], env=env)
    if rc_sys.returncode != 0:
        return None, None
    sysroot = Path(rc_sys.stdout.strip())
    miri_bin = sysroot / "bin" / "miri"
    if not miri_bin.is_file():
        which_miri = shutil.which("miri", path=env.get("PATH"))
        if not which_miri:
            return None, None
        miri_bin = Path(which_miri)

    candidates = []
    if env.get("MIRI_SYSROOT"):
        candidates.append(Path(env["MIRI_SYSROOT"]))
    candidates.append(Path.home() / ".cache" / "miri")
    for cand in candidates:
        if (cand / "lib").is_dir():
            return str(miri_bin), str(cand)
    return str(miri_bin), None


def _compile_case(
    tmp: Path,
    name: str,
    code: str,
    *,
    env: dict[str, str],
    edition: str = "2024",
    crate_type: str = "bin",
    extra_args: list[str] | None = None,
    run_bin: bool = False,
    emit_mir: bool = False,
    dump_mir_fn: str | None = None,
    preserve_ub_mir: bool = False,
) -> dict[str, Any]:
    case_dir = tmp / name
    case_dir.mkdir(parents=True, exist_ok=True)
    src = case_dir / f"{name}.rs"
    src.write_text(code, encoding="utf-8")
    out_path = case_dir / (f"{name}.mir" if emit_mir else (f"lib{name}.rlib" if crate_type == "lib" else name))

    cmd = ["rustc", f"--edition={edition}", f"--crate-type={crate_type}", str(src), "-o", str(out_path)]
    if emit_mir:
        cmd.append("--emit=mir")
    if extra_args:
        cmd.extend(extra_args)

    res = _run(cmd, env=env, cwd=str(case_dir))
    rec: dict[str, Any] = {
        "rc": res.returncode,
        "error_codes": _extract_error_codes(res.stderr),
        "stderr": _normalize(res.stderr.strip(), str(case_dir)),
    }

    if emit_mir and res.returncode == 0 and out_path.is_file():
        mir_text = out_path.read_text(encoding="utf-8")
        rec["mir"] = mir_text.strip()
        rec["has_place_mention"] = "PlaceMention(" in mir_text
        rec["has_fake_read"] = "FakeRead(" in mir_text
        rec["has_unreachable"] = "unreachable;" in mir_text

    if dump_mir_fn and res.returncode == 0:
        dump_dir = case_dir / "mir_dumps"
        dump_dir.mkdir(exist_ok=True)
        dump_cmd = [
            "rustc",
            f"--edition={edition}",
            f"--crate-type={crate_type}",
            str(src),
            "-o",
            str(case_dir / "dump_out"),
            f"-Zdump-mir={dump_mir_fn}",
            f"-Zdump-mir-dir={dump_dir}",
            "-Zdump-mir-exclude-pass-number",
        ]
        if extra_args:
            dump_cmd.extend(extra_args)
        dres = _run(dump_cmd, env=env, cwd=str(case_dir))
        if dres.returncode == 0:
            built_files = sorted(dump_dir.glob("*.built.after.mir"))
            post_files = sorted(dump_dir.glob("*.RemovePlaceMention.after.mir"))
            cleanup_files = sorted(dump_dir.glob("*.CleanupPostBorrowck.after.mir"))
            rec["mir_built_after"] = {
                f.name: f.read_text(encoding="utf-8").strip() for f in built_files
            }
            rec["mir_cleanup_post_borrowck_after"] = {
                f.name: f.read_text(encoding="utf-8").strip() for f in cleanup_files
            }
            rec["mir_remove_place_mention_after"] = {
                f.name: f.read_text(encoding="utf-8").strip() for f in post_files
            }

    if preserve_ub_mir and res.returncode == 0:
        ub_mir_path = case_dir / f"{name}_preserve_ub.mir"
        ub_cmd = [
            "rustc",
            f"--edition={edition}",
            f"--crate-type={crate_type}",
            "-Zmir-preserve-ub",
            "-Zmir-opt-level=0",
            "--emit=mir",
            str(src),
            "-o",
            str(ub_mir_path),
        ]
        if extra_args:
            ub_cmd.extend(extra_args)
        ub_res = _run(ub_cmd, env=env, cwd=str(case_dir))
        if ub_res.returncode == 0 and ub_mir_path.is_file():
            ub_mir = ub_mir_path.read_text(encoding="utf-8").strip()
            rec["mir_preserve_ub_opt0"] = ub_mir
            rec["preserve_ub_opt0_has_place_mention"] = "PlaceMention(" in ub_mir

        ub_opt1_path = case_dir / f"{name}_preserve_ub_opt1.mir"
        ub_opt1_cmd = [
            "rustc",
            f"--edition={edition}",
            f"--crate-type={crate_type}",
            "-Zmir-preserve-ub",
            "--emit=mir",
            str(src),
            "-o",
            str(ub_opt1_path),
        ]
        if extra_args:
            ub_opt1_cmd.extend(extra_args)
        ub_opt1_res = _run(ub_opt1_cmd, env=env, cwd=str(case_dir))
        if ub_opt1_res.returncode == 0 and ub_opt1_path.is_file():
            ub_opt1_mir = ub_opt1_path.read_text(encoding="utf-8").strip()
            rec["mir_preserve_ub_opt1"] = ub_opt1_mir
            rec["preserve_ub_opt1_has_place_mention"] = "PlaceMention(" in ub_opt1_mir

    if run_bin and res.returncode == 0 and out_path.is_file():
        run_res = _run([str(out_path)], env=env, cwd=str(case_dir))
        rec["run_rc"] = run_res.returncode
        rec["run_stdout"] = run_res.stdout.strip()
        rec["run_stderr"] = run_res.stderr.strip()

    return rec


def _run_miri_case(
    tmp: Path,
    name: str,
    code: str,
    *,
    miri_bin: str,
    miri_sysroot: str,
    env: dict[str, str],
    edition: str = "2024",
) -> dict[str, Any]:
    case_dir = tmp / f"miri_{name}"
    case_dir.mkdir(parents=True, exist_ok=True)
    src = case_dir / "main.rs"
    src.write_text(code, encoding="utf-8")

    # Build a clean environment with MIRI_SYSROOT pointing to the prebuilt sysroot.
    miri_env = env.copy()
    miri_env["MIRI_SYSROOT"] = miri_sysroot
    cmd = [
        miri_bin,
        f"--edition={edition}",
        "--sysroot",
        miri_sysroot,
        str(src),
    ]
    res = _run(cmd, env=miri_env, cwd=str(case_dir), timeout=60)
    return {
        "rc": res.returncode,
        "stdout": res.stdout.strip(),
        "stderr": _normalize(res.stderr.strip(), str(case_dir)),
    }


def run_probe() -> dict[str, Any]:
    env = _env_with_cargo()
    ver = _run(["rustc", "--version", "-v"], env=env)
    if ver.returncode != 0:
        raise RuntimeError(f"rustc --version -v failed: {ver.stderr}")

    miri_bin, miri_sysroot = _find_miri_binary_and_sysroot(env)
    miri_ver_str = None
    if miri_bin:
        mver = _run([miri_bin, "--version"], env=env)
        if mver.returncode == 0:
            miri_ver_str = mver.stdout.strip()

    results: dict[str, Any] = {
        "rustc_version": ver.stdout.strip(),
        "miri_version": miri_ver_str,
        "cases": {},
        "cross_crate_cases": {},
        "miri_comparison": {},
    }

    with tempfile.TemporaryDirectory(prefix="neverpat_probe_") as td:
        tmp = Path(td)

        # Case 1: Result<u32, !> with bodiless Err(!)
        results["cases"]["np_01_never_pattern_in_result_ok_and_err_never"] = _compile_case(
            tmp,
            "np_01",
            """#![feature(never_patterns, never_type)]

fn unwrap_ok(r: Result<u32, !>) -> u32 {
    match r {
        Ok(v) => v,
        Err(!),
    }
}

fn main() {
    println!("UNWRAP={}", unwrap_ok(Ok(42)));
}
""",
            env=env,
            run_bin=True,
        )

        # Case 1b: By-value Result<u32, !> omitting Err (min_exhaustive_patterns, stable since 1.82)
        results["cases"]["np_01b_by_value_omit_err_min_exhaustive"] = _compile_case(
            tmp,
            "np_01b",
            """#![feature(never_type)]

fn unwrap_ok_min_exhaustive(r: Result<u32, !>) -> u32 {
    match r {
        Ok(v) => v,
    }
}

fn main() {
    println!("MIN_EXHAUSTIVE={}", unwrap_ok_min_exhaustive(Ok(42)));
}
""",
            env=env,
            run_bin=True,
        )

        # Case 2: &Result<u32, !> with Err(!) -- inspect MIR at built, post-borrowck, and post-cleanup
        results["cases"]["np_02_never_pattern_behind_shared_ref_requires_deref_read"] = _compile_case(
            tmp,
            "np_02",
            """#![feature(never_patterns, never_type)]

pub fn ref_to_err_never(r: &Result<u32, !>) -> u32 {
    match r {
        Ok(v) => *v,
        Err(!),
    }
}
""",
            env=env,
            crate_type="lib",
            emit_mir=True,
            dump_mir_fn="ref_to_err_never",
            preserve_ub_mir=True,
        )

        # Case 2b: &Result<u32, !> omitting Err(!) -> rejected E0004 (MaybeInvalid across Constructor::Ref)
        results["cases"]["np_02b_ref_result_omit_err_rejected"] = _compile_case(
            tmp,
            "np_02b",
            """#![feature(never_patterns, never_type)]

pub fn ref_omit_err(r: &Result<u32, !>) -> u32 {
    match r {
        Ok(v) => *v,
    }
}
""",
            env=env,
            crate_type="lib",
        )

        # Case 2c: &Result<u32, !> omitting Err under #![feature(exhaustive_patterns)] -> accepted
        results["cases"]["np_02c_ref_result_omit_err_exhaustive_patterns"] = _compile_case(
            tmp,
            "np_02c",
            """#![feature(exhaustive_patterns, never_type)]

pub fn ref_omit_err_exh(r: &Result<u32, !>) -> u32 {
    match r {
        Ok(v) => *v,
    }
}
""",
            env=env,
            crate_type="lib",
            emit_mir=True,
        )

        # Case 3: Never pattern on inhabited type rejected (NonEmptyNeverPattern)
        results["cases"]["np_03_never_pattern_on_inhabited_type_rejected"] = _compile_case(
            tmp,
            "np_03",
            """#![feature(never_patterns)]

pub fn bad_never(x: Option<u32>) -> u32 {
    match x {
        Some(!),
        None => 0,
    }
}
""",
            env=env,
            crate_type="lib",
        )

        # Case 4: Never pattern with arm body rejected (NeverPatternWithBody)
        results["cases"]["np_04_never_pattern_with_arm_body_rejected"] = _compile_case(
            tmp,
            "np_04",
            """#![feature(never_patterns, never_type)]

pub fn bad_body(r: Result<u32, !>) -> u32 {
    match r {
        Ok(v) => v,
        Err(!) => 0,
    }
}
""",
            env=env,
            crate_type="lib",
        )

        # Case 4b: Never pattern with guard rejected (NeverPatternWithGuard)
        results["cases"]["np_04b_never_pattern_with_guard_rejected"] = _compile_case(
            tmp,
            "np_04b",
            """#![feature(never_patterns, never_type)]

pub fn bad_guard(r: Result<u32, !>) -> u32 {
    match r {
        Ok(v) => v,
        Err(!) if true,
    }
}
""",
            env=env,
            crate_type="lib",
        )

        # Case 5: Raw pointer *const ! -- empty match vs ! vs _ => 99 MIR comparison
        results["cases"]["np_05_raw_ptr_empty_match_vs_never_pattern_deref"] = _compile_case(
            tmp,
            "np_05",
            """#![feature(never_patterns, never_type)]

pub fn empty_match_raw_never(p: *const !) -> () {
    unsafe { match *p {} }
}

pub fn explicit_never_pat_raw_never(p: *const !) -> u32 {
    unsafe { match *p { ! } }
}

pub fn wildcard_match_raw_never(p: *const !) -> u32 {
    unsafe { match *p { _ => 99 } }
}
""",
            env=env,
            crate_type="lib",
            emit_mir=True,
            dump_mir_fn="raw_never",
            preserve_ub_mir=True,
        )

        # Case 5b: Raw pointer *const HasNever -- NOT NoConstructors, so empty match rejected!
        results["cases"]["np_05b_hasnever_raw_ptr_empty_match_rejected"] = _compile_case(
            tmp,
            "np_05b",
            """#![feature(never_type)]

pub struct HasNever(pub u32, pub !);

pub fn empty_match_raw_hasnever(p: *const HasNever) -> () {
    unsafe { match *p {} }
}
""",
            env=env,
            crate_type="lib",
        )

        # Case 6: Postfix match chaining and temporary drop order (Edition 2024 & 2021)
        postfix_src = """#![feature(postfix_match)]
use std::cell::RefCell;

struct Guard<'a>(&'a RefCell<Vec<&'static str>>, u32);
impl Drop for Guard<'_> {
    fn drop(&mut self) {
        self.0.borrow_mut().push("drop_inner");
    }
}

fn make<'a>(log: &'a RefCell<Vec<&'static str>>) -> Guard<'a> {
    log.borrow_mut().push("make");
    Guard(log, 10)
}

fn main() {
    let log = RefCell::new(Vec::new());
    let res = make(&log).match {
        Guard(_, v) => {
            log.borrow_mut().push("arm_body");
            v + 5
        }
    };
    log.borrow_mut().push("after_match");
    println!("RES={} LOG={:?}", res, log.borrow());
}
"""
        results["cases"]["np_06_postfix_match_chaining_and_temp_drop_order"] = _compile_case(
            tmp, "np_06", postfix_src, env=env, edition="2024", run_bin=True
        )
        results["cases"]["np_06b_postfix_match_edition_2021"] = _compile_case(
            tmp, "np_06b", postfix_src, env=env, edition="2021", run_bin=True
        )
        prefix_src = postfix_src.replace("#![feature(postfix_match)]\n", "").replace(
            "make(&log).match {", "match make(&log) {"
        )
        results["cases"]["np_06c_prefix_match_edition_2024_comparison"] = _compile_case(
            tmp, "np_06c", prefix_src, env=env, edition="2024", run_bin=True
        )

        # Case 7a: Traditional arm guard does NOT contribute to exhaustiveness (E0004)
        results["cases"]["np_07a_arm_guard_opaque_to_exhaustiveness"] = _compile_case(
            tmp,
            "np_07a",
            """pub fn guarded_arm(x: Option<i32>) -> i32 {
    match x {
        Some(n) if n > 0 => n,
        None => 0,
    }
}
""",
            env=env,
            crate_type="lib",
        )

        # Case 7b: #![feature(guard_patterns)] sub-pattern guard live defect & exhaustive int ranges
        results["cases"]["np_07b_guard_patterns_live_defect_and_int_ranges"] = _compile_case(
            tmp,
            "np_07b",
            """#![feature(guard_patterns)]

fn classify_subpat_guard(x: Option<i32>) -> &'static str {
    match x {
        Some(n if n > 0) => "pos",
        Some(_) => "nonpos",
        None => "none",
    }
}

fn exhaustive_u8(b: u8) -> &'static str {
    match b {
        0..=127 | 128..=255 => "hit",
    }
}

fn main() {
    println!(
        "GUARD_POS={} GUARD_NEG={} GUARD_NONE={} RANGE_0={} RANGE_255={}",
        classify_subpat_guard(Some(5)),
        classify_subpat_guard(Some(-5)),
        classify_subpat_guard(None),
        exhaustive_u8(0),
        exhaustive_u8(255),
    );
}
""",
            env=env,
            run_bin=True,
        )

        # Case 7c: #![feature(guard_patterns)] omits E0004 AND fails E0381 when binding used
        results["cases"]["np_07c_guard_patterns_omits_e0004_and_drops_binding"] = _compile_case(
            tmp,
            "np_07c",
            """#![feature(guard_patterns)]

pub fn only_subpat_guard(x: Option<i32>) -> i32 {
    match x {
        Some(n if n > 0) => n,
        None => 0,
    }
}
""",
            env=env,
            crate_type="lib",
        )

        # Case 7d: Module privacy boundary on PrivateUninhabitedField
        results["cases"]["np_07d_private_uninhabited_field_inside_vs_outside"] = _compile_case(
            tmp,
            "np_07d_outside",
            """#![feature(never_type)]

mod inner {
    pub struct PrivEmpty {
        _priv: !,
        pub x: u8,
    }
    pub fn inside_ok(r: Result<u8, PrivEmpty>) -> u8 {
        match r {
            Ok(v) => v,
        }
    }
}

pub fn outside_err(r: Result<u8, inner::PrivEmpty>) -> u8 {
    match r {
        Ok(v) => v,
    }
}
""",
            env=env,
            crate_type="lib",
        )

        # Case 7e: Cross-crate #[non_exhaustive] empty enum
        cc_dir = tmp / "cross_crate_non_exhaustive"
        cc_dir.mkdir(parents=True, exist_ok=True)
        dep_src = cc_dir / "dep.rs"
        dep_src.write_text(
            """#[non_exhaustive]
pub enum ForeignEmpty {}

pub fn inside_defining_crate(x: ForeignEmpty) -> u32 {
    match x {}
}
""",
            encoding="utf-8",
        )
        dep_rlib = cc_dir / "libdep.rlib"
        dep_res = _run(
            ["rustc", "--edition=2024", "--crate-type=lib", "--crate-name=dep", str(dep_src), "-o", str(dep_rlib)],
            env=env,
            cwd=str(cc_dir),
        )
        client_src = cc_dir / "client.rs"
        client_src.write_text(
            """extern crate dep;

pub fn outside_defining_crate(x: dep::ForeignEmpty) -> u32 {
    match x {}
}
""",
            encoding="utf-8",
        )
        client_res = _run(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                "--extern",
                f"dep={dep_rlib}",
                str(client_src),
                "-o",
                str(cc_dir / "libclient.rlib"),
            ],
            env=env,
            cwd=str(cc_dir),
        )
        results["cross_crate_cases"]["foreign_non_exhaustive_empty_enum"] = {
            "dep_rc": dep_res.returncode,
            "dep_stderr": _normalize(dep_res.stderr.strip(), str(cc_dir)),
            "client_rc": client_res.returncode,
            "client_error_codes": _extract_error_codes(client_res.stderr),
            "client_stderr": _normalize(client_res.stderr.strip(), str(cc_dir)),
        }

        # Case 7f: Never pattern initialization check (E0381) and union read safety check (E0133)
        results["cases"]["np_07f_never_pattern_uninit_and_union_read"] = _compile_case(
            tmp,
            "np_07f",
            """#![feature(never_patterns, never_type)]

union U {
    a: !,
    b: usize,
}

pub fn uninit_check() -> u32 {
    let x: !;
    match x { ! }
}

pub fn union_read_requires_unsafe(u: U) -> ! {
    let U { a: ! } = u;
}
""",
            env=env,
            crate_type="lib",
        )

        # Miri differential cases
        if miri_bin and miri_sysroot:
            results["miri_comparison"]["wildcard_match_star_null"] = _run_miri_case(
                tmp,
                "wildcard_star_null",
                """#![feature(never_type)]
fn main() {
    let p: *const ! = core::ptr::null();
    let x: u32 = unsafe { match *p { _ => 99 } };
    println!("WILDCARD_NULL_OK={}", x);
}
""",
                miri_bin=miri_bin,
                miri_sysroot=miri_sysroot,
                env=env,
            )

            results["miri_comparison"]["empty_match_star_null"] = _run_miri_case(
                tmp,
                "empty_star_null",
                """#![feature(never_type)]
fn main() {
    let p: *const ! = core::ptr::null();
    unsafe { match *p {} }
}
""",
                miri_bin=miri_bin,
                miri_sysroot=miri_sysroot,
                env=env,
            )

            results["miri_comparison"]["explicit_bang_match_star_null"] = _run_miri_case(
                tmp,
                "bang_star_null",
                """#![feature(never_patterns, never_type)]
fn main() {
    let p: *const ! = core::ptr::null();
    let _x: u32 = unsafe { match *p { ! } };
}
""",
                miri_bin=miri_bin,
                miri_sysroot=miri_sysroot,
                env=env,
            )

            # Rogue tagged enum behind raw pointer (properly 4-byte aligned):
            # Err(_) avoids reading the `!` field vs Err(!) enters `unreachable`.
            results["miri_comparison"]["rogue_tagged_raw_ptr_err_wildcard"] = _run_miri_case(
                tmp,
                "rogue_tagged_wildcard",
                """#![feature(never_type)]
#[repr(C, u8)]
enum Tagged {
    Ok(u32) = 0,
    Err(!) = 1,
}
#[repr(C, align(4))]
struct AlignedBuf([u8; 8]);
fn main() {
    let raw = AlignedBuf([1, 0, 0, 0, 0, 0, 0, 0]);
    let p: *const Tagged = (&raw as *const AlignedBuf).cast();
    let v = unsafe {
        match *p {
            Tagged::Ok(x) => x,
            Tagged::Err(_) => 777,
        }
    };
    println!("ROGUE_ERR_WILDCARD_OK={}", v);
}
""",
                miri_bin=miri_bin,
                miri_sysroot=miri_sysroot,
                env=env,
            )

            results["miri_comparison"]["rogue_tagged_raw_ptr_err_bang"] = _run_miri_case(
                tmp,
                "rogue_tagged_bang",
                """#![feature(never_patterns, never_type)]
#[repr(C, u8)]
enum Tagged {
    Ok(u32) = 0,
    Err(!) = 1,
}
#[repr(C, align(4))]
struct AlignedBuf([u8; 8]);
fn main() {
    let raw = AlignedBuf([1, 0, 0, 0, 0, 0, 0, 0]);
    let p: *const Tagged = (&raw as *const AlignedBuf).cast();
    let v = unsafe {
        match *p {
            Tagged::Ok(x) => x,
            Tagged::Err(!),
        }
    };
    println!("UNREACHABLE={}", v);
}
""",
                miri_bin=miri_bin,
                miri_sysroot=miri_sysroot,
                env=env,
            )

            results["miri_comparison"]["rogue_tagged_raw_ptr_omit_err_exhaustive_patterns"] = _run_miri_case(
                tmp,
                "rogue_tagged_omit_exh",
                """#![feature(exhaustive_patterns, never_type)]
#[repr(C, u8)]
enum Tagged {
    Ok(u32) = 0,
    Err(!) = 1,
}
#[repr(C, align(4))]
struct AlignedBuf([u8; 8]);
fn main() {
    let raw = AlignedBuf([1, 0, 0, 0, 0, 0, 0, 0]);
    let p: *const Tagged = (&raw as *const AlignedBuf).cast();
    let v = unsafe {
        match *p {
            Tagged::Ok(x) => x,
        }
    };
    println!("UNREACHABLE={}", v);
}
""",
                miri_bin=miri_bin,
                miri_sysroot=miri_sysroot,
                env=env,
            )

            # Rogue tagged enum behind shared reference (properly 4-byte aligned):
            # Does creating `&Tagged` with tag=1 already succeed (shallow ref validity) and
            # then let `Err(_)` succeed while `Err(!)` faults UB?
            results["miri_comparison"]["rogue_tagged_shared_ref_err_wildcard"] = _run_miri_case(
                tmp,
                "rogue_ref_wildcard",
                """#![feature(never_type)]
#[repr(C, u8)]
enum Tagged {
    Ok(u32) = 0,
    Err(!) = 1,
}
#[repr(C, align(4))]
struct AlignedBuf([u8; 8]);
fn main() {
    let raw = AlignedBuf([1, 0, 0, 0, 0, 0, 0, 0]);
    let r: &Tagged = unsafe { &*(&raw as *const AlignedBuf).cast::<Tagged>() };
    let v = match r {
        Tagged::Ok(x) => *x,
        Tagged::Err(_) => 777,
    };
    println!("ROGUE_REF_WILDCARD_OK={}", v);
}
""",
                miri_bin=miri_bin,
                miri_sysroot=miri_sysroot,
                env=env,
            )

            results["miri_comparison"]["rogue_tagged_shared_ref_err_bang"] = _run_miri_case(
                tmp,
                "rogue_ref_bang",
                """#![feature(never_patterns, never_type)]
#[repr(C, u8)]
enum Tagged {
    Ok(u32) = 0,
    Err(!) = 1,
}
#[repr(C, align(4))]
struct AlignedBuf([u8; 8]);
fn main() {
    let raw = AlignedBuf([1, 0, 0, 0, 0, 0, 0, 0]);
    let r: &Tagged = unsafe { &*(&raw as *const AlignedBuf).cast::<Tagged>() };
    let v = match r {
        Tagged::Ok(x) => *x,
        Tagged::Err(!),
    };
    println!("UNREACHABLE={}", v);
}
""",
                miri_bin=miri_bin,
                miri_sysroot=miri_sysroot,
                env=env,
            )

            # Top-level wildcard on rogue &Tagged skips Rvalue::Discriminant -> succeeds!
            results["miri_comparison"]["rogue_tagged_shared_ref_top_wildcard"] = _run_miri_case(
                tmp,
                "rogue_ref_top_wildcard",
                """#![feature(never_type)]
#[repr(C, u8)]
enum Tagged {
    Ok(u32) = 0,
    Err(!) = 1,
}
#[repr(C, align(4))]
struct AlignedBuf([u8; 8]);
fn main() {
    let raw = AlignedBuf([1, 0, 0, 0, 0, 0, 0, 0]);
    let r: &Tagged = unsafe { &*(&raw as *const AlignedBuf).cast::<Tagged>() };
    let v = match r {
        _ => 888,
    };
    println!("ROGUE_TOP_WILDCARD_OK={}", v);
}
""",
                miri_bin=miri_bin,
                miri_sysroot=miri_sysroot,
                env=env,
            )

            # Product type with uninhabited field behind raw pointer / ref:
            # HasNever(x, _) does not inspect `!` field -> succeeds; HasNever(_, !) faults UB!
            results["miri_comparison"]["rogue_hasnever_raw_ptr_wildcard"] = _run_miri_case(
                tmp,
                "rogue_hasnever_raw_wild",
                """#![feature(never_type)]
#[repr(C)]
struct HasNever(u32, !);
fn main() {
    let x: u32 = 42;
    let p: *const HasNever = (&x as *const u32).cast();
    let v = unsafe {
        match *p {
            HasNever(n, _) => n,
        }
    };
    println!("HASNEVER_RAW_WILD_OK={}", v);
}
""",
                miri_bin=miri_bin,
                miri_sysroot=miri_sysroot,
                env=env,
            )

            results["miri_comparison"]["rogue_hasnever_raw_ptr_bang"] = _run_miri_case(
                tmp,
                "rogue_hasnever_raw_bang",
                """#![feature(never_patterns, never_type)]
#[repr(C)]
struct HasNever(u32, !);
fn main() {
    let x: u32 = 42;
    let p: *const HasNever = (&x as *const u32).cast();
    let _v: u32 = unsafe {
        match *p {
            HasNever(_, !),
        }
    };
}
""",
                miri_bin=miri_bin,
                miri_sysroot=miri_sysroot,
                env=env,
            )

            results["miri_comparison"]["rogue_hasnever_shared_ref_wildcard"] = _run_miri_case(
                tmp,
                "rogue_hasnever_ref_wild",
                """#![feature(never_type)]
#[repr(C)]
struct HasNever(u32, !);
fn main() {
    let x: u32 = 42;
    let r: &HasNever = unsafe { &*(&x as *const u32).cast::<HasNever>() };
    let v = match r {
        HasNever(n, _) => *n,
    };
    println!("HASNEVER_REF_WILD_OK={}", v);
}
""",
                miri_bin=miri_bin,
                miri_sysroot=miri_sysroot,
                env=env,
            )

            results["miri_comparison"]["rogue_hasnever_shared_ref_bang"] = _run_miri_case(
                tmp,
                "rogue_hasnever_ref_bang",
                """#![feature(never_patterns, never_type)]
#[repr(C)]
struct HasNever(u32, !);
fn main() {
    let x: u32 = 42;
    let r: &HasNever = unsafe { &*(&x as *const u32).cast::<HasNever>() };
    let _v: u32 = match r {
        HasNever(_, !),
    };
}
""",
                miri_bin=miri_bin,
                miri_sysroot=miri_sysroot,
                env=env,
            )

    return results


def main() -> int:
    out_path = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    data = run_probe()
    rendered = json.dumps(data, indent=2, ensure_ascii=True) + "\n"
    if out_path is not None:
        out_path.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
