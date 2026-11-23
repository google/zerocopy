#!/usr/bin/env python3
"""Live rustc verification probe for rustc_pattern_analysis Maranget exhaustiveness,
uninhabited types vs &Void, PrivateUninhabited, cross-crate #[non_exhaustive],
guard non-exhaustiveness, integer/usize range splitting, and unreachable_patterns.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _find_rustc() -> str:
    env_rustc = os.environ.get("RUSTC")
    if env_rustc and Path(env_rustc).is_file():
        return env_rustc
    which_rustc = shutil.which("rustc")
    if which_rustc:
        return which_rustc
    cargo_rustc = Path.home() / ".cargo" / "bin" / "rustc"
    if cargo_rustc.is_file():
        return str(cargo_rustc)
    raise FileNotFoundError("Could not locate rustc executable")


def _scrub(text: str, tmpdir: str) -> str:
    text = text.replace(tmpdir, "<tmp>")
    home = str(Path.home())
    if home:
        text = text.replace(home, "<home>")
    return text


def _run_rustc(
    rustc: str,
    src_path: Path,
    out_path: Path,
    tmpdir: str,
    *,
    edition: str = "2024",
    crate_type: str = "bin",
    extra_args: list[str] | None = None,
    cwd: Path | None = None,
) -> dict[str, Any]:
    cmd = [
        rustc,
        f"--edition={edition}",
        "--crate-type",
        crate_type,
        str(src_path),
        "-o",
        str(out_path),
    ]
    if extra_args:
        cmd.extend(extra_args)
    proc = subprocess.run(
        cmd,
        cwd=str(cwd or src_path.parent),
        capture_output=True,
        text=True,
        timeout=60,
    )
    return {
        "edition": edition,
        "crate_type": crate_type,
        "extra_args": [_scrub(a, tmpdir) for a in (extra_args or [])],
        "compile_returncode": proc.returncode,
        "compile_stdout": _scrub(proc.stdout.strip(), tmpdir),
        "compile_stderr": _scrub(proc.stderr.strip(), tmpdir),
    }


def _run_bin(bin_path: Path, tmpdir: str) -> dict[str, Any]:
    proc = subprocess.run([str(bin_path)], capture_output=True, text=True, timeout=30)
    return {
        "run_returncode": proc.returncode,
        "run_stdout": _scrub(proc.stdout.strip(), tmpdir),
        "run_stderr": _scrub(proc.stderr.strip(), tmpdir),
    }


def run_probes() -> dict[str, Any]:
    rustc = _find_rustc()
    ver_proc = subprocess.run([rustc, "--version", "--verbose"], capture_output=True, text=True, check=True)
    rustc_version = ver_proc.stdout.strip()

    results: dict[str, Any] = {
        "probe_suite": "rustc_pattern_analysis_maranget_exhaustiveness",
        "rustc_version": rustc_version,
        "groups": {},
    }

    with tempfile.TemporaryDirectory(prefix="rustc_pattern_analysis_probe_") as tmpdir:
        tmp = Path(tmpdir)

        # ------------------------------------------------------------------
        # Group A: Uninhabited types, MIR UnreachablePropagation, &Void, PrivateUninhabited
        # ------------------------------------------------------------------
        group_a: dict[str, Any] = {}

        # A1: Result<u32, Void> at -Copt-level=0 vs -Copt-level=1 with MIR dumps
        src_void_res = """pub enum Void {}

#[inline(never)]
pub fn unwrap_void_res(r: Result<u32, Void>) -> u32 {
    match r {
        Ok(x) => x,
        Err(v) => match v {},
    }
}

#[inline(never)]
pub fn unwrap_void_res_implicit(r: Result<u32, Void>) -> u32 {
    match r {
        Ok(x) => x,
    }
}

fn main() {
    let x = unwrap_void_res(Ok(77));
    let y = unwrap_void_res_implicit(Ok(99));
    println!("UNWRAP_VOID=({},{})", x, y);
}
"""
        a1_rs = tmp / "a1_void_res.rs"
        a1_rs.write_text(src_void_res, encoding="utf-8")

        for opt_label, opt_arg in [("opt0", "-Copt-level=0"), ("opt1", "-Copt-level=1")]:
            mir_dir = tmp / f"mir_{opt_label}"
            mir_dir.mkdir()
            out_bin = tmp / f"a1_{opt_label}"
            rec = _run_rustc(
                rustc,
                a1_rs,
                out_bin,
                tmpdir,
                extra_args=[
                    opt_arg,
                    "-Zdump-mir=UnreachablePropagation|MatchBranchSimplification|built",
                    f"-Zdump-mir-dir={mir_dir}",
                ],
                cwd=tmp,
            )
            if rec["compile_returncode"] == 0:
                rec.update(_run_bin(out_bin, tmpdir))
            mir_dumps: dict[str, str] = {}
            for p in sorted(mir_dir.glob("*unwrap_void_res*")):
                if any(tag in p.name for tag in ("built", "UnreachablePropagation", "MatchBranchSimplification")):
                    mir_dumps[p.name] = _scrub(p.read_text(encoding="utf-8").strip(), tmpdir)
            rec["mir_dumps"] = mir_dumps
            group_a[f"void_and_result_void_{opt_label}"] = rec

        # A2: Deref of &Result<u32, Void> (PlaceValidity::MaybeInvalid) without vs with exhaustive_patterns
        for feat_label, header in [
            ("default", ""),
            ("exhaustive_patterns", "#![feature(exhaustive_patterns)]\n"),
        ]:
            src_deref_res = f"""{header}pub enum Void {{}}
pub fn unwrap_ref_res(r: &Result<u32, Void>) -> u32 {{
    match *r {{
        Ok(x) => x,
    }}
}}
fn main() {{
    let v = Ok(55);
    println!("DEREF_RES={{}}", unwrap_ref_res(&v));
}}
"""
            rs_p = tmp / f"a2_deref_{feat_label}.rs"
            rs_p.write_text(src_deref_res, encoding="utf-8")
            out_p = tmp / f"a2_deref_{feat_label}"
            rec = _run_rustc(rustc, rs_p, out_p, tmpdir)
            if rec["compile_returncode"] == 0:
                rec.update(_run_bin(out_p, tmpdir))
            group_a[f"deref_result_void_{feat_label}"] = rec

        # A3: Never type `!` and Result<u32, !>
        src_never = """#![feature(never_type)]

#[inline(never)]
pub fn absurd(n: !) -> u32 {
    match n {}
}

#[inline(never)]
pub fn unwrap_never_res(r: Result<u32, !>) -> u32 {
    match r {
        Ok(x) => x,
        Err(n) => absurd(n),
    }
}

fn main() {
    println!("UNWRAP_NEVER={}", unwrap_never_res(Ok(88)));
}
"""
        a3_rs = tmp / "a3_never.rs"
        a3_rs.write_text(src_never, encoding="utf-8")
        a3_bin = tmp / "a3_never"
        rec_a3 = _run_rustc(rustc, a3_rs, a3_bin, tmpdir)
        if rec_a3["compile_returncode"] == 0:
            rec_a3.update(_run_bin(a3_bin, tmpdir))
        group_a["never_type_and_result_never"] = rec_a3

        # A4: &Void empty match without deref (default & exhaustive_patterns) vs with deref
        for label, header, body in [
            ("ref_void_empty_default", "", "match r {}"),
            ("ref_void_empty_exhaustive_patterns", "#![feature(exhaustive_patterns)]\n", "match r {}"),
            ("ref_void_deref_empty_default", "", "match *r {}"),
            ("ref_void_wildcard_default", "", "match r { &_ => 12 }"),
        ]:
            src_rv = f"""{header}pub enum Void {{}}
pub fn check_ref(r: &Void) -> u32 {{
    {body}
}}
fn main() {{}}
"""
            rs_p = tmp / f"a4_{label}.rs"
            rs_p.write_text(src_rv, encoding="utf-8")
            out_p = tmp / f"a4_{label}"
            group_a[label] = _run_rustc(rustc, rs_p, out_p, tmpdir)

        # A5: Constructor::PrivateUninhabited (inside vs outside defining module)
        for label, body in [
            ("private_uninhabited_inside_mod_empty_ok", "inner::inside_empty(p)"),
            ("private_uninhabited_outside_mod_empty_e0004", "match p {}"),
            (
                "private_uninhabited_outside_mod_cover_pub_tag_ok",
                "match p { inner::Priv { tag: 0..=255, .. } => 1 }",
            ),
        ]:
            src_pu = f"""mod inner {{
    pub enum Void {{}}
    pub struct Priv {{
        pub tag: u8,
        _v: Void,
    }}
    pub fn inside_empty(p: Priv) -> u32 {{
        match p {{}}
    }}
}}
pub fn outside(p: inner::Priv) -> u32 {{
    {body}
}}
fn main() {{}}
"""
            rs_p = tmp / f"a5_{label}.rs"
            rs_p.write_text(src_pu, encoding="utf-8")
            out_p = tmp / f"a5_{label}"
            group_a[label] = _run_rustc(rustc, rs_p, out_p, tmpdir)

        results["groups"]["a_uninhabited_matching_and_mir"] = group_a

        # ------------------------------------------------------------------
        # Group B: Cross-crate #[non_exhaustive] (E0004 & E0638)
        # ------------------------------------------------------------------
        group_b: dict[str, Any] = {}
        up_rs = tmp / "up.rs"
        up_rs.write_text(
            """#[non_exhaustive]
pub enum Status {
    Ok,
    Err,
}

#[non_exhaustive]
pub enum SingleNonExh {
    Only,
}

#[non_exhaustive]
pub struct Config {
    pub port: u16,
    extra: u8,
}

#[non_exhaustive]
pub struct AllPub {
    pub port: u16,
}

pub enum Ev {
    #[non_exhaustive]
    V { a: u8 },
}

pub fn make_status(ok: bool) -> Status {
    if ok { Status::Ok } else { Status::Err }
}

pub fn make_single() -> SingleNonExh {
    SingleNonExh::Only
}

pub fn make_config(port: u16) -> Config {
    Config { port, extra: 1 }
}

pub fn make_allpub(port: u16) -> AllPub {
    AllPub { port }
}

pub fn make_ev(a: u8) -> Ev {
    Ev::V { a }
}

pub fn internal_exhaustive_match(s: Status, x: SingleNonExh, c: Config, a: AllPub) -> u32 {
    let v1 = match s {
        Status::Ok => 1,
        Status::Err => 2,
    };
    let v2 = match x {
        SingleNonExh::Only => 10,
    };
    let Config { port, extra } = c;
    let AllPub { port: p2 } = a;
    v1 + v2 + u32::from(port) + u32::from(extra) + u32::from(p2)
}
""",
            encoding="utf-8",
        )
        up_rlib = tmp / "libup.rlib"
        group_b["upstream_defining_crate_without_wildcard_ok"] = _run_rustc(
            rustc, up_rs, up_rlib, tmpdir, crate_type="rlib"
        )

        dn_cases = [
            (
                "downstream_non_exhaustive_enum_without_wildcard_e0004",
                """extern crate up;
fn check(s: up::Status) -> u32 {
    match s {
        up::Status::Ok => 1,
        up::Status::Err => 2,
    }
}
fn main() {}
""",
                False,
            ),
            (
                "downstream_single_variant_non_exhaustive_without_wildcard_e0004",
                """extern crate up;
fn check(x: up::SingleNonExh) -> u32 {
    match x {
        up::SingleNonExh::Only => 1,
    }
}
fn main() {}
""",
                False,
            ),
            (
                "downstream_non_exhaustive_enum_with_wildcard_ok",
                """extern crate up;
fn check(s: up::Status) -> u32 {
    match s {
        up::Status::Ok => 1,
        up::Status::Err => 2,
        _ => 3,
    }
}
fn main() {
    let a = check(up::make_status(true));
    let b = check(up::make_status(false));
    println!("STAT=({},{})", a, b);
}
""",
                True,
            ),
            (
                "downstream_non_exhaustive_struct_without_dotdot_e0638",
                """extern crate up;
fn port_of(c: up::Config) -> u16 {
    let up::Config { port } = c;
    port
}
fn main() {}
""",
                False,
            ),
            (
                "downstream_non_exhaustive_allpub_struct_without_dotdot_e0638",
                """extern crate up;
fn port_of(a: up::AllPub) -> u16 {
    let up::AllPub { port } = a;
    port
}
fn main() {}
""",
                False,
            ),
            (
                "downstream_non_exhaustive_variant_without_dotdot_e0638",
                """extern crate up;
fn read_ev(e: up::Ev) -> u8 {
    match e {
        up::Ev::V { a } => a,
    }
}
fn main() {}
""",
                False,
            ),
            (
                "downstream_non_exhaustive_struct_with_dotdot_ok",
                """extern crate up;
fn port_of(c: up::Config) -> u16 {
    let up::Config { port, .. } = c;
    port
}
fn main() {
    let c = up::make_config(8080);
    println!("PORT={}", port_of(c));
}
""",
                True,
            ),
        ]
        for label, code, should_run in dn_cases:
            dn_rs = tmp / f"dn_{label}.rs"
            dn_rs.write_text(code, encoding="utf-8")
            dn_bin = tmp / f"dn_{label}"
            rec = _run_rustc(
                rustc,
                dn_rs,
                dn_bin,
                tmpdir,
                extra_args=["--extern", f"up={up_rlib}"],
            )
            if should_run and rec["compile_returncode"] == 0:
                rec.update(_run_bin(dn_bin, tmpdir))
            group_b[label] = rec

        results["groups"]["b_cross_crate_non_exhaustive"] = group_b

        # ------------------------------------------------------------------
        # Group C: Guards, integer ranges, usize::MAX, and unreachable_patterns
        # ------------------------------------------------------------------
        group_c: dict[str, Any] = {}

        c_cases = [
            (
                "guarded_arms_non_exhaustive_e0004",
                """fn sign(x: i32) -> i32 {
    match x {
        n if n >= 0 => 1,
        n if n < 0 => -1,
    }
}
fn main() {}
""",
                False,
            ),
            (
                "guarded_bool_non_exhaustive_e0004",
                """fn classify_bool(b: bool, flag: bool) -> u8 {
    match b {
        true if flag => 1,
        false if !flag => 0,
    }
}
fn main() {}
""",
                False,
            ),
            (
                "usize_max_range_non_exhaustive_e0004",
                """fn match_usize(x: usize) -> u8 {
    match x {
        0..=usize::MAX => 1,
    }
}
fn main() {}
""",
                False,
            ),
            (
                "integer_ranges_and_unreachable_patterns_lint",
                """fn split_u8(x: u8) -> u8 {
    match x {
        0..=127 => 1,
        128..=255 => 2,
    }
}

fn shadowed(x: u8) -> u8 {
    match x {
        0..=10 => 100,
        5..=15 => 200,
        7 => 255,
        _ => 0,
    }
}

fn guarded_does_not_shadow(x: u8, flag: bool) -> u8 {
    match x {
        0..=10 if flag => 100,
        7 => 255,
        _ => 0,
    }
}

fn main() {
    println!(
        "U8=({},{}) SHAD=({},{},{},{}) GSHAD=({},{})",
        split_u8(0),
        split_u8(200),
        shadowed(3),
        shadowed(12),
        shadowed(20),
        shadowed(7),
        guarded_does_not_shadow(7, false),
        guarded_does_not_shadow(7, true),
    );
}
""",
                True,
            ),
        ]
        for label, code, should_run in c_cases:
            c_rs = tmp / f"c_{label}.rs"
            c_rs.write_text(code, encoding="utf-8")
            c_bin = tmp / f"c_{label}"
            rec = _run_rustc(rustc, c_rs, c_bin, tmpdir)
            if should_run and rec["compile_returncode"] == 0:
                rec.update(_run_bin(c_bin, tmpdir))
            group_c[label] = rec

        results["groups"]["c_guards_ranges_and_unreachable_patterns"] = group_c

    verify_invariants(results)
    return results


def verify_invariants(payload: dict[str, Any]) -> None:
    ga = payload["groups"]["a_uninhabited_matching_and_mir"]
    assert ga["void_and_result_void_opt0"]["compile_returncode"] == 0
    assert ga["void_and_result_void_opt0"]["run_stdout"] == "UNWRAP_VOID=(77,99)"
    assert ga["void_and_result_void_opt1"]["compile_returncode"] == 0
    assert ga["void_and_result_void_opt1"]["run_stdout"] == "UNWRAP_VOID=(77,99)"
    assert any(
        "assume(" in txt and "Eq(" in txt and "discriminant(" in txt
        for txt in ga["void_and_result_void_opt1"]["mir_dumps"].values()
    )
    assert ga["deref_result_void_default"]["compile_returncode"] == 1
    assert "E0004" in ga["deref_result_void_default"]["compile_stderr"]
    assert ga["deref_result_void_exhaustive_patterns"]["compile_returncode"] == 0
    assert ga["deref_result_void_exhaustive_patterns"]["run_stdout"] == "DEREF_RES=55"
    assert ga["never_type_and_result_never"]["compile_returncode"] == 0
    assert ga["never_type_and_result_never"]["run_stdout"] == "UNWRAP_NEVER=88"
    assert ga["ref_void_empty_default"]["compile_returncode"] == 1
    assert "E0004" in ga["ref_void_empty_default"]["compile_stderr"]
    assert "references are always considered inhabited" in ga["ref_void_empty_default"]["compile_stderr"]
    assert ga["ref_void_empty_exhaustive_patterns"]["compile_returncode"] == 1
    assert "E0004" in ga["ref_void_empty_exhaustive_patterns"]["compile_stderr"]
    assert ga["ref_void_deref_empty_default"]["compile_returncode"] == 0
    assert ga["ref_void_wildcard_default"]["compile_returncode"] == 0
    assert ga["private_uninhabited_inside_mod_empty_ok"]["compile_returncode"] == 0
    assert ga["private_uninhabited_outside_mod_empty_e0004"]["compile_returncode"] == 1
    assert "E0004" in ga["private_uninhabited_outside_mod_empty_e0004"]["compile_stderr"]
    assert ga["private_uninhabited_outside_mod_cover_pub_tag_ok"]["compile_returncode"] == 0

    gb = payload["groups"]["b_cross_crate_non_exhaustive"]
    assert gb["upstream_defining_crate_without_wildcard_ok"]["compile_returncode"] == 0
    assert gb["downstream_non_exhaustive_enum_without_wildcard_e0004"]["compile_returncode"] == 1
    assert "E0004" in gb["downstream_non_exhaustive_enum_without_wildcard_e0004"]["compile_stderr"]
    assert gb["downstream_single_variant_non_exhaustive_without_wildcard_e0004"]["compile_returncode"] == 1
    assert "E0004" in gb["downstream_single_variant_non_exhaustive_without_wildcard_e0004"]["compile_stderr"]
    assert gb["downstream_non_exhaustive_enum_with_wildcard_ok"]["compile_returncode"] == 0
    assert gb["downstream_non_exhaustive_enum_with_wildcard_ok"]["run_stdout"] == "STAT=(1,2)"
    assert gb["downstream_non_exhaustive_struct_without_dotdot_e0638"]["compile_returncode"] == 1
    assert "E0638" in gb["downstream_non_exhaustive_struct_without_dotdot_e0638"]["compile_stderr"]
    assert gb["downstream_non_exhaustive_allpub_struct_without_dotdot_e0638"]["compile_returncode"] == 1
    assert "E0638" in gb["downstream_non_exhaustive_allpub_struct_without_dotdot_e0638"]["compile_stderr"]
    assert gb["downstream_non_exhaustive_variant_without_dotdot_e0638"]["compile_returncode"] == 1
    assert "E0638" in gb["downstream_non_exhaustive_variant_without_dotdot_e0638"]["compile_stderr"]
    assert gb["downstream_non_exhaustive_struct_with_dotdot_ok"]["compile_returncode"] == 0
    assert gb["downstream_non_exhaustive_struct_with_dotdot_ok"]["run_stdout"] == "PORT=8080"

    gc = payload["groups"]["c_guards_ranges_and_unreachable_patterns"]
    assert gc["guarded_arms_non_exhaustive_e0004"]["compile_returncode"] == 1
    assert "E0004" in gc["guarded_arms_non_exhaustive_e0004"]["compile_stderr"]
    assert "match arms with guards don't count towards exhaustivity" in gc["guarded_arms_non_exhaustive_e0004"]["compile_stderr"]
    assert gc["guarded_bool_non_exhaustive_e0004"]["compile_returncode"] == 1
    assert "E0004" in gc["guarded_bool_non_exhaustive_e0004"]["compile_stderr"]
    assert gc["usize_max_range_non_exhaustive_e0004"]["compile_returncode"] == 1
    assert "E0004" in gc["usize_max_range_non_exhaustive_e0004"]["compile_stderr"]
    assert "usize::MAX" in gc["usize_max_range_non_exhaustive_e0004"]["compile_stderr"]
    lint_case = gc["integer_ranges_and_unreachable_patterns_lint"]
    assert lint_case["compile_returncode"] == 0
    assert "unreachable pattern" in lint_case["compile_stderr"]
    assert "collectively making this unreachable" in lint_case["compile_stderr"]
    assert "guarded_does_not_shadow" not in lint_case["compile_stderr"]
    assert lint_case["run_stdout"] == "U8=(1,2) SHAD=(100,200,0,100) GSHAD=(255,100)"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON output path")
    args = parser.parse_args()
    payload = run_probes()
    rendered = json.dumps(payload, indent=2, ensure_ascii=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
        print(f"wrote {args.output} ({len(rendered)} bytes)")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
