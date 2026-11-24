#!/usr/bin/env python3
"""Empirical rustc probe for Edition 2021 vs 2024 RPIT lifetime capturing,
RFC 3617 `use<...>` precise capturing, and `dyn Trait` default lifetime bounds.

Executes all rustc compilations and compiled binaries inside an isolated
`tempfile.TemporaryDirectory`, scrubs host/temporary paths from captured
diagnostics, validates every expected outcome, and writes structured JSON.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _env_with_cargo() -> dict[str, str]:
    env = os.environ.copy()
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    path = env.get("PATH", "")
    if cargo_bin not in path.split(os.pathsep):
        env["PATH"] = f"{cargo_bin}{os.pathsep}{path}" if path else cargo_bin
    env.setdefault("CARGO_TERM_COLOR", "never")
    return env


def _scrub(text: str, tmpdir: str) -> str:
    s = text.replace(tmpdir, "<tmp>")
    home = str(Path.home())
    if home:
        s = s.replace(home, "<home>")
        home_parent = str(Path(home).parent)
        if home_parent and home_parent != "/":
            s = re.sub(re.escape(home_parent) + r"/[^/\s:\"]+", "<home>", s)
    s = re.sub(r"<home>/\.rustup/toolchains/[^/\s:\"]+", "<toolchain>", s)
    s = re.sub(r"/tmp/rustc_rpit_dyn_probe_[^/\s:\"]+", "<tmp>", s)
    return s


def _run_rustc(
    src: str,
    tmpdir: Path,
    name: str,
    *,
    edition: str = "2024",
    crate_type: str = "bin",
    extra_args: list[str] | None = None,
    run_binary: bool = False,
) -> dict[str, Any]:
    rs_path = tmpdir / f"{name}.rs"
    out_path = tmpdir / f"{name}.out"
    rs_path.write_text(src, encoding="utf-8")
    cmd = [
        "rustc",
        f"--edition={edition}",
        "--crate-type",
        crate_type,
        "--color=never",
        "-o",
        str(out_path),
        str(rs_path),
    ]
    if extra_args:
        cmd.extend(extra_args)
    proc = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        env=_env_with_cargo(),
        check=False,
    )
    res: dict[str, Any] = {
        "edition": edition,
        "crate_type": crate_type,
        "extra_args": list(extra_args or []),
        "compile_returncode": proc.returncode,
        "compile_stdout": _scrub(proc.stdout.strip(), str(tmpdir)),
        "compile_stderr": _scrub(proc.stderr.strip(), str(tmpdir)),
    }
    if run_binary and proc.returncode == 0:
        run_proc = subprocess.run(
            [str(out_path)],
            capture_output=True,
            text=True,
            env=_env_with_cargo(),
            check=False,
        )
        res["run_returncode"] = run_proc.returncode
        res["run_stdout"] = _scrub(run_proc.stdout.strip(), str(tmpdir))
        res["run_stderr"] = _scrub(run_proc.stderr.strip(), str(tmpdir))
    return res


def probe_part_a_rpit_and_use(tmpdir: Path) -> dict[str, Any]:
    out: dict[str, Any] = {}

    capture_check_prog = """fn capture_check(x: &u32) -> impl Sized{bound} {{
    let _ = x;
    42u32
}}

fn main() {{
    let val = {{
        let local = 10u32;
        capture_check(&local)
    }};
    let _ = val;
    println!("{tag}=42");
}}
"""

    a1 = _run_rustc(
        capture_check_prog.format(bound="", tag="RPIT_OK"),
        tmpdir,
        "a1_ed21_unannotated",
        edition="2021",
        run_binary=True,
    )
    assert a1["compile_returncode"] == 0 and a1["run_returncode"] == 0
    assert a1["run_stdout"] == "RPIT_OK=42"
    out["ed21_unannotated_rpit_does_not_capture_unused_ref"] = a1

    a2 = _run_rustc(
        capture_check_prog.format(bound="", tag="RPIT_FAIL"),
        tmpdir,
        "a2_ed24_unannotated",
        edition="2024",
    )
    assert a2["compile_returncode"] == 1 and "E0597" in a2["compile_stderr"]
    assert "Rust 2024" in a2["compile_stderr"] and "use<>" in a2["compile_stderr"]
    out["ed24_unannotated_rpit_captures_all_in_scope_lifetimes_rejected"] = a2

    a3 = _run_rustc(
        capture_check_prog.format(bound=" + use<>", tag="ED24_USE_EMPTY"),
        tmpdir,
        "a3_ed24_use_empty",
        edition="2024",
        run_binary=True,
    )
    assert a3["compile_returncode"] == 0 and a3["run_returncode"] == 0
    assert a3["run_stdout"] == "ED24_USE_EMPTY=42"
    out["ed24_rpit_use_empty_opts_out_of_lifetime_capture"] = a3

    pick_exclude_b = """fn pick<'a, 'b, T>(a: &'a u32, _b: &'b u32, _t: T) -> impl Sized + use<'a, T> {
    *a
}

fn main() {
    let long_a = 77u32;
    let r = {
        let short_b = 11u32;
        pick(&long_a, &short_b, 0u8)
    };
    let _ = r;
    println!("USE_A_T_EXCLUDES_B=77");
}
"""
    a4 = _run_rustc(pick_exclude_b, tmpdir, "a4_use_a_t_excl_b", edition="2024", run_binary=True)
    assert a4["compile_returncode"] == 0 and a4["run_returncode"] == 0
    assert a4["run_stdout"] == "USE_A_T_EXCLUDES_B=77"
    out["ed24_rpit_use_a_t_excludes_b_ok"] = a4

    pick_capture_a = """fn pick<'a, 'b, T>(a: &'a u32, _b: &'b u32, _t: T) -> impl Sized + use<'a, T> {
    *a
}

fn main() {
    let short_b = 11u32;
    let r = {
        let short_a = 77u32;
        pick(&short_a, &short_b, 0u8)
    };
    let _ = r;
}
"""
    a5 = _run_rustc(pick_capture_a, tmpdir, "a5_use_a_t_cap_a", edition="2024")
    assert a5["compile_returncode"] == 1 and "E0597" in a5["compile_stderr"]
    out["ed24_rpit_use_a_t_still_captures_a_rejected"] = a5

    pick_capture_via_t = """fn pick<'a, 'b, T>(a: &'a u32, _b: &'b u32, _t: T) -> impl Sized + use<'a, T> {
    *a
}

fn main() {
    let long_a = 77u32;
    let long_b = 11u32;
    let r = {
        let short_c = 99u32;
        pick(&long_a, &long_b, &short_c)
    };
    let _ = r;
}
"""
    a6 = _run_rustc(pick_capture_via_t, tmpdir, "a6_use_a_t_cap_via_t", edition="2024")
    assert a6["compile_returncode"] == 1 and "E0597" in a6["compile_stderr"]
    out["ed24_rpit_use_a_t_indirectly_captures_t_lifetime_rejected"] = a6

    omit_t_src = """pub fn bad<'a, T>(_a: &'a u32, _t: T) -> impl Sized + use<'a> {
    1u32
}
"""
    a7 = _run_rustc(omit_t_src, tmpdir, "a7_omit_t", edition="2024", crate_type="lib")
    assert a7["compile_returncode"] == 1 and "must mention all type parameters" in a7["compile_stderr"]
    out["ed24_rpit_use_omitting_in_scope_type_param_rejected"] = a7

    order_src = """pub fn bad<'a, T>(_a: &'a u32, _t: T) -> impl Sized + use<T, 'a> {
    1u32
}
"""
    a8 = _run_rustc(order_src, tmpdir, "a8_bad_order", edition="2024", crate_type="lib")
    assert a8["compile_returncode"] == 1 and "must be listed before non-lifetime parameters" in a8["compile_stderr"]
    out["ed24_rpit_use_lifetime_after_type_param_rejected"] = a8

    bound_omit_src = """pub fn bad<'a>(x: &'a u32) -> impl core::fmt::Debug + 'a + use<> {
    x
}
"""
    a9 = _run_rustc(bound_omit_src, tmpdir, "a9_bound_omit", edition="2024", crate_type="lib")
    assert a9["compile_returncode"] == 1 and "not mentioned in `use<...>`" in a9["compile_stderr"]
    out["ed24_rpit_use_omitting_bound_lifetime_rejected"] = a9

    apit_src = """pub fn bad(_x: impl Sized + use<>) {}
"""
    a10 = _run_rustc(apit_src, tmpdir, "a10_apit_use", edition="2024", crate_type="lib")
    assert a10["compile_returncode"] == 1 and "not allowed in argument-position" in a10["compile_stderr"]
    out["ed24_rpit_use_on_apit_rejected"] = a10

    elided_use_src = """fn capture_elided(x: &u32) -> impl Sized + use<'_> {
    *x
}

fn main() {
    let val = 99u32;
    let tok = capture_elided(&val);
    let _ = tok;
    println!("USE_ELIDED_UNDERSCORE=99");
}
"""
    a11 = _run_rustc(elided_use_src, tmpdir, "a11_use_elided", edition="2024", run_binary=True)
    assert a11["compile_returncode"] == 0 and a11["run_returncode"] == 0
    assert a11["run_stdout"] == "USE_ELIDED_UNDERSCORE=99"
    out["ed24_rpit_use_elided_underscore_ok"] = a11

    rpitit_ed21_src = """trait Maker {
    fn make(&self, x: &u32) -> impl Sized;
}
struct S;
impl Maker for S {
    fn make(&self, _x: &u32) -> impl Sized {
        42u32
    }
}
fn main() {
    let s = S;
    let val = {
        let local = 10u32;
        s.make(&local)
    };
    let _ = val;
}
"""
    a12 = _run_rustc(rpitit_ed21_src, tmpdir, "a12_ed21_rpitit", edition="2021")
    assert a12["compile_returncode"] == 1 and "E0597" in a12["compile_stderr"]
    out["ed21_rpitit_captures_all_in_scope_by_default_rejected"] = a12

    a13 = _run_rustc(
        capture_check_prog.format(bound=" + use<'_>", tag="ED21_USE_OPTIN"),
        tmpdir,
        "a13_ed21_use_optin",
        edition="2021",
    )
    assert a13["compile_returncode"] == 1 and "E0597" in a13["compile_stderr"]
    out["ed21_rpit_use_optin_captures_ref_rejected"] = a13

    callee_uncap_src = """pub fn bad<'a>(x: &'a u32) -> impl core::fmt::Debug + use<> {
    x
}
"""
    a14 = _run_rustc(callee_uncap_src, tmpdir, "a14_callee_uncaptured", edition="2024", crate_type="lib")
    assert a14["compile_returncode"] == 1 and ("E0700" in a14["compile_stderr"] or "captures lifetime" in a14["compile_stderr"])
    out["ed24_rpit_callee_returning_uncaptured_lifetime_rejected"] = a14

    return out


def probe_part_b_dyn_default_lifetime(tmpdir: Path) -> dict[str, Any]:
    out: dict[str, Any] = {}

    b1_src = """use core::fmt::Debug;
pub fn box_dyn<'a>(r: &'a u32) -> Box<dyn Debug> {
    Box::new(r)
}
"""
    b1 = _run_rustc(b1_src, tmpdir, "b1_box_dyn_static", edition="2024", crate_type="lib")
    assert b1["compile_returncode"] == 1 and "'static" in b1["compile_stderr"]
    out["box_dyn_defaults_to_static_rejected_with_ref_a"] = b1

    b2_src = """use core::fmt::Debug;
fn box_dyn<'a>(r: &'a u32) -> Box<dyn Debug + 'a> {
    Box::new(r)
}
fn main() {
    let x = 1u32;
    let b = box_dyn(&x);
    let _ = format!("{:?}", b);
    println!("BOX_DYN_A=1");
}
"""
    b2 = _run_rustc(b2_src, tmpdir, "b2_box_dyn_a", edition="2024", run_binary=True)
    assert b2["compile_returncode"] == 0 and b2["run_returncode"] == 0
    assert b2["run_stdout"] == "BOX_DYN_A=1"
    out["box_dyn_explicit_plus_a_ok"] = b2

    b3_src = """use core::fmt::Debug;
fn box_dyn(r: &u32) -> Box<dyn Debug + '_> {
    Box::new(r)
}
fn main() {
    let x = 4u32;
    let b = box_dyn(&x);
    let _ = format!("{:?}", b);
    println!("BOX_DYN_UNDERSCORE=4");
}
"""
    b3 = _run_rustc(b3_src, tmpdir, "b3_box_dyn_underscore", edition="2024", run_binary=True)
    assert b3["compile_returncode"] == 0 and b3["run_returncode"] == 0
    assert b3["run_stdout"] == "BOX_DYN_UNDERSCORE=4"
    out["box_dyn_underscore_in_return_uses_ordinary_elision_ok"] = b3

    b4_src = """use core::fmt::Debug;
fn ref_dyn<'a>(d: &'a (dyn Debug + 'a)) -> &'a dyn Debug {
    d
}
fn main() {
    let x = 2u32;
    let r = ref_dyn(&x);
    let _ = format!("{:?}", r);
    println!("REF_DYN_A=2");
}
"""
    b4 = _run_rustc(b4_src, tmpdir, "b4_ref_a_dyn", edition="2024", run_binary=True)
    assert b4["compile_returncode"] == 0 and b4["run_returncode"] == 0
    assert b4["run_stdout"] == "REF_DYN_A=2"
    out["ref_a_dyn_defaults_to_a_ok"] = b4

    b5_src = """use core::fmt::Debug;
pub fn coerce<'a>(b: &'a Box<dyn Debug + 'a>) -> &'a Box<dyn Debug> {
    b
}
"""
    b5 = _run_rustc(b5_src, tmpdir, "b5_ref_a_box_dyn", edition="2024", crate_type="lib")
    assert b5["compile_returncode"] == 1 and "'static" in b5["compile_stderr"]
    out["ref_a_box_dyn_inner_box_overrides_outer_ref_a_with_static_rejected"] = b5

    b6_src = """use core::fmt::Debug;
fn coerce<'a>(b: &'a Box<dyn Debug + 'a>) -> &'a Box<dyn Debug + 'a> {
    b
}
fn main() {
    let x = 5u32;
    let boxed: Box<dyn Debug + '_> = Box::new(&x);
    let r = coerce(&boxed);
    let _ = format!("{:?}", r);
    println!("REF_BOX_DYN_EXPLICIT_A=5");
}
"""
    b6 = _run_rustc(b6_src, tmpdir, "b6_ref_a_box_dyn_a", edition="2024", run_binary=True)
    assert b6["compile_returncode"] == 0 and b6["run_returncode"] == 0
    assert b6["run_stdout"] == "REF_BOX_DYN_EXPLICIT_A=5"
    out["ref_a_box_dyn_explicit_a_ok"] = b6

    b7_src = """use core::fmt::Debug;
struct RefWrap<'a, T: ?Sized + 'a>(&'a T);
fn wrap<'a>(r: &'a (dyn Debug + 'a)) -> RefWrap<'a, dyn Debug> {
    RefWrap(r)
}
fn main() {
    let x = 3u32;
    let w = wrap(&x);
    let _ = format!("{:?}", w.0);
    println!("STRUCT_DYN_A=3");
}
"""
    b7 = _run_rustc(b7_src, tmpdir, "b7_struct_ref_dyn", edition="2024", run_binary=True)
    assert b7["compile_returncode"] == 0 and b7["run_returncode"] == 0
    assert b7["run_stdout"] == "STRUCT_DYN_A=3"
    out["struct_ref_a_dyn_defaults_to_a_ok"] = b7

    b8_src = """use core::fmt::Debug;
pub struct TwoBounds<'a, 'b, T: ?Sized + 'a + 'b>(&'a T, &'b u32);
pub fn bad<'a, 'b>(_x: TwoBounds<'a, 'b, dyn Debug>) {}
"""
    b8 = _run_rustc(b8_src, tmpdir, "b8_two_bounds_e0228", edition="2024", crate_type="lib")
    assert b8["compile_returncode"] == 1 and "E0228" in b8["compile_stderr"]
    out["struct_two_bounds_ambiguous_dyn_rejected_e0228"] = b8

    b9_late_src = """trait BoundTrait<'a>: 'a {
    fn val(&self) -> u32;
}
struct Wrap<'a>(&'a u32);
impl<'a> BoundTrait<'a> for Wrap<'a> {
    fn val(&self) -> u32 { *self.0 }
}
pub fn mk<'a>(r: &'a u32) -> Box<dyn BoundTrait<'a>> {
    Box::new(Wrap(r))
}
"""
    b9_late = _run_rustc(b9_late_src, tmpdir, "b9_trait_late_bound", edition="2024", crate_type="lib")
    assert b9_late["compile_returncode"] == 1 and "'static" in b9_late["compile_stderr"]
    out["trait_with_late_bound_lifetime_box_dyn_falls_back_to_static_rejected"] = b9_late

    b9_early_src = """trait BoundTrait<'a>: 'a {
    fn val(&self) -> u32;
}
struct Wrap<'a>(&'a u32);
impl<'a> BoundTrait<'a> for Wrap<'a> {
    fn val(&self) -> u32 { *self.0 }
}
fn mk<'a: 'a>(r: &'a u32) -> Box<dyn BoundTrait<'a>> {
    Box::new(Wrap(r))
}
fn main() {
    let x = 6u32;
    let b = mk(&x);
    println!("TRAIT_EARLY_BOUND_DYN_A={}", b.val());
}
"""
    b9_early = _run_rustc(b9_early_src, tmpdir, "b9_trait_early_bound", edition="2024", run_binary=True)
    assert b9_early["compile_returncode"] == 0 and b9_early["run_returncode"] == 0
    assert b9_early["run_stdout"] == "TRAIT_EARLY_BOUND_DYN_A=6"
    out["trait_with_early_bound_lifetime_box_dyn_derives_a_ok"] = b9_early

    b10_src = """use core::fmt::Debug;
fn main() {
    let out = {
        let local = 7u32;
        let b: Box<dyn Debug> = Box::new(&local);
        format!("{:?}", b)
    };
    println!("IN_BODY_BOX_DYN={}", out);
}
"""
    b10 = _run_rustc(b10_src, tmpdir, "b10_in_body_box_dyn", edition="2024", run_binary=True)
    assert b10["compile_returncode"] == 0 and b10["run_returncode"] == 0
    assert b10["run_stdout"] == "IN_BODY_BOX_DYN=7"
    out["in_body_box_dyn_infers_non_static_lifetime_ok"] = b10

    b11_src = """use core::fmt::Debug;
fn nested_ref<'a, 'b>(r: &'a &'b (dyn Debug + 'b)) -> &'a &'b dyn Debug {
    r
}
fn main() {
    let x = 8u32;
    let d: &dyn Debug = &x;
    let rr = nested_ref(&d);
    let _ = format!("{:?}", rr);
    println!("NESTED_REF_DYN_B=8");
}
"""
    b11 = _run_rustc(b11_src, tmpdir, "b11_nested_ref_dyn", edition="2024", run_binary=True)
    assert b11["compile_returncode"] == 0 and b11["run_returncode"] == 0
    assert b11["run_stdout"] == "NESTED_REF_DYN_B=8"
    out["nested_ref_a_ref_b_dyn_defaults_to_inner_b_ok"] = b11

    b12_src = """use core::fmt::Debug;
pub struct RefWrap<'b, T: ?Sized + 'b>(&'b T);
pub fn ref_of_wrap<'a, 'b>(w: &'a RefWrap<'b, dyn Debug + 'b>) -> &'a RefWrap<'b, dyn Debug> {
    w
}
"""
    b12 = _run_rustc(b12_src, tmpdir, "b12_ref_wrap_shadow", edition="2024", crate_type="lib")
    assert b12["compile_returncode"] == 0
    out["ref_a_of_refwrap_b_dyn_shadows_outer_a_with_b_ok"] = b12

    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Optional output path for JSON results (defaults to stdout).",
    )
    args = parser.parse_args()

    env = _env_with_cargo()
    rustc_ver = subprocess.run(
        ["rustc", "--version", "--verbose"],
        capture_output=True,
        text=True,
        env=env,
        check=True,
    ).stdout.strip()

    with tempfile.TemporaryDirectory(prefix="rustc_rpit_dyn_probe_") as tmp:
        tmpdir = Path(tmp)
        results: dict[str, Any] = {
            "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "rustc_version": rustc_ver,
            "experiments": {
                "a_edition2021_vs_2024_rpit_and_use_precise_capturing": probe_part_a_rpit_and_use(tmpdir),
                "b_dyn_trait_default_lifetime_elision": probe_part_b_dyn_default_lifetime(tmpdir),
            },
        }

    rendered = json.dumps(results, indent=2, ensure_ascii=True) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
        print(f"Wrote verified probe results to {args.out}")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
