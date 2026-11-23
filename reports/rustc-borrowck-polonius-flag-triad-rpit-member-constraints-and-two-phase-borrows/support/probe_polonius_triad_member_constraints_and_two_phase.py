#!/usr/bin/env python3
"""Differential rustc and Miri probe for:
  - Polonius CLI triad (default / -Zpolonius=off / -Zpolonius / -Zpolonius=next / -Zpolonius=legacy)
  - 3-way behavioral separation (Problem Case #3 vs flow_sensitive_invariance)
  - Edition 2021 vs 2024 RPIT capture and member_constraints lattice resolution
  - TwoPhaseBorrow reservation vs activation and Tree Borrows Reserved permissions
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
from typing import Any


CASES: dict[str, dict[str, Any]] = {
    "a1_polonius_problem_case_3_hashmap_get": {
        "family": "A_polonius_triad",
        "edition": "2024",
        "source": """use std::collections::HashMap;

pub fn get_or_insert<'a>(map: &'a mut HashMap<u32, String>, key: u32) -> &'a str {
    if let Some(v) = map.get(&key) {
        return v;
    }
    map.insert(key, String::from("default"));
    map.get(&key).unwrap()
}
""",
    },
    "a2_polonius_hashmap_get_mut_return": {
        "family": "A_polonius_triad",
        "edition": "2024",
        "source": """use std::collections::HashMap;

pub fn get_mut_or_insert<'a>(map: &'a mut HashMap<u32, String>, key: u32) -> &'a mut str {
    if let Some(v) = map.get_mut(&key) {
        return v;
    }
    map.insert(key, String::from("default"));
    map.get_mut(&key).unwrap()
}
""",
    },
    "a3_polonius_3way_separator_flow_sensitive_invariance": {
        "family": "A_polonius_triad",
        "edition": "2024",
        "source": """use std::cell::Cell;

pub struct Invariant<'l>(Cell<&'l ()>);

fn create_invariant<'l>() -> Invariant<'l> {
    Invariant(Cell::new(&()))
}

pub fn flow_sensitive_invariance<'a, 'b>(choice: bool) -> Result<Invariant<'a>, Invariant<'b>> {
    let returned_value = create_invariant();
    if choice { Ok(returned_value) } else { Err(returned_value) }
}
""",
    },
    "a4_polonius_flow_sensitive_covariant_control": {
        "family": "A_polonius_triad",
        "edition": "2024",
        "source": """pub struct Covariant<'l>(&'l ());

fn create_covariant<'l>() -> Covariant<'l> {
    Covariant(&())
}

pub fn flow_sensitive_covariant<'a, 'b>(choice: bool) -> Result<Covariant<'a>, Covariant<'b>> {
    let returned_value = create_covariant();
    if choice { Ok(returned_value) } else { Err(returned_value) }
}
""",
    },
    "a5_polonius_invariant_backward_time_travel_reject": {
        "family": "A_polonius_triad",
        "edition": "2024",
        "source": """pub fn invariant_time_travel_must_reject() -> i32 {
    let mut a = 0i32;
    let mut b = 1i32;
    let mut p = &mut a;
    let q = &mut p;
    *q = &mut b;
    b = 3;
    *p
}
""",
    },
    "b1_ed2024_rpit_default_captures_all_lifetimes_err": {
        "family": "B_rpit_member_constraints",
        "edition": "2024",
        "source": """fn rpit_default<'a, 'b>(x: &'a i32, _y: &'b i32) -> impl core::fmt::Debug {
    x
}

pub fn caller() {
    let a = 1;
    let mut b = 2;
    let r = rpit_default(&a, &b);
    b = 3;
    let _ = (r, b);
}
""",
    },
    "b2_ed2021_rpit_without_capture_err": {
        "family": "B_rpit_member_constraints",
        "edition": "2021",
        "source": """fn rpit_default<'a, 'b>(x: &'a i32, _y: &'b i32) -> impl core::fmt::Debug {
    x
}

pub fn caller() {
    let a = 1;
    let mut b = 2;
    let r = rpit_default(&a, &b);
    b = 3;
    let _ = (r, b);
}
""",
    },
    "b3_ed2024_rpit_use_precise_captures_ok": {
        "family": "B_rpit_member_constraints",
        "edition": "2024",
        "source": """fn rpit_precise<'a, 'b>(x: &'a i32, _y: &'b i32) -> impl core::fmt::Debug + use<'a> {
    x
}

pub fn caller() {
    let a = 1;
    let mut b = 2;
    let r = rpit_precise(&a, &b);
    b = 3;
    let _ = (r, b);
}
""",
    },
    "b4_opaque_member_constraint_incomparable_choices_err": {
        "family": "B_rpit_member_constraints",
        "edition": "2024",
        "source": """pub fn member_incomparable<'a, 'b>(
    x: &'a str,
    y: &'b str,
    cond: bool,
) -> impl core::fmt::Display + use<'a, 'b> {
    if cond { x } else { y }
}
""",
    },
    "b5_opaque_member_constraint_ordered_choices_ok": {
        "family": "B_rpit_member_constraints",
        "edition": "2024",
        "source": """pub fn member_ordered<'a, 'b>(
    x: &'a str,
    y: &'b str,
    cond: bool,
) -> impl core::fmt::Display + use<'a, 'b>
where
    'a: 'b,
{
    if cond { x } else { y }
}
""",
    },
    "b6_opaque_member_constraint_unique_upper_bound_ok": {
        "family": "B_rpit_member_constraints",
        "edition": "2024",
        "source": """use core::cell::Cell;

pub fn member_with_cell<'a, 'b>(
    x: Cell<&'a str>,
    _y: Cell<&'b str>,
) -> impl Sized + use<'a, 'b> {
    x
}
""",
    },
    "b7_opaque_member_constraint_static_promoted_ok": {
        "family": "B_rpit_member_constraints",
        "edition": "2024",
        "source": """pub fn member_static<'a, 'b>(x: &'static str) -> impl core::fmt::Display + use<'a, 'b> {
    x
}
""",
    },
    "b8_opaque_member_constraint_diamond_min_ok": {
        "family": "B_rpit_member_constraints",
        "edition": "2024",
        "source": """pub fn member_diamond<'a, 'b, 'c>(
    x: &'a str,
    y: &'b str,
    cond: bool,
) -> impl core::fmt::Display + use<'a, 'b, 'c>
where
    'a: 'c,
    'b: 'c,
{
    if cond { x } else { y }
}

pub fn call_diamond_with_locals(cond: bool) -> usize {
    let s1 = String::from("alpha");
    let s2 = String::from("beta");
    let out = member_diamond::<'_, '_, '_>(&s1, &s2, cond);
    out.to_string().len()
}
""",
    },
    "c1_two_phase_shared_read_before_activation_ok": {
        "family": "C_two_phase_borrows",
        "edition": "2024",
        "source": """pub fn two_phase_shared_read() -> usize {
    let mut v = vec![10usize, 20, 30];
    v.push(v.len());
    v.len()
}
""",
    },
    "c2_two_phase_conflicting_write_before_activation_err": {
        "family": "C_two_phase_borrows",
        "edition": "2024",
        "source": """pub fn two_phase_conflicting_write() {
    let mut v = vec![10usize, 20, 30];
    v.push({
        v.clear();
        42
    });
}
""",
    },
    "c3_two_phase_nested_mut_reservation_conflict_err": {
        "family": "C_two_phase_borrows",
        "edition": "2024",
        "source": """pub fn two_phase_nested_push() {
    let mut v = vec![10usize, 20, 30];
    v.push({
        v.push(99);
        42
    });
}
""",
    },
    "c4_non_two_phase_explicit_mut_borrow_shared_read_err": {
        "family": "C_two_phase_borrows",
        "edition": "2024",
        "source": """pub fn explicit_mut_borrow_read_conflict() -> usize {
    let mut v = vec![10usize, 20, 30];
    let r = &mut v;
    let len = v.len();
    r.push(len);
    v.len()
}
""",
    },
    "c5_two_phase_prior_shared_borrow_ends_before_activation_ok": {
        "family": "C_two_phase_borrows",
        "edition": "2024",
        "source": """pub fn two_phase_prior_shared_ends_ok() -> usize {
    let mut v = vec![10usize, 20, 30];
    let r = &v[0];
    v.push(*r);
    v.len()
}
""",
    },
    "c6_two_phase_prior_shared_borrow_live_at_activation_err": {
        "family": "C_two_phase_borrows",
        "edition": "2024",
        "source": """pub fn two_phase_prior_shared_live_err() -> usize {
    let mut v = vec![10usize, 20, 30];
    let r = &v[0];
    v.push(*r);
    *r
}
""",
    },
}

MODES: list[tuple[str, list[str]]] = [
    ("nightly_default_no_flag", []),
    ("z_polonius_off", ["-Zpolonius=off"]),
    ("z_polonius_bare", ["-Zpolonius"]),
    ("z_polonius_next", ["-Zpolonius=next"]),
    ("z_polonius_legacy", ["-Zpolonius=legacy"]),
]

MIRI_CASES: dict[str, str] = {
    "tb_two_phase_vec_push_len": """fn main() {
    let mut v = vec![10usize, 20, 30];
    v.push(v.len());
    println!("len={} last={}", v.len(), v[3]);
}
""",
    "tb_two_phase_prior_shared_read": """fn main() {
    let mut v = vec![10usize, 20, 30];
    let r = &v[0];
    v.push(*r);
    println!("len={} last={}", v.len(), v[3]);
}
""",
    "tb_protected_mut_foreign_read_ub": """unsafe fn protected_conflict(x: &mut i32, raw: *const i32) {
    let _v = unsafe { *raw };
    *x = 99;
}

fn main() {
    let mut x = 10;
    let raw = &raw const x;
    unsafe { protected_conflict(&mut x, raw); }
}
""",
}


def scrub_text(text: str, tmp_dir: str) -> str:
    home = os.path.expanduser("~")
    text = text.replace(tmp_dir, "<tmp>")
    text = re.sub(r"/[^ \n\t:]+/\.rustup/toolchains/[^ \n\t:]+", "<toolchain>", text)
    if home and home != "/":
        text = text.replace(home, "<home>")
    text = re.sub(r"/tmp/[A-Za-z0-9_.-]+", "<tmp>", text)
    text = re.sub(r"/home/[A-Za-z0-9_.-]+", "<home>", text)
    text = re.sub(r"/usr/local/google/home/[A-Za-z0-9_.-]+", "<home>", text)
    text = re.sub(r"/rustc-dev/[0-9a-f]{40}/", "<rustc-dev>/", text)
    text = re.sub(r"/rustc/[0-9a-f]{40}/", "<rustc>/", text)
    return text


def run_rustc_case(
    rustc: str,
    src_path: pathlib.Path,
    out_path: pathlib.Path,
    edition: str,
    extra_flags: list[str],
    tmp_dir: str,
) -> dict[str, Any]:
    flags = ["--crate-type", "lib", "--edition", edition] + extra_flags
    cmd = [rustc] + flags + [str(src_path), "-o", str(out_path)]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    stderr = scrub_text(proc.stderr.strip(), tmp_dir)
    error_codes = sorted(set(re.findall(r"error\[(E\d{4})\]", stderr)))
    return {
        "flags": flags,
        "rc": proc.returncode,
        "accepted": proc.returncode == 0,
        "error_codes": error_codes,
        "stderr": stderr,
    }


def extract_compiler_info(rustc: str, cargo: str, stable_rustc: str | None) -> dict[str, Any]:
    vv = subprocess.run([rustc, "-Vv"], capture_output=True, text=True)
    z_help = subprocess.run([rustc, "-Z", "help"], capture_output=True, text=True)
    polonius_help_lines = [
        line.strip()
        for line in (z_help.stdout + "\n" + z_help.stderr).splitlines()
        if "polonius" in line.lower()
    ]
    miri_ver = subprocess.run([cargo, "miri", "--version"], capture_output=True, text=True)
    info: dict[str, Any] = {
        "rustc_vv": vv.stdout.strip(),
        "polonius_z_help": polonius_help_lines,
        "miri_version": miri_ver.stdout.strip() if miri_ver.returncode == 0 else None,
        "stable_rustc_vv": None,
    }
    if stable_rustc:
        sv = subprocess.run([stable_rustc, "-Vv"], capture_output=True, text=True)
        if sv.returncode == 0:
            info["stable_rustc_vv"] = sv.stdout.strip()
    return info


def capture_mir_dumps(
    rustc: str,
    tmp_path: pathlib.Path,
) -> dict[str, Any]:
    dumps: dict[str, Any] = {}
    specs = [
        ("a3_default_nll", "a3_polonius_3way_separator_flow_sensitive_invariance", ["-Zdump-mir=nll"], ["*flow_sensitive_invariance*nll*.mir", "*flow_sensitive_invariance*regioncx.all.dot"]),
        ("a3_next_nll", "a3_polonius_3way_separator_flow_sensitive_invariance", ["-Zpolonius=next", "-Zdump-mir=nll"], ["*flow_sensitive_invariance*nll*.mir"]),
        ("a3_legacy_nll", "a3_polonius_3way_separator_flow_sensitive_invariance", ["-Zpolonius=legacy", "-Zdump-mir=nll"], ["*flow_sensitive_invariance*nll*.mir"]),
        ("a1_next_nll", "a1_polonius_problem_case_3_hashmap_get", ["-Zpolonius=next", "-Zdump-mir=nll"], ["*get_or_insert*nll*.mir"]),
        ("c1_default_built_nll", "c1_two_phase_shared_read_before_activation_ok", ["-Zdump-mir=built | nll"], ["*two_phase_shared_read*built*.mir", "*two_phase_shared_read*nll*.mir"]),
    ]
    for label, case_id, extra_flags, patterns in specs:
        dump_dir = tmp_path / f"dump_{label}"
        dump_dir.mkdir(parents=True, exist_ok=True)
        src = tmp_path / f"{case_id}.rs"
        out = dump_dir / "lib.rlib"
        cmd = [
            rustc,
            "--crate-type",
            "lib",
            "--edition",
            CASES[case_id]["edition"],
            f"-Zdump-mir-dir={dump_dir}",
            *extra_flags,
            str(src),
            "-o",
            str(out),
        ]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        files: dict[str, str] = {}
        for pat in patterns:
            for p in sorted(dump_dir.glob(pat)):
                files[p.name] = scrub_text(p.read_text(), str(tmp_path))
        dumps[label] = {
            "rc": proc.returncode,
            "files": files,
        }
    return dumps


def run_miri_tree_borrows(cargo: str, tmp_path: pathlib.Path) -> dict[str, Any]:
    results: dict[str, Any] = {}
    for cid, src in MIRI_CASES.items():
        proj = tmp_path / f"miri_{cid}"
        (proj / "src").mkdir(parents=True, exist_ok=True)
        (proj / "Cargo.toml").write_text(
            f'[package]\nname = "{cid}"\nversion = "0.1.0"\nedition = "2024"\n'
        )
        (proj / "src" / "main.rs").write_text(src)
        env = dict(os.environ)
        env["MIRIFLAGS"] = "-Zmiri-tree-borrows"
        proc = subprocess.run(
            [cargo, "miri", "run", "--offline"],
            cwd=proj,
            env=env,
            capture_output=True,
            text=True,
        )
        results[cid] = {
            "rc": proc.returncode,
            "stdout": scrub_text(proc.stdout.strip(), str(tmp_path)),
            "stderr": scrub_text(proc.stderr.strip(), str(tmp_path)),
        }
    return results


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rustc", default="rustc")
    ap.add_argument("--cargo", default="cargo")
    ap.add_argument("--stable-rustc", default=None)
    ap.add_argument(
        "--out",
        default=str(
            pathlib.Path(__file__).with_name(
                "probe_polonius_triad_member_constraints_and_two_phase_results.json"
            )
        ),
    )
    args = ap.parse_args()

    compiler_info = extract_compiler_info(args.rustc, args.cargo, args.stable_rustc)
    results: dict[str, Any] = {
        "compiler_info": compiler_info,
        "flag_triad_smoke": {},
        "experiments": {},
        "mir_dumps": {},
        "miri_tree_borrows": {},
    }

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = pathlib.Path(tmp)
        smoke_src = tmp_path / "smoke.rs"
        smoke_src.write_text("pub fn id(x: &mut i32) { *x += 1; }\n")
        for mode_name, flags in MODES:
            results["flag_triad_smoke"][mode_name] = run_rustc_case(
                args.rustc,
                smoke_src,
                tmp_path / f"smoke_{mode_name}.rlib",
                "2024",
                flags,
                tmp,
            )
        if args.stable_rustc and compiler_info["stable_rustc_vv"]:
            results["flag_triad_smoke"]["stable_baseline"] = run_rustc_case(
                args.stable_rustc,
                smoke_src,
                tmp_path / "smoke_stable.rlib",
                "2024",
                [],
                tmp,
            )

        for cid, spec in CASES.items():
            src_path = tmp_path / f"{cid}.rs"
            src_path.write_text(spec["source"])
            modes_out: dict[str, Any] = {}
            for mode_name, flags in MODES:
                modes_out[mode_name] = run_rustc_case(
                    args.rustc,
                    src_path,
                    tmp_path / f"{cid}_{mode_name}.rlib",
                    spec["edition"],
                    flags,
                    tmp,
                )
            if args.stable_rustc and compiler_info["stable_rustc_vv"]:
                modes_out["stable_baseline"] = run_rustc_case(
                    args.stable_rustc,
                    src_path,
                    tmp_path / f"{cid}_stable.rlib",
                    spec["edition"],
                    [],
                    tmp,
                )
            results["experiments"][cid] = {
                "family": spec["family"],
                "edition": spec["edition"],
                "source": spec["source"],
                "modes": modes_out,
            }

        results["mir_dumps"] = capture_mir_dumps(args.rustc, tmp_path)
        if compiler_info["miri_version"] is not None:
            results["miri_tree_borrows"] = run_miri_tree_borrows(args.cargo, tmp_path)

    out_path = pathlib.Path(args.out)
    out_path.write_text(json.dumps(results, indent=2) + "\n")
    print(f"wrote {out_path} ({len(results['experiments'])} cases)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
