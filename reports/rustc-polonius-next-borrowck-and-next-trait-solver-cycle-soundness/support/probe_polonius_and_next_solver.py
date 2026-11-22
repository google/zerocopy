#!/usr/bin/env python3
"""Reproducible empirical probe for rustc Polonius::Next, rustc_next_trait_solver
cycle polarity, -Z assumptions-on-binders #25860 UAF, and zerocopy compilation.

Runs real rustc and Miri subprocesses in an isolated temporary directory and emits
a self-contained JSON report with all host-specific absolute paths scrubbed.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import statistics
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any


POLONIUS_CASES: dict[str, str] = {
    "nll_problem_case_3_hashmap": r"""
use std::collections::HashMap;

pub fn get_or_insert<'a>(map: &'a mut HashMap<u32, u32>, key: u32) -> &'a mut u32 {
    match map.get_mut(&key) {
        Some(v) => return v,
        None => {}
    }
    map.insert(key, 0);
    map.get_mut(&key).unwrap()
}
""",
    "loop_conditional_mut_return": r"""
pub fn find_or_push<'a>(v: &'a mut Vec<u32>, target: u32) -> &'a mut u32 {
    loop {
        if let Some(elem) = v.iter_mut().find(|x| **x == target) {
            return elem;
        }
        v.push(target);
    }
}
""",
    "invariant_backward_loan_must_reject": r"""
pub fn bad_invariant<'a>(p: &'a mut &'a mut i32) -> &'a mut i32 {
    let r = &mut **p;
    let s = &mut **p;
    *r += 1;
    s
}
""",
    "invariant_time_travel_through_mut_ref_must_reject": r"""
pub fn invariant_time_travel() {
    let mut a = 1i32;
    let mut b = 2i32;
    let mut p: &mut i32 = &mut a;
    let q: &mut &mut i32 = &mut p;
    *q = &mut b;
    b = 3;
    let _ = *p;
}
""",
    "aliasing_mut_escape_must_reject": r"""
pub fn aliasing_mut_escape(v: &mut Vec<u32>) -> (&mut u32, &mut u32) {
    let r1: &mut u32 = &mut v[0];
    let r2: &mut u32 = &mut v[1];
    (r1, r2)
}
""",
    "two_phase_borrow_allowed": r"""
pub fn two_phase_push(v: &mut Vec<usize>) {
    v.push(v.len());
}
""",
    "conditional_reborrow_and_mutate_else": r"""
pub fn get_or_mutate<'a>(slice: &'a mut [u32], cond: bool) -> &'a mut u32 {
    let r = &mut slice[0];
    if cond {
        return r;
    }
    slice[0] += 1;
    &mut slice[0]
}
""",
}


NEXT_SOLVER_CASES: dict[str, str] = {
    "coinductive_auto_send_recursive": r"""
pub struct Rec(pub Option<Box<Rec>>);

fn assert_send<T: Send>() {}

pub fn check() {
    assert_send::<Rec>();
}
""",
    "inductive_cycle_in_typeck_rejected": r"""
pub trait Loop {}
impl<T: Loop> Loop for T {}

fn need<T: Loop>() {}

pub fn check() {
    need::<u32>();
}
""",
    "inductive_cycle_in_coherence_overlap_rejected": r"""
pub trait Loop {}
impl<T: Loop> Loop for T {}

pub trait Disjoint {}
impl<T: Loop> Disjoint for T {}
impl Disjoint for u32 {}
""",
    "coherence_unproductive_assoc_norm_rejected": r"""
pub trait Trait {
    type Assoc<T: Trait>;
}

pub struct Overflow;
impl Trait for Overflow {
    type Assoc<T: Trait> = <T as Trait>::Assoc<Overflow>;
}

pub trait Overlap<T, WfHack> {}
impl<T: Trait, U: Copy> Overlap<T::Assoc<T>, U> for T {}
impl<U> Overlap<u32, U> for Overflow {}
""",
    "hrtb_implied_bounds_assumptions_on_binders": r"""
pub fn apply_hrtb<F>(f: F, s: &str) -> usize
where
    F: for<'a> Fn(&'a str) -> &'a str,
{
    f(s).len()
}

pub fn check(s: &str) -> usize {
    apply_hrtb(|x| x, s)
}
""",
    "hrtb_lifetime_transmute_25860_must_reject": r"""
static UNIT: &'static &'static () = &&();

fn foo<'a, 'b, T>(_: &'a &'b (), v: &'b T) -> &'a T {
    v
}

pub fn extend_lifetime<'a, T>(x: &'a T) -> &'static T {
    let f: fn(_, &'a T) -> &'static T = foo;
    f(UNIT, x)
}
""",
    "rpit_defining_use_consistency": r"""
pub fn make_iter(x: u32, cond: bool) -> impl Iterator<Item = u32> {
    if cond {
        core::iter::once(x)
    } else {
        core::iter::once(x.wrapping_add(1))
    }
}
""",
    "marker_trait_overlap_allowed": r"""
#![feature(marker_trait_attr)]

#[marker]
pub trait MarkerOverlap {}
impl<T> MarkerOverlap for T {}
impl MarkerOverlap for u32 {}
""",
    "deep_assoc_proj_normalization": r"""
pub trait Step {
    type Next: Step;
}
pub struct Z;
pub struct S<T>(core::marker::PhantomData<T>);
impl Step for Z {
    type Next = S<Z>;
}
impl<T: Step> Step for S<T> {
    type Next = S<S<T>>;
}

pub fn check() -> <<<<Z as Step>::Next as Step>::Next as Step>::Next as Step>::Next {
    S(core::marker::PhantomData)
}
""",
    "param_env_rigid_alias_vs_normalization": r"""
pub trait AssocTrait {
    type Assoc;
}

pub fn use_bound<T: AssocTrait<Assoc = u32>>(x: T::Assoc) -> u32 {
    x + 1
}

pub fn use_rigid<T: AssocTrait>(x: T::Assoc) -> T::Assoc {
    x
}
""",
}


MIRI_25860_MAIN = r"""
static UNIT: &'static &'static () = &&();

fn foo<'a, 'b, T>(_: &'a &'b (), v: &'b T) -> &'a T {
    v
}

fn extend_lifetime<'a, T>(x: &'a T) -> &'static T {
    let f: fn(_, &'a T) -> &'static T = foo;
    f(UNIT, x)
}

fn main() {
    let dangling: &'static String = {
        let local = String::from("temporary heap buffer");
        extend_lifetime(&local)
    };
    let _len = dangling.len();
}
"""


def scrub_text(text: str, tmpdir: str, extra_roots: list[str] | None = None) -> str:
    """Replace temporary and host-specific absolute paths with stable placeholders."""
    out = text.replace(tmpdir, "<TMP>")
    for root in extra_roots or []:
        if root:
            out = out.replace(root, "<WORKSPACE>")
    home = os.environ.get("HOME", "")
    if home:
        out = out.replace(home, "<HOME>")
    out = re.sub(r"/tmp/[^\s:\"']+", "<TMP>", out)
    home_parent = str(Path.home().parent)
    if home_parent and home_parent != "/":
        out = re.sub(re.escape(home_parent) + r"/[^/\s:\"']+", "<HOME>", out)
    return out


def parse_rustc_stderr(stderr: str, tmpdir: str) -> tuple[list[str], list[str]]:
    scrubbed = scrub_text(stderr, tmpdir)
    codes = sorted(set(re.findall(r"error\[E\d{4}\]", scrubbed)))
    err_lines = [
        line.strip()
        for line in scrubbed.splitlines()
        if line.startswith("error") or line.startswith("error[")
    ]
    return codes, err_lines[:6]


def supports_flag(rustc: str, flags: list[str], tmpdir: str) -> bool:
    rs_path = Path(tmpdir) / "flag_probe.rs"
    out_path = Path(tmpdir) / "flag_probe.rmeta"
    rs_path.write_text("pub fn ok() {}\n", encoding="utf-8")
    proc = subprocess.run(
        [rustc, "--crate-type=lib", "--edition=2021", "--emit=metadata", "-o", str(out_path), *flags, str(rs_path)],
        capture_output=True,
        text=True,
        timeout=30,
    )
    return proc.returncode == 0


def run_rustc_snippet(
    rustc: str,
    src: str,
    extra_flags: list[str],
    tmpdir: str,
    case_name: str,
) -> dict[str, Any]:
    rs_path = Path(tmpdir) / f"{case_name}.rs"
    out_path = Path(tmpdir) / f"{case_name}.rmeta"
    rs_path.write_text(src, encoding="utf-8")
    cmd = [
        rustc,
        "--crate-type=lib",
        "--edition=2021",
        "--emit=metadata",
        "-o",
        str(out_path),
        *extra_flags,
        str(rs_path),
    ]
    t0 = time.perf_counter()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    elapsed_ms = round((time.perf_counter() - t0) * 1000.0, 2)
    codes, err_head = parse_rustc_stderr(proc.stderr, tmpdir)
    return {
        "ok": proc.returncode == 0,
        "rc": proc.returncode,
        "error_codes": codes,
        "err_head": err_head,
        "elapsed_ms": elapsed_ms,
    }


def run_miri_25860(cargo: str, tmpdir: str) -> dict[str, Any]:
    proj = Path(tmpdir) / "miri_25860_uaf"
    (proj / "src").mkdir(parents=True, exist_ok=True)
    (proj / "Cargo.toml").write_text(
        '[package]\nname = "miri_25860_uaf"\nversion = "0.1.0"\nedition = "2021"\n',
        encoding="utf-8",
    )
    (proj / "src" / "main.rs").write_text(MIRI_25860_MAIN, encoding="utf-8")

    env = os.environ.copy()
    env["RUSTFLAGS"] = "-Znext-solver=globally -Zassumptions-on-binders=yes"
    env["CARGO_TARGET_DIR"] = str(Path(tmpdir) / "miri_target")

    ver = subprocess.run([cargo, "miri", "--version"], capture_output=True, text=True, env=env, timeout=60)
    if ver.returncode != 0:
        return {
            "available": False,
            "rc": ver.returncode,
            "stderr_head": scrub_text(ver.stderr, tmpdir).splitlines()[:6],
        }

    t0 = time.perf_counter()
    proc = subprocess.run(
        [cargo, "miri", "run", "--offline"],
        cwd=str(proj),
        capture_output=True,
        text=True,
        env=env,
        timeout=180,
    )
    wall_s = round(time.perf_counter() - t0, 3)
    scrubbed_err = scrub_text(proc.stderr, tmpdir)
    ub_lines = [
        line.strip()
        for line in scrubbed_err.splitlines()
        if any(
            tok in line
            for tok in (
                "Undefined Behavior",
                "dangling reference",
                "use-after-free",
                "error:",
                "= help:",
            )
        )
    ]
    return {
        "available": True,
        "miri_version": ver.stdout.strip(),
        "rustflags": env["RUSTFLAGS"],
        "rc": proc.returncode,
        "wall_s": wall_s,
        "ub_detected": "Undefined Behavior" in scrubbed_err
        and ("dangling" in scrubbed_err or "use-after-free" in scrubbed_err),
        "ub_lines": ub_lines[:10],
    }


def discover_zerocopy_rustc_env_and_cfg(
    cargo: str, crate_dir: Path, tmpdir: str
) -> tuple[dict[str, str], list[str]]:
    """Run build.rs via cargo check once in a temp target dir to harvest CARGO_* env and --cfg flags."""
    env = os.environ.copy()
    env["CARGO_TARGET_DIR"] = str(Path(tmpdir) / "zc_discover_target")
    proc = subprocess.run(
        [cargo, "check", "--lib", "--locked", "--offline", "--no-default-features", "-vv"],
        cwd=str(crate_dir),
        env=env,
        capture_output=True,
        text=True,
        timeout=180,
    )
    cargo_env: dict[str, str] = {}
    cfg_flags: list[str] = []
    for line in proc.stderr.splitlines():
        if "Running `" in line and "--crate-name zerocopy " in line:
            inner = line.split("Running `", 1)[1].rsplit("`", 1)[0]
            tokens = shlex.split(inner)
            i = 0
            while i < len(tokens) and "=" in tokens[i] and not tokens[i].startswith("-"):
                k, v = tokens[i].split("=", 1)
                if k.startswith("CARGO_") or k in ("OUT_DIR",):
                    cargo_env[k] = v
                i += 1
            while i < len(tokens):
                if tokens[i] == "--cfg" and i + 1 < len(tokens):
                    cfg_flags.extend(["--cfg", tokens[i + 1]])
                    i += 2
                else:
                    i += 1
            break
    return cargo_env, cfg_flags


def run_zerocopy_stress(
    rustc: str,
    cargo: str,
    zerocopy_dir: Path,
    tmpdir: str,
    trials: int,
    has_polonius_off: bool,
) -> dict[str, Any]:
    crate_dir = zerocopy_dir
    if not (crate_dir / "src" / "lib.rs").is_file() and (zerocopy_dir / "zerocopy" / "src" / "lib.rs").is_file():
        crate_dir = zerocopy_dir / "zerocopy"
    lib_rs = crate_dir / "src" / "lib.rs"
    if not lib_rs.is_file():
        return {"skipped": True, "reason": "zerocopy src/lib.rs not found"}

    git_rev = "unknown"
    git_proc = subprocess.run(
        ["git", "-C", str(zerocopy_dir), "rev-parse", "HEAD"],
        capture_output=True,
        text=True,
    )
    if git_proc.returncode == 0:
        git_rev = git_proc.stdout.strip()

    cargo_env, cfg_flags = discover_zerocopy_rustc_env_and_cfg(cargo, crate_dir, tmpdir)
    run_env = os.environ.copy()
    run_env.update(cargo_env)
    off_flags = ["-Zpolonius=off"] if has_polonius_off else []

    modes: dict[str, list[str]] = {
        "nll_baseline_default_solver": [*off_flags],
        "polonius_next_default_solver": ["-Zpolonius=next"],
        "nll_baseline_next_solver_globally": [*off_flags, "-Znext-solver=globally"],
        "polonius_next_and_next_solver_globally": ["-Zpolonius=next", "-Znext-solver=globally"],
    }

    results: dict[str, Any] = {
        "zerocopy_revision": git_rev,
        "zerocopy_pkg_version": cargo_env.get("CARGO_PKG_VERSION", "unknown"),
        "cfg_flags_discovered": cfg_flags,
        "trials_per_mode": trials,
        "modes": {},
    }

    # Warm OS page cache with one untimed baseline pass.
    warm_out = Path(tmpdir) / "zerocopy_warm.rmeta"
    subprocess.run(
        [
            rustc,
            "--crate-name=zerocopy",
            "--crate-type=lib",
            "--edition=2021",
            "--cap-lints=allow",
            "--emit=metadata",
            *cfg_flags,
            "-o",
            str(warm_out),
            str(lib_rs),
        ],
        env=run_env,
        capture_output=True,
        text=True,
        timeout=120,
    )

    for mode_name, flags in modes.items():
        samples: list[float] = []
        last_rc = 0
        last_codes: list[str] = []
        last_err_head: list[str] = []
        for trial in range(trials):
            out_path = Path(tmpdir) / f"zerocopy_{mode_name}_{trial}.rmeta"
            cmd = [
                rustc,
                "--crate-name=zerocopy",
                "--crate-type=lib",
                "--edition=2021",
                "--cap-lints=allow",
                "--emit=metadata",
                *cfg_flags,
                *flags,
                "-o",
                str(out_path),
                str(lib_rs),
            ]
            t0 = time.perf_counter()
            proc = subprocess.run(cmd, env=run_env, capture_output=True, text=True, timeout=180)
            dt = round(time.perf_counter() - t0, 4)
            samples.append(dt)
            last_rc = proc.returncode
            last_codes, last_err_head = parse_rustc_stderr(
                scrub_text(proc.stderr, tmpdir, [str(zerocopy_dir), str(crate_dir)]),
                tmpdir,
            )
        results["modes"][mode_name] = {
            "flags": flags,
            "ok": last_rc == 0,
            "rc": last_rc,
            "wall_s_samples": samples,
            "wall_s_median": round(statistics.median(samples), 4),
            "wall_s_mean": round(statistics.mean(samples), 4),
            "error_codes": last_codes,
            "err_head": last_err_head,
        }

    # Single timed trial of Datalog -Zpolonius=legacy (bounded timeout).
    out_legacy = Path(tmpdir) / "zerocopy_polonius_legacy.rmeta"
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            [
                rustc,
                "--crate-name=zerocopy",
                "--crate-type=lib",
                "--edition=2021",
                "--cap-lints=allow",
                "--emit=metadata",
                *cfg_flags,
                "-Zpolonius=legacy",
                "-o",
                str(out_legacy),
                str(lib_rs),
            ],
            env=run_env,
            capture_output=True,
            text=True,
            timeout=90,
        )
        dt = round(time.perf_counter() - t0, 4)
        codes, err_head = parse_rustc_stderr(
            scrub_text(proc.stderr, tmpdir, [str(zerocopy_dir), str(crate_dir)]),
            tmpdir,
        )
        results["modes"]["polonius_legacy_datalog_single_trial"] = {
            "flags": ["-Zpolonius=legacy"],
            "ok": proc.returncode == 0,
            "rc": proc.returncode,
            "wall_s_samples": [dt],
            "wall_s_median": dt,
            "wall_s_mean": dt,
            "error_codes": codes,
            "err_head": err_head,
        }
    except subprocess.TimeoutExpired:
        results["modes"]["polonius_legacy_datalog_single_trial"] = {
            "flags": ["-Zpolonius=legacy"],
            "ok": False,
            "rc": -1,
            "timed_out_after_s": 90,
        }

    base = results["modes"]["nll_baseline_default_solver"]["wall_s_median"]
    if base > 0:
        for mode_name, rec in results["modes"].items():
            if "wall_s_median" in rec:
                rec["delta_pct_vs_nll_baseline"] = round(
                    ((rec["wall_s_median"] - base) / base) * 100.0, 2
                )
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rustc", default="rustc", help="Path to nightly rustc binary")
    parser.add_argument("--cargo", default="cargo", help="Path to nightly cargo binary")
    parser.add_argument(
        "--zerocopy-dir",
        type=Path,
        default=None,
        help="Optional path to a google/zerocopy checkout for full-crate compile stress check",
    )
    parser.add_argument("--trials", type=int, default=5, help="Timed trials per zerocopy mode")
    parser.add_argument("--out", type=Path, required=True, help="Output JSON path")
    args = parser.parse_args()

    rustc_vv = subprocess.run([args.rustc, "-Vv"], capture_output=True, text=True, check=True).stdout.strip()
    z_help = subprocess.run([args.rustc, "-Z", "help"], capture_output=True, text=True, check=True).stdout
    polonius_help_lines = [
        line.strip()
        for line in z_help.splitlines()
        if any(
            k in line
            for k in (
                "polonius=",
                "next-solver=",
                "assumptions-on-binders=",
                "higher-ranked-assumptions=",
            )
        )
    ]

    with tempfile.TemporaryDirectory(prefix="polonius_next_solver_probe_") as tmpdir:
        has_polonius_off = supports_flag(args.rustc, ["-Zpolonius=off"], tmpdir)
        aob_alone_ok = supports_flag(args.rustc, ["-Zassumptions-on-binders=yes"], tmpdir)
        aob_with_next_ok = supports_flag(
            args.rustc, ["-Znext-solver=globally", "-Zassumptions-on-binders=yes"], tmpdir
        )

        polonius_modes: dict[str, list[str] | None] = {
            "rustc_default": [],
            "polonius_off": ["-Zpolonius=off"] if has_polonius_off else None,
            "polonius_next": ["-Zpolonius=next"],
            "polonius_legacy": ["-Zpolonius=legacy"],
        }
        polonius_matrix: dict[str, dict[str, Any]] = {}
        for case_name, src in POLONIUS_CASES.items():
            polonius_matrix[case_name] = {}
            for mode_name, flags in polonius_modes.items():
                if flags is None:
                    polonius_matrix[case_name][mode_name] = {
                        "supported": False,
                        "note": "-Zpolonius=off not recognized by this rustc revision; rustc_default already uses Polonius::Off (NLL)",
                    }
                else:
                    polonius_matrix[case_name][mode_name] = run_rustc_snippet(
                        args.rustc, src, flags, tmpdir, f"pol_{case_name}_{mode_name}"
                    )

        solver_modes: dict[str, list[str]] = {
            "default_solver": [],
            "next_solver_globally": ["-Znext-solver=globally"],
            "assumptions_on_binders": ["-Znext-solver=globally", "-Zassumptions-on-binders=yes"],
        }
        solver_matrix: dict[str, dict[str, Any]] = {}
        for case_name, src in NEXT_SOLVER_CASES.items():
            row: dict[str, Any] = {}
            for mode_name, flags in solver_modes.items():
                row[mode_name] = run_rustc_snippet(
                    args.rustc, src, flags, tmpdir, f"sol_{case_name}_{mode_name}"
                )
            row["default_vs_next_globally_diverge"] = (
                row["default_solver"]["ok"] != row["next_solver_globally"]["ok"]
            )
            row["next_globally_vs_assumptions_on_binders_diverge"] = (
                row["next_solver_globally"]["ok"] != row["assumptions_on_binders"]["ok"]
            )
            solver_matrix[case_name] = row

        miri_uaf = run_miri_25860(args.cargo, tmpdir)

        zerocopy_stress: dict[str, Any]
        if args.zerocopy_dir is not None:
            zerocopy_stress = run_zerocopy_stress(
                args.rustc, args.cargo, args.zerocopy_dir, tmpdir, args.trials, has_polonius_off
            )
        else:
            zerocopy_stress = {"skipped": True, "reason": "--zerocopy-dir not supplied"}

    payload = {
        "rustc_version_verbose": rustc_vv,
        "rustc_z_flag_help": polonius_help_lines,
        "flag_capabilities": {
            "supports_z_polonius_off": has_polonius_off,
            "assumptions_on_binders_alone_compiles_empty_crate": aob_alone_ok,
            "assumptions_on_binders_with_next_solver_compiles_empty_crate": aob_with_next_ok,
        },
        "probe_1_polonius_matrix": polonius_matrix,
        "probe_2_next_solver_matrix": solver_matrix,
        "probe_3_miri_25860_uaf": miri_uaf,
        "probe_4_zerocopy_compile_stress": zerocopy_stress,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    print(f"Wrote probe results to {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
