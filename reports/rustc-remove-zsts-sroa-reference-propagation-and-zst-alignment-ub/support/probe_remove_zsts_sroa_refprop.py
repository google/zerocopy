#!/usr/bin/env python3
"""Reproducible empirical probe for rustc MIR passes RemoveZsts, ReferencePropagation,
and ScalarReplacementOfAggregates, Miri -Zmir-opt-level=1 over-aligned ZST UB erasure,
CheckAlignment interaction with MIRI_DEFAULT_ARGS, and full-crate zerocopy MIR census.

Run:
    python3 support/probe_remove_zsts_sroa_refprop.py --out support/probe_results.json
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


def _build_env() -> dict[str, str]:
    env = os.environ.copy()
    extra_bins = [
        str(Path.home() / ".cargo" / "bin"),
        str(Path.home() / ".elan" / "bin"),
        str(Path.home() / ".local" / "bin"),
    ]
    cur_path = env.get("PATH", "")
    parts = [p for p in cur_path.split(os.pathsep) if p]
    for b in reversed(extra_bins):
        if b not in parts:
            parts.insert(0, b)
    env["PATH"] = os.pathsep.join(parts)
    env["RUST_BACKTRACE"] = "0"
    return env


def scrub_text(text: str, extra_paths: list[tuple[str, str]] | None = None) -> str:
    """Scrub ephemeral temp directories, home directories, and local paths."""
    s = text
    if extra_paths:
        for raw, repl in extra_paths:
            if raw:
                s = s.replace(raw, repl)
    home = str(Path.home())
    if home:
        s = s.replace(home, "<HOME>")
    home_parent = str(Path.home().parent)
    if home_parent and home_parent != "/":
        s = re.sub(re.escape(home_parent) + r"/[A-Za-z0-9._/-]+", "<LOCAL_PATH>", s)
    s = re.sub(r"/tmp/[A-Za-z0-9._/-]+", "<TMP>", s)
    s = re.sub(r"0x[0-9a-fA-F]{6,16}", "<ADDR>", s)
    s = re.sub(r"thread 'main' \(\d+\)", "thread 'main' (<TID>)", s)
    return s


def run_cmd(
    cmd: list[str],
    cwd: Path,
    env: dict[str, str],
    timeout: int = 180,
) -> tuple[int, str, str]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
    )
    return proc.returncode, proc.stdout, proc.stderr


SPECIMENS_PART_A: dict[str, str] = {
    "surface_null_unit_read_black_box": """\
fn main() {
    let p: *const () = core::ptr::null();
    let v: () = unsafe { *p };
    core::hint::black_box(v);
}
""",
    "surface_null_unit_write": """\
fn main() {
    let p: *mut () = core::ptr::null_mut();
    unsafe { *p = (); }
}
""",
    "surface_null_align64_zst_read": """\
#[repr(align(64))]
#[derive(Copy, Clone)]
struct Aligned64Zst;

fn main() {
    let p: *const Aligned64Zst = core::ptr::null();
    let v: Aligned64Zst = unsafe { *p };
    core::hint::black_box(v);
}
""",
    "surface_dangling_align64_zst_read": """\
#[repr(align(64))]
#[derive(Copy, Clone)]
struct Aligned64Zst;

fn main() {
    let p: *const Aligned64Zst = core::ptr::NonNull::<Aligned64Zst>::dangling().as_ptr();
    let v: Aligned64Zst = unsafe { *p };
    core::hint::black_box(v);
}
""",
    "surface_misaligned_align64_zst_write": """\
#[repr(align(64))]
struct Aligned64Zst;

fn main() {
    let buf = [0u64; 16];
    let misaligned = unsafe { buf.as_ptr().cast::<u8>().add(1).cast_mut().cast::<Aligned64Zst>() };
    unsafe { *misaligned = Aligned64Zst; }
}
""",
    "surface_misaligned_align64_zst_read": """\
#[repr(align(64))]
#[derive(Copy, Clone)]
struct Aligned64Zst;

fn main() {
    let buf = [0u64; 16];
    let misaligned = unsafe { buf.as_ptr().cast::<u8>().add(1).cast::<Aligned64Zst>() };
    let v: Aligned64Zst = unsafe { *misaligned };
    core::hint::black_box(v);
}
""",
    "surface_misaligned_align64_zst_place_mention": """\
#[repr(align(64))]
struct Aligned64Zst;

fn main() {
    let buf = [0u64; 16];
    let misaligned = unsafe { buf.as_ptr().cast::<u8>().add(1).cast::<Aligned64Zst>() };
    unsafe { let _ = *misaligned; }
}
""",
    "surface_uninit_ptr_to_zst_write": """\
use core::mem::MaybeUninit;

fn main() {
    let uninit_ptr = MaybeUninit::<*mut ()>::uninit();
    let p: *mut () = unsafe { uninit_ptr.assume_init() };
    unsafe { *p = (); }
}
""",
}


LITMUS_PART_B_SRC = """\
#![allow(dead_code)]

#[derive(Copy, Clone)]
pub struct Pair(pub u64, pub u64);

#[derive(Copy, Clone)]
pub struct Inner {
    pub x: u64,
    pub y: u64,
}

#[derive(Copy, Clone)]
pub struct Outer {
    pub inner: Inner,
    pub z: u64,
}

#[repr(C)]
pub union WordOrBytes {
    pub word: u64,
    pub lo: u32,
}

pub enum TagOrVal {
    Empty,
    Val(u64),
}

#[inline(never)]
pub fn refprop_anon_borrow_unlocks_sroa(x: u64, y: u64) -> u64 {
    let p = Pair(x, y);
    (&p).0.wrapping_add((&p).1)
}

#[inline(never)]
pub fn refprop_named_borrow_blocked_by_debuginfo(x: u64, y: u64) -> u64 {
    let p = Pair(x, y);
    let r = &p;
    r.0.wrapping_add(r.1)
}

#[inline(never)]
pub fn refprop_mut_fully_replaced(x: u64) -> u64 {
    let mut slot = x;
    let r = &mut slot;
    *r = (*r).wrapping_add(10);
    let r2 = r;
    *r2 = (*r2).wrapping_mul(2);
    slot
}

#[inline(never)]
pub fn refprop_mut_escaped_blocks_partial(x: u64, sink: fn(*mut u64)) -> u64 {
    let mut slot = x;
    let r = &mut slot;
    *r = (*r).wrapping_add(1);
    let raw: *mut u64 = r;
    sink(raw);
    slot
}

#[inline(never)]
pub fn sroa_multi_iter_nested_and_move(x: u64, y: u64, z: u64) -> u64 {
    let a = Outer { inner: Inner { x, y }, z };
    let b = a;
    b.inner.x.wrapping_add(b.inner.y).wrapping_add(b.z)
}

#[inline(never)]
pub fn sroa_excluded_union_and_enum(v: u64) -> u64 {
    let u = WordOrBytes { word: v };
    let e = TagOrVal::Val(unsafe { u.lo } as u64);
    match e {
        TagOrVal::Empty => 0,
        TagOrVal::Val(n) => n,
    }
}

#[inline(never)]
pub fn sroa_excluded_address_taken(x: u64, y: u64) -> u64 {
    let p = Pair(x, y);
    let raw_first = &raw const p.0;
    let first = unsafe { *raw_first };
    first.wrapping_add(p.1)
}
"""


def extract_diag_head(stderr: str) -> list[str]:
    lines = [
        ln
        for ln in stderr.splitlines()
        if not ln.startswith("warning: You have explicitly enabled MIR optimizations")
        and not ln.startswith("warning: 1 warning emitted")
        and ln.strip() != ""
    ]
    return lines[:5]


def run_part_a(
    env: dict[str, str],
    miri_bin: str,
    miri_sysroot: str,
    td: Path,
) -> dict[str, Any]:
    modes: dict[str, tuple[str, list[str]]] = {
        "miri_opt0_preserve_ub": (
            "miri",
            ["-Zmir-opt-level=0", "-Zmir-preserve-ub=yes"],
        ),
        "miri_opt0_plus_RemoveZsts": (
            "miri",
            ["-Zmir-opt-level=0", "-Zmir-preserve-ub=yes", "-Zmir-enable-passes=+RemoveZsts"],
        ),
        "miri_opt1_default_preserve_ub": (
            "miri",
            ["-Zmir-opt-level=1", "-Zmir-preserve-ub=yes"],
        ),
        "miri_opt1_with_ub_checks_yes": (
            "miri",
            ["-Zmir-opt-level=1", "-Zmir-preserve-ub=yes", "-Zub-checks=yes"],
        ),
        "miri_opt1_force_enable_CheckAlignment": (
            "miri",
            [
                "-Zmir-opt-level=1",
                "-Zmir-preserve-ub=yes",
                "-Zub-checks=yes",
                "-Zmir-enable-passes=+CheckAlignment",
            ],
        ),
        "native_opt1_ub_checks_yes": (
            "native",
            ["-Copt-level=0", "-Zmir-opt-level=1", "-Zub-checks=yes"],
        ),
    }

    results: dict[str, Any] = {}
    for spec_name, src in SPECIMENS_PART_A.items():
        spec_dir = td / f"part_a_{spec_name}"
        spec_dir.mkdir(parents=True, exist_ok=True)
        rs_file = spec_dir / f"{spec_name}.rs"
        rs_file.write_text(src, encoding="utf-8")

        # Dump MIR before/after RemoveZsts at -Zmir-opt-level=1 -Zmir-preserve-ub=yes -Zub-checks=no
        mir_dir = spec_dir / "mir_dump"
        rc_dump, _, err_dump = run_cmd(
            [
                "rustc",
                "--edition=2024",
                "-Copt-level=0",
                "-Zmir-opt-level=1",
                "-Zmir-preserve-ub=yes",
                "-Zub-checks=no",
                "-Zdump-mir=RemoveZsts",
                f"-Zdump-mir-dir={mir_dir}",
                "--emit=mir",
                str(rs_file),
                "-o",
                str(spec_dir / "out.mir"),
            ],
            cwd=spec_dir,
            env=env,
        )
        if rc_dump != 0:
            raise RuntimeError(f"MIR dump failed for {spec_name}: {err_dump}")

        before_files = sorted(mir_dir.glob("*main*.RemoveZsts.before.mir"))
        after_files = sorted(mir_dir.glob("*main*.RemoveZsts.after.mir"))
        before_mir = (
            scrub_text(before_files[0].read_text(encoding="utf-8"), [(str(spec_dir), "<SPEC_DIR>")])
            if before_files
            else ""
        )
        after_mir = (
            scrub_text(after_files[0].read_text(encoding="utf-8"), [(str(spec_dir), "<SPEC_DIR>")])
            if after_files
            else ""
        )

        mode_results: dict[str, Any] = {}
        for mode_name, (runner_kind, flags) in modes.items():
            if runner_kind == "miri":
                rc, out, err = run_cmd(
                    [
                        miri_bin,
                        "--edition=2024",
                        "--sysroot",
                        miri_sysroot,
                        *flags,
                        str(rs_file),
                    ],
                    cwd=spec_dir,
                    env=env,
                )
                scrubbed_err = scrub_text(err, [(str(spec_dir), "<SPEC_DIR>")])
                mode_results[mode_name] = {
                    "rc": rc,
                    "ub_or_panic_caught": rc != 0,
                    "miri_opt_warning_emitted": "explicitly enabled MIR optimizations" in err,
                    "diag_head": extract_diag_head(scrubbed_err),
                }
            else:
                bin_path = spec_dir / f"bin_{mode_name}"
                rc_c, _, err_c = run_cmd(
                    [
                        "rustc",
                        "--edition=2024",
                        *flags,
                        str(rs_file),
                        "-o",
                        str(bin_path),
                    ],
                    cwd=spec_dir,
                    env=env,
                )
                if rc_c != 0:
                    raise RuntimeError(f"Native compile failed for {spec_name}: {err_c}")
                rc_r, _, err_r = run_cmd([str(bin_path)], cwd=spec_dir, env=env)
                scrubbed_err = scrub_text(err_r, [(str(spec_dir), "<SPEC_DIR>")])
                mode_results[mode_name] = {
                    "rc": rc_r,
                    "ub_or_panic_caught": rc_r != 0,
                    "diag_head": extract_diag_head(scrubbed_err),
                }

        results[spec_name] = {
            "before_RemoveZsts_mir": before_mir,
            "after_RemoveZsts_mir": after_mir,
            "modes": mode_results,
        }
    return results


def analyze_mir_body_text(mir_text: str) -> dict[str, int | bool]:
    """Count projections, borrows, and ZST constants strictly within basic-block statements/terminators."""
    in_bb = False
    brace_depth = 0
    field_projections = 0
    direct_local_field_projections = 0
    deref_projections = 0
    other_projections = 0
    ref_rvalues = 0
    zst_const_ops = 0

    for raw_line in mir_text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("//"):
            continue
        if not in_bb:
            if re.match(r"^bb\d+\s*(?:\(cleanup\))?\s*:\s*\{$", line):
                in_bb = True
                brace_depth = 1
            continue

        brace_depth += line.count("{") - line.count("}")
        if brace_depth <= 0:
            in_bb = False
            continue

        # Strip string literals so text inside panic strings does not pollute structural counts
        clean = re.sub(r'"(?:\\.|[^"\\])*"', '""', line)
        # Strip trailing comments
        clean = clean.split("//", 1)[0]

        derefs = len(re.findall(r"\(\*", clean))
        # All PlaceElem::Field projections (both direct `_3.0` and nested `((_3.0).1)` / `((*_1).0)`)
        fields = len(re.findall(r"(?:_[0-9]+|\))\.\d+(?=\s*:|\)|\.|\[|\s|,|;)", clean))
        # Direct unprojected-base local field projections `_3.0` (excluding `(*_1).0` and nested `).0`)
        direct_local_fields = len(
            re.findall(r"(?<!\*)(?<![A-Za-z0-9_])_[0-9]+\.\d+(?=\s*:|\)|\.|\[|\s|,|;)", clean)
        )
        # Index / ConstantIndex / Subslice / Downcast projections
        indices = len(re.findall(r"(?:_[0-9]+|\))\[[^\]]+\]", clean))
        downcasts = len(re.findall(r"\(_[0-9]+\s+as\s+[A-Za-z0-9_:]+\)", clean))

        refs = len(re.findall(r"=\s*&(?:raw\s+(?:const|mut)|mut)?\s", clean))
        zsts = len(re.findall(r"\bconst\s+(?:\(\)|ZeroSized\b)", clean))

        deref_projections += derefs
        field_projections += fields
        direct_local_field_projections += direct_local_fields
        other_projections += indices + downcasts
        ref_rvalues += refs
        zst_const_ops += zsts

    projection_free = (deref_projections + field_projections + other_projections) == 0
    ref_free = ref_rvalues == 0
    return {
        "projection_free": projection_free,
        "ref_free": ref_free,
        "pure_unprojected_noref": projection_free and ref_free,
        "field_projections": field_projections,
        "direct_local_field_projections": direct_local_field_projections,
        "deref_projections": deref_projections,
        "other_projections": other_projections,
        "ref_rvalues": ref_rvalues,
        "zst_const_ops": zst_const_ops,
    }


def run_part_b(env: dict[str, str], td: Path) -> dict[str, Any]:
    b_dir = td / "part_b"
    b_dir.mkdir(parents=True, exist_ok=True)
    rs_file = b_dir / "litmus.rs"
    rs_file.write_text(LITMUS_PART_B_SRC, encoding="utf-8")
    mir_dir = b_dir / "mir_dump"

    rc, _, err = run_cmd(
        [
            "rustc",
            "--edition=2024",
            "--crate-type=lib",
            "-Copt-level=2",
            "-Zmir-opt-level=2",
            "-Zdump-mir=ReferencePropagation|ScalarReplacementOfAggregates",
            f"-Zdump-mir-dir={mir_dir}",
            "--emit=mir",
            str(rs_file),
            "-o",
            str(b_dir / "litmus.mir"),
        ],
        cwd=b_dir,
        env=env,
    )
    if rc != 0:
        raise RuntimeError(f"Part B compile failed: {err}")

    fns = [
        "refprop_anon_borrow_unlocks_sroa",
        "refprop_named_borrow_blocked_by_debuginfo",
        "refprop_mut_fully_replaced",
        "refprop_mut_escaped_blocks_partial",
        "sroa_multi_iter_nested_and_move",
        "sroa_excluded_union_and_enum",
        "sroa_excluded_address_taken",
    ]
    out: dict[str, Any] = {}
    for fn_name in fns:
        rp_b = sorted(mir_dir.glob(f"*{fn_name}*.ReferencePropagation.before.mir"))
        rp_a = sorted(mir_dir.glob(f"*{fn_name}*.ReferencePropagation.after.mir"))
        sr_b = sorted(mir_dir.glob(f"*{fn_name}*.ScalarReplacementOfAggregates.before.mir"))
        sr_a = sorted(mir_dir.glob(f"*{fn_name}*.ScalarReplacementOfAggregates.after.mir"))
        if not (rp_b and rp_a and sr_b and sr_a):
            raise RuntimeError(f"Missing MIR dump files for {fn_name}")

        rp_b_txt = scrub_text(rp_b[0].read_text(encoding="utf-8"), [(str(b_dir), "<LITMUS_DIR>")])
        rp_a_txt = scrub_text(rp_a[0].read_text(encoding="utf-8"), [(str(b_dir), "<LITMUS_DIR>")])
        sr_b_txt = scrub_text(sr_b[0].read_text(encoding="utf-8"), [(str(b_dir), "<LITMUS_DIR>")])
        sr_a_txt = scrub_text(sr_a[0].read_text(encoding="utf-8"), [(str(b_dir), "<LITMUS_DIR>")])

        out[fn_name] = {
            "before_ReferencePropagation": analyze_mir_body_text(rp_b_txt),
            "after_ReferencePropagation": analyze_mir_body_text(rp_a_txt),
            "after_ScalarReplacementOfAggregates": analyze_mir_body_text(sr_a_txt),
            "refprop_changed_mir": "\n".join(rp_b_txt.splitlines()[1:])
            != "\n".join(rp_a_txt.splitlines()[1:]),
            "sroa_changed_mir": "\n".join(sr_b_txt.splitlines()[1:])
            != "\n".join(sr_a_txt.splitlines()[1:]),
            "final_sroa_after_mir": sr_a_txt,
        }
    return out


def summarize_pass_dir(mir_dir: Path, pass_name: str) -> dict[str, Any]:
    before_files = sorted(mir_dir.glob(f"*.{pass_name}.before.mir"))
    keys = [
        "bodies",
        "projection_free_bodies",
        "ref_free_bodies",
        "pure_unprojected_noref_bodies",
        "field_projections",
        "direct_local_field_projections",
        "deref_projections",
        "other_projections",
        "ref_rvalues",
        "zst_const_ops",
    ]
    before_tot = {k: 0 for k in keys}
    after_tot = {k: 0 for k in keys}
    bodies_modified = 0

    for bf in before_files:
        af = Path(str(bf).replace(".before.mir", ".after.mir"))
        if not af.exists():
            continue
        btxt = bf.read_text(encoding="utf-8", errors="replace")
        atxt = af.read_text(encoding="utf-8", errors="replace")
        if "\n".join(btxt.splitlines()[1:]) != "\n".join(atxt.splitlines()[1:]):
            bodies_modified += 1

        bm = analyze_mir_body_text(btxt)
        am = analyze_mir_body_text(atxt)

        for tot, m in ((before_tot, bm), (after_tot, am)):
            tot["bodies"] += 1
            tot["projection_free_bodies"] += int(bool(m["projection_free"]))
            tot["ref_free_bodies"] += int(bool(m["ref_free"]))
            tot["pure_unprojected_noref_bodies"] += int(bool(m["pure_unprojected_noref"]))
            tot["field_projections"] += int(m["field_projections"])
            tot["direct_local_field_projections"] += int(m["direct_local_field_projections"])
            tot["deref_projections"] += int(m["deref_projections"])
            tot["other_projections"] += int(m["other_projections"])
            tot["ref_rvalues"] += int(m["ref_rvalues"])
            tot["zst_const_ops"] += int(m["zst_const_ops"])

    delta = {k: after_tot[k] - before_tot[k] for k in keys}
    total_bodies = after_tot["bodies"]
    return {
        "bodies_modified_by_pass": bodies_modified,
        "bodies_modified_pct": round(100.0 * bodies_modified / total_bodies, 2)
        if total_bodies
        else 0.0,
        "before": before_tot,
        "after": after_tot,
        "delta": delta,
        "after_pure_unprojected_noref_pct": round(
            100.0 * after_tot["pure_unprojected_noref_bodies"] / total_bodies, 2
        )
        if total_bodies
        else 0.0,
    }


def find_default_zerocopy_lib() -> Path | None:
    env_override = os.environ.get("ZEROCOPY_LIB_RS")
    if env_override and Path(env_override).is_file():
        return Path(env_override)
    candidates = [
        Path.cwd() / "zerocopy" / "src" / "lib.rs",
        Path.cwd() / "src" / "lib.rs",
    ]
    projects_dir = Path.home() / "Projects"
    if projects_dir.is_dir():
        for child in sorted(projects_dir.iterdir()):
            cand = child / "zerocopy" / "zerocopy" / "src" / "lib.rs"
            if cand.is_file():
                candidates.append(cand)
    for c in candidates:
        if c.is_file() and "zerocopy" in c.read_text(encoding="utf-8", errors="replace")[:2000]:
            return c
    return None


def run_part_c_zerocopy(
    env: dict[str, str],
    td: Path,
    zerocopy_lib_rs: Path,
) -> dict[str, Any]:
    cargo_toml = zerocopy_lib_rs.parent.parent / "Cargo.toml"
    pkg_version = "0.8.64"
    if cargo_toml.is_file():
        m = re.search(r'^version\s*=\s*"([^"]+)"', cargo_toml.read_text(encoding="utf-8"), re.M)
        if m:
            pkg_version = m.group(1)

    git_rev = "unknown"
    rc_git, out_git, _ = run_cmd(["git", "rev-parse", "HEAD"], cwd=zerocopy_lib_rs.parent, env=env)
    if rc_git == 0:
        git_rev = out_git.strip()

    zc_env = env.copy()
    zc_env["CARGO_PKG_VERSION"] = pkg_version

    # Check rustc minor version to pass no_zerocopy_allocator_api_1_100_0 when rustc < 1.100.0
    _, ver_out, _ = run_cmd(["rustc", "--version"], cwd=td, env=env)
    ver_m = re.search(r"rustc\s+(\d+)\.(\d+)\.", ver_out)
    extra_cfgs: list[str] = []
    if ver_m and (int(ver_m.group(1)), int(ver_m.group(2))) < (1, 100):
        extra_cfgs = ["--cfg", "no_zerocopy_allocator_api_1_100_0"]

    c_dir = td / "part_c_zerocopy"
    c_dir.mkdir(parents=True, exist_ok=True)
    mir_dir = c_dir / "mir_dump"

    rc, _, err = run_cmd(
        [
            "rustc",
            "--edition=2021",
            "--crate-name=zerocopy",
            "--crate-type=lib",
            "-Copt-level=2",
            "-Zmir-opt-level=2",
            "-Zdump-mir=RemoveZsts|ReferencePropagation|ScalarReplacementOfAggregates|SimplifyLocals-before-const-prop|DeadStoreElimination-initial|SimplifyLocals-final",
            f"-Zdump-mir-dir={mir_dir}",
            "--emit=mir",
            *extra_cfgs,
            str(zerocopy_lib_rs),
            "-o",
            str(c_dir / "zerocopy.mir"),
        ],
        cwd=c_dir,
        env=zc_env,
        timeout=240,
    )
    if rc != 0:
        raise RuntimeError(f"zerocopy MIR dump failed: {err}")

    return {
        "zerocopy_package_version": pkg_version,
        "zerocopy_git_revision": git_rev,
        "extra_cfgs": extra_cfgs,
        "RemoveZsts": summarize_pass_dir(mir_dir, "RemoveZsts"),
        "ReferencePropagation": summarize_pass_dir(mir_dir, "ReferencePropagation"),
        "ScalarReplacementOfAggregates": summarize_pass_dir(
            mir_dir, "ScalarReplacementOfAggregates"
        ),
        "SimplifyLocals_before_const_prop": summarize_pass_dir(
            mir_dir, "SimplifyLocals-before-const-prop"
        ),
        "DeadStoreElimination_initial": summarize_pass_dir(
            mir_dir, "DeadStoreElimination-initial"
        ),
        "SimplifyLocals_final": summarize_pass_dir(mir_dir, "SimplifyLocals-final"),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--zerocopy-lib-rs",
        type=Path,
        default=None,
        help="Path to zerocopy/src/lib.rs (auto-detected if omitted)",
    )
    parser.add_argument(
        "--skip-zerocopy",
        action="store_true",
        help="Run only Part A (Miri ZST UB erasure matrix) and Part B (RefProp/SROA litmus)",
    )
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    env = _build_env()
    rc_v, rustc_vv, err_v = run_cmd(["rustc", "--version", "-v"], cwd=Path.cwd(), env=env)
    if rc_v != 0:
        raise RuntimeError(f"rustc --version -v failed: {err_v}")

    _, sysroot_out, _ = run_cmd(["rustc", "--print", "sysroot"], cwd=Path.cwd(), env=env)
    rustc_sysroot = Path(sysroot_out.strip())
    miri_bin = str(rustc_sysroot / "bin" / "miri")
    if not Path(miri_bin).is_file():
        raise RuntimeError("miri binary not found in rustc sysroot")

    rc_ms, miri_sysroot_out, err_ms = run_cmd(
        ["cargo", "miri", "setup", "--print-sysroot"], cwd=Path.cwd(), env=env, timeout=240
    )
    if rc_ms != 0:
        raise RuntimeError(f"cargo miri setup --print-sysroot failed: {err_ms}")
    miri_sysroot = miri_sysroot_out.strip()

    with tempfile.TemporaryDirectory(prefix="probe_rz_sroa_rp_") as td_str:
        td = Path(td_str)
        part_a = run_part_a(env, miri_bin, miri_sysroot, td)
        part_b = run_part_b(env, td)

        part_c: dict[str, Any] | None = None
        if not args.skip_zerocopy:
            zc_lib = args.zerocopy_lib_rs or find_default_zerocopy_lib()
            if zc_lib is None or not zc_lib.is_file():
                raise RuntimeError(
                    "Could not locate zerocopy/src/lib.rs; pass --zerocopy-lib-rs or --skip-zerocopy"
                )
            part_c = run_part_c_zerocopy(env, td, zc_lib)

    payload: dict[str, Any] = {
        "rustc_version_verbose": rustc_vv.strip(),
        "part_a_miri_zst_ub_erasure_matrix": part_a,
        "part_b_refprop_and_sroa_mir_litmus": part_b,
    }
    if part_c is not None:
        payload["part_c_zerocopy_mir_pass_census"] = part_c

    text = json.dumps(payload, indent=2, sort_keys=False) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text, encoding="utf-8")
        print(f"wrote {args.out}")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
