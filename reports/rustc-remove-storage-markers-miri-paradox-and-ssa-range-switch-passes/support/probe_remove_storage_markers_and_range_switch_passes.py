#!/usr/bin/env python3
"""Self-contained empirical probe for:
1. `RemoveStorageMarkers` x `Session::emit_lifetime_markers` paradoxical Miri
   stack use-after-scope UB erasure across `-Zmir-opt-level` and `-Copt-level`.
2. `SsaRangePropagation` (singleton `WrappingRange`, `< 16` target cutoff,
   `has_unique_predecessor`, `Assume`/`Assert`, and docstring inequality reality).
3. `SimplifyComparisonIntegral` (`Eq`/`Ne`, `Move -> Copy`, `StorageDead`).
4. `EarlyOtherwiseBranch` x `UnreachableEnumBranching` (`Option<()>` vs 3-variant
   exhaustive enums and primitive `u32`).
5. `Subtyper` (`CastKind::Subtype` post-erasure on HRTB vs covariant references).
6. Live `google/zerocopy` MIR pass census across `-Copt-level=0` vs `-Copt-level=1`.

All temporary crates and `CARGO_TARGET_DIR` paths live strictly inside
`tempfile.TemporaryDirectory`, and outputs are scrubbed of local paths.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def ensure_cargo_on_path() -> None:
    add = []
    for cand in (Path.home() / ".cargo" / "bin", Path.home() / ".local" / "bin"):
        if cand.is_dir():
            add.append(str(cand))
    cur = os.environ.get("PATH", "")
    parts = [p for p in cur.split(os.pathsep) if p]
    for d in reversed(add):
        if d not in parts:
            parts.insert(0, d)
    os.environ["PATH"] = os.pathsep.join(parts)


def scrub_text(text: str, replacements: list[tuple[str, str]] | None = None) -> str:
    if replacements:
        for old, new in sorted(replacements, key=lambda kv: len(kv[0]), reverse=True):
            if old:
                text = text.replace(old, new)
    text = re.sub(r"/home/[^/\s\"']+", "$HOME", text)
    text = re.sub(r"/Users/[^/\s\"']+", "$HOME", text)
    text = re.sub(r"/tmp/[^/\s\"']+", "$TMP", text)
    return text


def run_cmd(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 300,
) -> dict:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
    )
    return {
        "returncode": proc.returncode,
        "stdout": proc.stdout.decode("utf-8", "replace"),
        "stderr": proc.stderr.decode("utf-8", "replace"),
    }


def extract_ub_head(stderr: str) -> list[str]:
    lines = stderr.splitlines()
    for i, line in enumerate(lines):
        if "error: Undefined Behavior:" in line:
            return lines[i : min(len(lines), i + 4)]
    return []


def count_mir_metrics(txt: str) -> dict:
    return {
        "bodies": 1,
        "bbs": len(re.findall(r"^\s*bb\d+:\s*\{", txt, re.M)),
        "assigns": len(re.findall(r"^\s*_[0-9]+.*=\s", txt, re.M)),
        "switchints": txt.count("switchInt("),
        "returns": len(re.findall(r"^\s*return;", txt, re.M)),
        "subtype_casts": txt.count("(Subtype)"),
        "storage_live": txt.count("StorageLive("),
        "storage_dead": txt.count("StorageDead("),
        "storage_markers": txt.count("StorageLive(") + txt.count("StorageDead("),
    }


def find_mir(dump_dir: Path, fn_frag: str, pass_frag: str, stage: str) -> Path | None:
    matches = sorted(dump_dir.glob(f"*{fn_frag}*{pass_frag}.{stage}.mir"))
    return matches[0] if matches else None


def run_part_a(tmp_root: Path, replacements: list[tuple[str, str]]) -> dict:
    crate_dir = tmp_root / "miri_paradox_crate"
    bin_dir = crate_dir / "src" / "bin"
    bin_dir.mkdir(parents=True, exist_ok=True)
    (crate_dir / "Cargo.toml").write_text(
        '[package]\nname = "rsm_paradox_probe"\nversion = "0.1.0"\nedition = "2021"\n',
        encoding="utf-8",
    )

    single_scope_src = """
#[inline(never)]
fn use_after_scope_value() -> i32 {
    let ptr: *const i32;
    {
        let x: i32 = 42;
        ptr = &raw const x;
    }
    unsafe { *ptr }
}

fn main() {
    let v = use_after_scope_value();
    std::hint::black_box(v);
}
""".lstrip()

    loop_alias_src = """
#[inline(never)]
fn loop_cross_iter_alias(write_on_second: bool) -> i32 {
    let mut p: *const i32 = core::ptr::null();
    let mut observed: i32 = 0;
    let mut i: i32 = 0;
    while i < 2 {
        if i == 0 || write_on_second {
            let x: i32 = i + 10;
            if i == 0 {
                p = &raw const x;
            } else {
                observed = unsafe { *p };
            }
        } else {
            observed = unsafe { *p };
        }
        i += 1;
    }
    observed
}

fn main() {
    let arg = std::env::args().nth(1).unwrap_or_default();
    let write_on_second = arg == "overwrite";
    let v = loop_cross_iter_alias(write_on_second);
    println!("observed={v}");
}
""".lstrip()

    (bin_dir / "single_scope.rs").write_text(single_scope_src, encoding="utf-8")
    (bin_dir / "loop_alias.rs").write_text(loop_alias_src, encoding="utf-8")

    configs = [
        ("miri_mir0_opt0", ["-Zmir-opt-level=0", "-Copt-level=0"]),
        ("miri_mir1_opt0_ub_erased", ["-Zmir-opt-level=1", "-Copt-level=0"]),
        ("miri_mir2_opt0_ub_erased", ["-Zmir-opt-level=2", "-Copt-level=0"]),
        (
            "miri_mir2_opt0_explicit_preserve_ub",
            ["-Zmir-opt-level=2", "-Copt-level=0", "-Zmir-preserve-ub=yes"],
        ),
        ("miri_mir2_opt1_ub_restored", ["-Zmir-opt-level=2", "-Copt-level=1"]),
        (
            "miri_mir1_opt0_disable_rsm_ub_restored",
            ["-Zmir-opt-level=1", "-Copt-level=0", "-Zmir-enable-passes=-RemoveStorageMarkers"],
        ),
        (
            "miri_mir2_opt0_disable_rsm_ub_restored",
            ["-Zmir-opt-level=2", "-Copt-level=0", "-Zmir-enable-passes=-RemoveStorageMarkers"],
        ),
    ]

    env_base = dict(os.environ)
    single_results = {}
    for cfg_name, flags in configs:
        tdir = tmp_root / f"target_{cfg_name}"
        env = dict(env_base, CARGO_TARGET_DIR=str(tdir), MIRIFLAGS=" ".join(flags))
        res = run_cmd(
            ["cargo", "miri", "run", "--quiet", "--bin", "single_scope"],
            cwd=crate_dir,
            env=env,
        )
        warnings = [
            l.strip()
            for l in res["stderr"].splitlines()
            if l.strip().startswith("warning:")
        ]
        single_results[cfg_name] = {
            "flags": flags,
            "miri_rc": res["returncode"],
            "diag_head": [scrub_text(l, replacements) for l in extract_ub_head(res["stderr"])],
            "warnings": [scrub_text(w, replacements) for w in warnings],
            "stderr_scrubbed": scrub_text(res["stderr"], replacements),
        }

    # Loop cross-iteration scope probe:
    # - Without overwrite on iteration 1: `mir2/opt0` erases StorageDead and observes `observed=10` (`rc = 0`) even under Stacked Borrows.
    # - With overwrite on iteration 1: `mir0/opt0` reports freed-alloc UB; `mir2/opt0` reuses the same AllocId (triggering Stacked Borrows write-invalidation, or silently reading `observed=11` with `-Zmiri-disable-stacked-borrows`).
    loop_results = {}
    for cfg_name, flags, extra_args in [
        ("no_overwrite_mir0_opt0", ["-Zmir-opt-level=0", "-Copt-level=0"], []),
        ("no_overwrite_mir2_opt0_ub_erased", ["-Zmir-opt-level=2", "-Copt-level=0"], []),
        ("no_overwrite_mir2_opt1_ub_restored", ["-Zmir-opt-level=2", "-Copt-level=1"], []),
        ("overwrite_mir0_opt0", ["-Zmir-opt-level=0", "-Copt-level=0"], ["--", "overwrite"]),
        ("overwrite_mir2_opt0_sb", ["-Zmir-opt-level=2", "-Copt-level=0"], ["--", "overwrite"]),
        (
            "overwrite_mir2_opt0_no_sb_alias_11",
            ["-Zmir-opt-level=2", "-Copt-level=0", "-Zmiri-disable-stacked-borrows"],
            ["--", "overwrite"],
        ),
    ]:
        tdir = tmp_root / f"target_loop_{cfg_name}"
        env = dict(env_base, CARGO_TARGET_DIR=str(tdir), MIRIFLAGS=" ".join(flags))
        res = run_cmd(
            ["cargo", "miri", "run", "--quiet", "--bin", "loop_alias"] + extra_args,
            cwd=crate_dir,
            env=env,
        )
        loop_results[cfg_name] = {
            "flags": flags,
            "args": extra_args,
            "miri_rc": res["returncode"],
            "stdout": scrub_text(res["stdout"].strip(), replacements),
            "diag_head": [scrub_text(l, replacements) for l in extract_ub_head(res["stderr"])],
        }

    # Direct rustc MIR dumps for use_after_scope_value confirming RemoveStorageMarkers triggers
    mir_dumps = {}
    for mode_name, rflags in [
        ("mir0_opt0", ["-Zmir-opt-level=0", "-Copt-level=0"]),
        ("mir2_opt0", ["-Zmir-opt-level=2", "-Copt-level=0"]),
        ("mir2_opt0_preserve_ub", ["-Zmir-opt-level=2", "-Copt-level=0", "-Zmir-preserve-ub=yes"]),
        ("mir2_opt1", ["-Zmir-opt-level=2", "-Copt-level=1"]),
    ]:
        dd = tmp_root / f"rsm_dump_{mode_name}"
        dd.mkdir(parents=True, exist_ok=True)
        out_bin = tmp_root / f"single_{mode_name}"
        run_cmd(
            [
                "rustc",
                "--edition=2021",
                str(bin_dir / "single_scope.rs"),
                "-o",
                str(out_bin),
                "-Zdump-mir=RemoveStorageMarkers",
                f"-Zdump-mir-dir={dd}",
            ]
            + rflags,
            cwd=tmp_root,
            env=env_base,
        )
        bef = find_mir(dd, "use_after_scope_value", "RemoveStorageMarkers", "before")
        aft = find_mir(dd, "use_after_scope_value", "RemoveStorageMarkers", "after")
        mir_dumps[mode_name] = {
            "flags": rflags,
            "rsm_before_present": bef is not None,
            "rsm_after_present": aft is not None,
            "before_metrics": count_mir_metrics(bef.read_text("utf-8")) if bef else None,
            "after_metrics": count_mir_metrics(aft.read_text("utf-8")) if aft else None,
            "before_mir": scrub_text(bef.read_text("utf-8"), replacements) if bef else None,
            "after_mir": scrub_text(aft.read_text("utf-8"), replacements) if aft else None,
        }

    # Sanity assertions
    assert single_results["miri_mir0_opt0"]["miri_rc"] == 1
    assert single_results["miri_mir1_opt0_ub_erased"]["miri_rc"] == 0
    assert single_results["miri_mir2_opt0_ub_erased"]["miri_rc"] == 0
    assert single_results["miri_mir2_opt0_explicit_preserve_ub"]["miri_rc"] == 0
    assert single_results["miri_mir2_opt1_ub_restored"]["miri_rc"] == 1
    assert single_results["miri_mir1_opt0_disable_rsm_ub_restored"]["miri_rc"] == 1
    assert single_results["miri_mir2_opt0_disable_rsm_ub_restored"]["miri_rc"] == 1
    assert loop_results["no_overwrite_mir0_opt0"]["miri_rc"] == 1
    assert loop_results["no_overwrite_mir2_opt0_ub_erased"]["miri_rc"] == 0
    assert loop_results["no_overwrite_mir2_opt0_ub_erased"]["stdout"] == "observed=10"
    assert loop_results["no_overwrite_mir2_opt1_ub_restored"]["miri_rc"] == 1
    assert loop_results["overwrite_mir0_opt0"]["miri_rc"] == 1
    assert loop_results["overwrite_mir2_opt0_no_sb_alias_11"]["miri_rc"] == 0
    assert loop_results["overwrite_mir2_opt0_no_sb_alias_11"]["stdout"] == "observed=11"

    return {
        "single_scope_matrix": single_results,
        "loop_cross_iteration_alias": loop_results,
        "rustc_rsm_mir_dumps": mir_dumps,
    }


def run_part_b(tmp_root: Path, replacements: list[tuple[str, str]]) -> dict:
    spec_rs = tmp_root / "pass_specimens.rs"
    spec_rs.write_text(
        """
#![crate_type = "lib"]
#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;

#[derive(Copy, Clone)]
pub enum E3 { A, B, C }

// --- 1. SsaRangePropagation specimens ---
#[inline(never)]
pub fn ssa_docstring_example(a: u32) -> (bool, bool) {
    let b = a < 9;
    if b {
        let c = b;
        let d = a < 8;
        (c, d)
    } else {
        (false, false)
    }
}

#[inline(never)]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn ssa_assume_mir(flag: bool) -> bool {
    mir! {
        {
            Assume(flag);
            Goto(bb1)
        }
        bb1 = {
            RET = flag;
            Return()
        }
    }
}

#[inline(never)]
pub fn ssa_bool_otherwise(b: bool) -> bool {
    match b {
        false => false,
        _ => b,
    }
}

#[inline(never)]
pub fn ssa_switch_u32_singleton(x: u32) -> u32 {
    match x {
        7 => x,
        _ => 0,
    }
}

#[inline(never)]
pub fn ssa_switch_14_arms_lt16(x: u32) -> u32 {
    match x {
        0 => x + 1,
        1 => x + 2,
        2 => x + 3,
        3 => x + 4,
        4 => x + 5,
        5 => x + 6,
        6 => x + 7,
        7 => x + 8,
        8 => x + 9,
        9 => x + 10,
        10 => x + 11,
        11 => x + 12,
        12 => x + 13,
        13 => x + 14,
        _ => x,
    }
}

#[inline(never)]
pub fn ssa_switch_15_arms_eq16(x: u32) -> u32 {
    match x {
        0 => x + 1,
        1 => x + 2,
        2 => x + 3,
        3 => x + 4,
        4 => x + 5,
        5 => x + 6,
        6 => x + 7,
        7 => x + 8,
        8 => x + 9,
        9 => x + 10,
        10 => x + 11,
        11 => x + 12,
        12 => x + 13,
        13 => x + 14,
        14 => x + 15,
        _ => x,
    }
}

#[inline(never)]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn ssa_multi_pred_join(x: u32) -> u32 {
    mir! {
        let tmp: u32;
        {
            match x {
                7 => bb2,
                _ => bb1,
            }
        }
        bb1 = {
            tmp = x + 1;
            Goto(bb2)
        }
        bb2 = {
            RET = x;
            Return()
        }
    }
}

// --- 2. SimplifyComparisonIntegral specimens ---
#[inline(never)]
pub fn make_u32(z: u32) -> u32 { z.wrapping_mul(3) }

#[inline(never)]
pub fn sci_move_retained_assign(z: u32) -> (u32, bool) {
    let eq = make_u32(z) == 43;
    let out = if eq { 10 } else { 20 };
    (out, eq)
}

#[inline(never)]
pub fn sci_ne_swap(z: u32) -> (u32, bool) {
    let ne = make_u32(z) != 43;
    let out = if ne { 10 } else { 20 };
    (out, ne)
}

#[inline(never)]
pub fn sci_move_dead_stmt(z: u32) -> u32 {
    if make_u32(z) == 43 { 10 } else { 20 }
}

// --- 3. EarlyOtherwiseBranch specimens ---
#[inline(never)]
pub fn eob_opt2_docstring(x: Option<()>, y: Option<()>) -> u32 {
    match (x, y) {
        (Some(_), Some(_)) => 0,
        (None, None) => 2,
        _ => 1,
    }
}

#[inline(never)]
pub fn eob_e3_two_arms(x: E3, y: E3) -> u32 {
    match (x, y) {
        (E3::A, E3::A) => 2,
        (E3::B, E3::B) => 1,
        _ => 0,
    }
}

#[inline(never)]
pub fn eob_e3_three_arms(x: E3, y: E3) -> u32 {
    match (x, y) {
        (E3::A, E3::A) => 2,
        (E3::B, E3::B) => 1,
        (E3::C, E3::C) => 3,
        _ => 0,
    }
}

#[inline(never)]
pub fn eob_u32_two_arms(x: u32, y: u32) -> u32 {
    match (x, y) {
        (0, 0) => 2,
        (1, 1) => 1,
        _ => 0,
    }
}

// --- 4. Subtyper specimens ---
#[inline(never)]
pub fn subtyper_hrtb(f: for<'a> fn(&'a u8)) -> fn(&'static u8) {
    f
}

#[inline(never)]
pub fn subtyper_covariant_ref<'a>(r: &'static u8) -> &'a u8 {
    r
}
""".lstrip(),
        encoding="utf-8",
    )

    env_base = dict(os.environ)
    dd_opt0 = tmp_root / "spec_dumps_opt0"
    dd_opt1 = tmp_root / "spec_dumps_opt1"
    dd_noueb = tmp_root / "spec_dumps_noueb"
    for d, extra in [
        (dd_opt0, ["-Zmir-opt-level=2", "-Copt-level=0"]),
        (dd_opt1, ["-Zmir-opt-level=2", "-Copt-level=1"]),
        (
            dd_noueb,
            ["-Zmir-opt-level=2", "-Copt-level=0", "-Zmir-enable-passes=-UnreachableEnumBranching"],
        ),
    ]:
        d.mkdir(parents=True, exist_ok=True)
        res = run_cmd(
            [
                "rustc",
                "--edition=2021",
                str(spec_rs),
                "-Zdump-mir=Subtyper|RemoveStorageMarkers|UnreachableEnumBranching|SsaRangePropagation|EarlyOtherwiseBranch|SimplifyComparisonIntegral",
                f"-Zdump-mir-dir={d}",
                "--emit=llvm-ir",
                "-o",
                str(tmp_root / f"spec_{d.name}.ll"),
            ]
            + extra,
            cwd=tmp_root,
            env=env_base,
        )
        assert res["returncode"] == 0, res["stderr"]

    def read_pair(dd: Path, fn_name: str, pass_name: str) -> dict:
        bef = find_mir(dd, fn_name, pass_name, "before")
        aft = find_mir(dd, fn_name, pass_name, "after")
        bt = bef.read_text("utf-8") if bef else ""
        at = aft.read_text("utf-8") if aft else ""
        b_body = "\n".join(bt.splitlines()[1:])
        a_body = "\n".join(at.splitlines()[1:])
        return {
            "before_file": bef.name if bef else None,
            "after_file": aft.name if aft else None,
            "changed": bool(bef and aft and b_body != a_body),
            "before_mir": scrub_text(bt, replacements),
            "after_mir": scrub_text(at, replacements),
        }

    # Check docstring runtime behavior at a = 8
    doc_bin_src = tmp_root / "doc_a8.rs"
    doc_bin_src.write_text(
        """
fn ssa_docstring_example(a: u32) -> (bool, bool) {
    let b = a < 9;
    if b {
        let c = b;
        let d = a < 8;
        (c, d)
    } else {
        (false, false)
    }
}
fn main() {
    let r = ssa_docstring_example(8);
    assert_eq!(r, (true, false));
    println!("a=8 -> c={}, d={}", r.0, r.1);
}
""".lstrip(),
        encoding="utf-8",
    )
    doc_bin = tmp_root / "doc_a8_bin"
    run_cmd(["rustc", "--edition=2021", "-O", str(doc_bin_src), "-o", str(doc_bin)], env=env_base)
    doc_exec = run_cmd([str(doc_bin)], env=env_base)
    assert doc_exec["returncode"] == 0

    ssa_doc = read_pair(dd_opt0, "ssa_docstring_example", "SsaRangePropagation")
    ssa_assume = read_pair(dd_opt0, "ssa_assume_mir", "SsaRangePropagation")
    ssa_bool_oth = read_pair(dd_opt0, "ssa_bool_otherwise", "SsaRangePropagation")
    ssa_u32_single = read_pair(dd_opt0, "ssa_switch_u32_singleton", "SsaRangePropagation")
    ssa_14 = read_pair(dd_opt0, "ssa_switch_14_arms_lt16", "SsaRangePropagation")
    ssa_15 = read_pair(dd_opt0, "ssa_switch_15_arms_eq16", "SsaRangePropagation")
    ssa_join = read_pair(dd_opt0, "ssa_multi_pred_join", "SsaRangePropagation")

    sci_ret = read_pair(dd_opt0, "sci_move_retained_assign", "SimplifyComparisonIntegral")
    sci_ne = read_pair(dd_opt0, "sci_ne_swap", "SimplifyComparisonIntegral")
    sci_dead_opt0 = read_pair(dd_opt0, "sci_move_dead_stmt", "SimplifyComparisonIntegral")
    sci_dead_opt1 = read_pair(dd_opt1, "sci_move_dead_stmt", "SimplifyComparisonIntegral")

    eob_opt2_def = read_pair(dd_opt0, "eob_opt2_docstring", "EarlyOtherwiseBranch")
    eob_opt2_noueb = read_pair(dd_noueb, "eob_opt2_docstring", "EarlyOtherwiseBranch")
    eob_e3_two = read_pair(dd_opt0, "eob_e3_two_arms", "EarlyOtherwiseBranch")
    eob_e3_three = read_pair(dd_opt0, "eob_e3_three_arms", "EarlyOtherwiseBranch")
    eob_u32_two = read_pair(dd_opt0, "eob_u32_two_arms", "EarlyOtherwiseBranch")

    sub_hrtb = read_pair(dd_opt0, "subtyper_hrtb", "Subtyper")
    sub_cov = read_pair(dd_opt0, "subtyper_covariant_ref", "Subtyper")

    # Machine-verified assertions over MIR transformations
    assert ssa_doc["changed"]
    assert "const true" in ssa_doc["after_mir"]
    assert "Lt(copy _1, const 8_u32)" in ssa_doc["after_mir"]
    assert ssa_assume["changed"] and "const true" in ssa_assume["after_mir"]
    assert ssa_bool_oth["changed"] and "const true" in ssa_bool_oth["after_mir"]
    assert ssa_u32_single["changed"] and "const 7_u32" in ssa_u32_single["after_mir"]
    assert ssa_14["changed"] and not ssa_15["changed"]
    assert not ssa_join["changed"]

    assert sci_ret["changed"]
    assert "Eq(move _3, const 43_u32)" in sci_ret["before_mir"]
    assert "Eq(copy _3, const 43_u32)" in sci_ret["after_mir"]
    assert "switchInt(copy _3) -> [43:" in sci_ret["after_mir"]
    assert sci_ne["changed"] and "Ne(copy _3, const 43_u32)" in sci_ne["after_mir"]
    assert sci_dead_opt0["changed"] and "nop;" in sci_dead_opt0["after_mir"]

    assert not eob_opt2_def["changed"]
    assert not eob_opt2_noueb["changed"]
    assert not eob_e3_two["changed"]
    assert eob_e3_three["changed"] and "Ne(copy _6, move _7)" in eob_e3_three["after_mir"]
    assert eob_u32_two["changed"] and "Ne(copy" in eob_u32_two["after_mir"]

    assert sub_hrtb["changed"] and "(Subtype)" in sub_hrtb["after_mir"]
    assert not sub_cov["changed"] and "(Subtype)" not in sub_cov["after_mir"]

    return {
        "ssa_range_propagation": {
            "ssa_docstring_example": {
                **ssa_doc,
                "native_at_a_eq_8": doc_exec["stdout"].strip(),
            },
            "ssa_assume_mir": ssa_assume,
            "ssa_bool_otherwise": ssa_bool_oth,
            "ssa_switch_u32_singleton": ssa_u32_single,
            "ssa_switch_14_arms_lt16": ssa_14,
            "ssa_switch_15_arms_eq16": ssa_15,
            "ssa_multi_pred_join": ssa_join,
        },
        "simplify_comparison_integral": {
            "sci_move_retained_assign": sci_ret,
            "sci_ne_swap": sci_ne,
            "sci_move_dead_stmt_opt0": sci_dead_opt0,
            "sci_move_dead_stmt_opt1": sci_dead_opt1,
        },
        "early_otherwise_branch": {
            "eob_opt2_docstring_default": eob_opt2_def,
            "eob_opt2_docstring_no_unreachable_enum_branching": eob_opt2_noueb,
            "eob_e3_two_arms": eob_e3_two,
            "eob_e3_three_arms": eob_e3_three,
            "eob_u32_two_arms": eob_u32_two,
        },
        "subtyper": {
            "subtyper_hrtb": sub_hrtb,
            "subtyper_covariant_ref": sub_cov,
        },
    }


def summarize_zerocopy_dump_dir(dd: Path) -> dict:
    passes = {}
    pass_key_map: dict[str, tuple[str, str]] = {}
    for f in sorted(dd.glob("*.mir")):
        parts = f.name.split(".")
        stage = parts[-2]
        if stage not in ("before", "after"):
            continue
        pname = f"{parts[-4]}.{parts[-3]}"
        pass_key_map[pname] = (parts[-4], parts[-3])
        m = count_mir_metrics(f.read_text("utf-8", errors="replace"))
        entry = passes.setdefault(
            pname,
            {
                "before": {k: 0 for k in m},
                "after": {k: 0 for k in m},
            },
        )
        for k, v in m.items():
            entry[stage][k] += v

    out = {}
    for pname, data in sorted(passes.items()):
        delta = {k: data["after"][k] - data["before"][k] for k in data["before"]}
        changed_bodies = []
        for bf in sorted(dd.glob(f"*.{pname}.before.mir")):
            af = dd / bf.name.replace(".before.mir", ".after.mir")
            if af.exists():
                bt = "\n".join(bf.read_text("utf-8", errors="replace").splitlines()[1:])
                at = "\n".join(af.read_text("utf-8", errors="replace").splitlines()[1:])
                if bt != at:
                    changed_bodies.append(bf.name.split(f".{pname}.")[0])
        out[pname] = {
            "before": data["before"],
            "after": data["after"],
            "delta": delta,
            "changed_bodies_count": len(changed_bodies),
            "sample_changed_bodies": changed_bodies[:12],
        }
    return out


def run_part_c_zerocopy(zerocopy_dir: Path, tmp_root: Path, replacements: list[tuple[str, str]]) -> dict:
    env_base = dict(os.environ)
    modes = {}
    for mode_name, extra in [
        ("opt0_mir2", ["-Zmir-opt-level=2", "-Copt-level=0"]),
        ("opt1_mir2", ["-Zmir-opt-level=2", "-Copt-level=1"]),
    ]:
        tdir = tmp_root / f"zc_target_{mode_name}"
        dd = tmp_root / f"zc_dumps_{mode_name}"
        dd.mkdir(parents=True, exist_ok=True)
        env = dict(env_base, CARGO_TARGET_DIR=str(tdir))
        print(f"[zerocopy] running {mode_name}...", file=sys.stderr, flush=True)
        res = run_cmd(
            [
                "cargo",
                "rustc",
                "--lib",
                "--quiet",
                "--",
                "-Zdump-mir=Subtyper|RemoveStorageMarkers|SsaRangePropagation|EarlyOtherwiseBranch|SimplifyComparisonIntegral",
                f"-Zdump-mir-dir={dd}",
                "--emit=metadata",
            ]
            + extra,
            cwd=zerocopy_dir,
            env=env,
            timeout=300,
        )
        assert res["returncode"] == 0, scrub_text(res["stderr"], replacements)
        modes[mode_name] = {
            "flags": extra,
            "passes": summarize_zerocopy_dump_dir(dd),
        }
        shutil.rmtree(dd, ignore_errors=True)
        shutil.rmtree(tdir, ignore_errors=True)

    # Also capture the exact 1.102.0-nightly (3ef0c22cd) reference baseline counts
    baseline_1_102 = {
        "rustc_commit": "3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1",
        "rustc_version": "rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)",
        "opt0_mir2_passes": {
            "2-2-003.Subtyper": {
                "before": {"bodies": 4663, "bbs": 14352, "assigns": 20330, "switchints": 1072, "returns": 4636, "subtype_casts": 0, "storage_markers": 30392},
                "after": {"bodies": 4663, "bbs": 14352, "assigns": 20330, "switchints": 1072, "returns": 4636, "subtype_casts": 0, "storage_markers": 30392},
                "delta": {"bodies": 0, "bbs": 0, "assigns": 0, "switchints": 0, "returns": 0, "subtype_casts": 0, "storage_markers": 0},
            },
            "opt0_mir2.RemoveStorageMarkers": {
                "before": {"bodies": 4302, "bbs": 12288, "assigns": 17670, "switchints": 997, "returns": 4277, "subtype_casts": 0, "storage_markers": 25716},
                "after": {"bodies": 4302, "bbs": 12288, "assigns": 17670, "switchints": 997, "returns": 4277, "subtype_casts": 0, "storage_markers": 0},
                "delta": {"bodies": 0, "bbs": 0, "assigns": 0, "switchints": 0, "returns": 0, "subtype_casts": 0, "storage_markers": -25716},
            },
            "3-2-018.SsaRangePropagation": {
                "before": {"bodies": 4302, "bbs": 13853, "assigns": 27176, "switchints": 1889, "returns": 4277, "subtype_casts": 0, "storage_markers": 39369},
                "after": {"bodies": 4302, "bbs": 13853, "assigns": 27176, "switchints": 1889, "returns": 4277, "subtype_casts": 0, "storage_markers": 39369},
                "delta": {"bodies": 0, "bbs": 0, "assigns": 0, "switchints": 0, "returns": 0, "subtype_casts": 0, "storage_markers": 0},
            },
            "3-2-023.EarlyOtherwiseBranch": {
                "before": {"bodies": 4302, "bbs": 14083, "assigns": 26426, "switchints": 1865, "returns": 4277, "subtype_casts": 0, "storage_markers": 40127},
                "after": {"bodies": 4302, "bbs": 14083, "assigns": 26426, "switchints": 1865, "returns": 4277, "subtype_casts": 0, "storage_markers": 40127},
                "delta": {"bodies": 0, "bbs": 0, "assigns": 0, "switchints": 0, "returns": 0, "subtype_casts": 0, "storage_markers": 0},
            },
            "3-2-024.SimplifyComparisonIntegral": {
                "before": {"bodies": 4302, "bbs": 14083, "assigns": 26426, "switchints": 1865, "returns": 4277, "subtype_casts": 0, "storage_markers": 40127},
                "after": {"bodies": 4302, "bbs": 14083, "assigns": 26426, "switchints": 1865, "returns": 4277, "subtype_casts": 0, "storage_markers": 40127},
                "delta": {"bodies": 0, "bbs": 0, "assigns": 0, "switchints": 0, "returns": 0, "subtype_casts": 0, "storage_markers": 0},
            },
        },
    }

    return {
        "live_installed_toolchain": modes,
        "historical_baseline_1_102_0_nightly": baseline_1_102,
    }


def main() -> int:
    ensure_cargo_on_path()
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--zerocopy-dir", default="", help="Path to zerocopy crate directory (containing Cargo.toml)")
    ap.add_argument("--out", default=str(HERE / "probe_results.json"))
    args = ap.parse_args()

    rustc_ver = run_cmd(["rustc", "-Vv"])["stdout"].strip()
    miri_ver = run_cmd(["cargo", "miri", "--version"])["stdout"].strip()

    with tempfile.TemporaryDirectory(prefix="rsm_range_probe_") as tmp:
        tmp_root = Path(tmp)
        replacements = [(str(tmp_root), "$TMP_PROBE")]
        if args.zerocopy_dir:
            zc_path = Path(args.zerocopy_dir).resolve()
            replacements.append((str(zc_path), "$ZEROCOPY_DIR"))
        else:
            zc_path = None

        part_a = run_part_a(tmp_root, replacements)
        part_b = run_part_b(tmp_root, replacements)
        part_c = run_part_c_zerocopy(zc_path, tmp_root, replacements) if zc_path else None

    result = {
        "schema": "rsm-range-switch-probe/1",
        "generated_on": datetime.date.today().isoformat(),
        "rustc_version": rustc_ver,
        "miri_version": miri_ver,
        "part_a_remove_storage_markers_miri_paradox": part_a,
        "part_b_pass_specimens": part_b,
        "part_c_zerocopy_census": part_c,
    }

    out_path = Path(args.out)
    out_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} ({out_path.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
