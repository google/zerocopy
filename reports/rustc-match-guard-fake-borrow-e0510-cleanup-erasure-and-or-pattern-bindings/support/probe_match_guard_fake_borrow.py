#!/usr/bin/env python3
"""Reproducible live rustc probes for match-guard FakeBorrow, E0510/E0506/E0594,
CleanupPostBorrowck erasure, interior mutability, and or-pattern guard bindings.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path


def sanitize_text(text: str, *roots: str) -> str:
    for root in roots:
        if root:
            text = text.replace(root + os.sep, "")
            text = text.replace(root, "<tmp>")
    return text


def run_rustc(
    src: str,
    tmpdir: str,
    *,
    edition: str = "2024",
    crate_type: str = "lib",
    extra_args: list[str] | None = None,
    run_binary: bool = False,
    dump_mir_fn: str | None = None,
) -> dict:
    with tempfile.TemporaryDirectory(dir=tmpdir) as work:
        src_path = Path(work) / "probe.rs"
        src_path.write_text(src, encoding="utf-8")
        out_path = Path(work) / ("probe_bin" if crate_type == "bin" else "libprobe.rlib")
        mir_dir = Path(work) / "mir_dump"
        cmd = [
            "rustc",
            f"--edition={edition}",
            f"--crate-type={crate_type}",
            "-o",
            str(out_path),
            str(src_path),
        ]
        if dump_mir_fn is not None:
            mir_dir.mkdir(parents=True, exist_ok=True)
            cmd.extend(
                [
                    f"-Zdump-mir={dump_mir_fn}",
                    f"-Zdump-mir-dir={mir_dir}",
                ]
            )
        if extra_args:
            cmd.extend(extra_args)

        comp = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        rec: dict = {
            "edition": edition,
            "crate_type": crate_type,
            "extra_args": list(extra_args or []),
            "source": src,
            "compile_returncode": comp.returncode,
            "compile_stdout": sanitize_text(comp.stdout, work, tmpdir),
            "compile_stderr": sanitize_text(comp.stderr, work, tmpdir),
        }

        if dump_mir_fn is not None and mir_dir.exists():
            stages: dict[str, str] = {}
            for p in sorted(mir_dir.iterdir()):
                if p.is_file() and p.name.endswith(".mir"):
                    if (
                        ".built.after.mir" in p.name
                        or ".CleanupPostBorrowck.after.mir" in p.name
                        or ".CleanupPostBorrowck.before.mir" in p.name
                        or ".runtime-optimized.after.mir" in p.name
                    ):
                        stages[p.name] = sanitize_text(p.read_text(encoding="utf-8"), work, tmpdir)
            rec["mir_pass_files"] = sorted(p.name for p in mir_dir.iterdir() if p.is_file())
            rec["stages"] = stages

        if run_binary and comp.returncode == 0 and out_path.exists():
            run = subprocess.run([str(out_path)], capture_output=True, text=True, timeout=30)
            rec["run_returncode"] = run.returncode
            rec["run_stdout"] = run.stdout
            rec["run_stderr"] = run.stderr

        return rec


def main() -> int:
    ver_proc = subprocess.run(["rustc", "-Vv"], capture_output=True, text=True, check=True)
    rustc_vv = ver_proc.stdout.strip()
    m_sha = re.search(r"^commit-hash:\s*([0-9a-f]{40})", rustc_vv, re.MULTILINE)
    commit_hash = m_sha.group(1) if m_sha else ""

    with tempfile.TemporaryDirectory() as tmpdir:
        a_experiments = {
            "wildcard_scrutinee_mutation_rejected_e0510": run_rustc(
                """pub fn probe() {
    let mut x = Some(10u32);
    match x {
        Some(_) if {
            x = None;
            true
        } => {}
        _ => {}
    }
}
""",
                tmpdir,
            ),
            "binding_scrutinee_mutation_rejected_e0506": run_rustc(
                """pub fn probe() {
    let mut x = Some(10u32);
    match x {
        Some(_y) if {
            x = None;
            true
        } => {}
        _ => {}
    }
}
""",
                tmpdir,
            ),
            "shallow_fake_borrow_allows_disjoint_payload_mutation": run_rustc(
                """pub fn probe() {
    let mut x = (Some(0u32), true);
    match x {
        (Some(_), false) => {}
        _ if {
            if let Some(ref mut y) = x.0 {
                *y += 1;
            }
            true
        } => {}
        _ => {}
    }
}
""",
                tmpdir,
            ),
            "shallow_fake_borrow_rejects_field_tag_overwrite_e0510": run_rustc(
                """pub fn probe() {
    let mut x = (Some(0u32), true);
    match x {
        (Some(_), false) => {}
        _ if {
            x.0 = None;
            true
        } => {}
        _ => {}
    }
}
""",
                tmpdir,
            ),
            "tested_subpattern_payload_shallow_fake_borrow_rejects_payload_mut_e0510": run_rustc(
                """pub fn probe() {
    let mut x = (Some(0u32), true);
    match x {
        (Some(0), false) => {}
        _ if {
            if let Some(ref mut y) = x.0 {
                *y += 1;
            }
            true
        } => {}
        _ => {}
    }
}
""",
                tmpdir,
            ),
            "box_deref_pattern_shallow_fake_borrow_rejects_pointee_mut_e0510": run_rustc(
                """#![feature(deref_patterns)]
pub fn probe() {
    let mut b = Box::new(false);
    match b {
        deref!(true) => {}
        _ if {
            *b = true;
            false
        } => {}
        deref!(false) => {}
    }
}
""",
                tmpdir,
            ),
            "vec_deref_pattern_deep_fake_borrow_rejects_elem_mut_e0502": run_rustc(
                """#![feature(deref_patterns)]
pub fn probe(mut v: Vec<u32>) -> u32 {
    match v {
        deref!([1, ..]) => 1,
        _ if {
            v[0] = 9;
            false
        } => 2,
        _ => 3,
    }
}
""",
                tmpdir,
            ),
            "vec_deref_pattern_deep_fake_borrow_rejects_scrutinee_assign_e0510": run_rustc(
                """#![feature(deref_patterns)]
pub fn probe(mut v: Vec<u32>) -> u32 {
    match v {
        deref!([1, ..]) => 1,
        _ if {
            v = Vec::new();
            false
        } => 2,
        _ => 3,
    }
}
""",
                tmpdir,
            ),
            "binding_behind_deref_prefix_shallow_fake_borrow_e0510": run_rustc(
                """pub fn probe() -> u32 {
    let mut x = &1u32;
    match *x {
        y if {
            y == 1 && {
                x = &2;
                false
            }
        } => y,
        _ => 3,
    }
}
""",
                tmpdir,
            ),
            "irrefutable_local_binding_without_deref_allows_mutation": run_rustc(
                """pub fn probe() {
    let mut u = false;
    match u {
        _ if {
            u = true;
            false
        } => {}
        _x => {}
    }
}
""",
                tmpdir,
            ),
            "mir_built_vs_cleanup_post_borrowck": run_rustc(
                """pub fn guard_probe(x: Option<u32>) -> u32 {
    match x {
        Some(v) if v > 5 => v,
        _ => 0,
    }
}
""",
                tmpdir,
                dump_mir_fn="guard_probe",
            ),
            "mir_box_deref_pattern_built_vs_cleanup": run_rustc(
                """#![feature(deref_patterns)]
pub fn deref_guard_probe(b: Box<bool>) -> u32 {
    match b {
        deref!(true) => 1,
        _ if false => 2,
        deref!(false) => 3,
    }
}
""",
                tmpdir,
                dump_mir_fn="deref_guard_probe",
            ),
            "mir_vec_deref_pattern_deep_fake_borrow_built_vs_cleanup": run_rustc(
                """#![feature(deref_patterns)]
pub fn vec_deref_guard_probe(v: Vec<u32>) -> u32 {
    match v {
        deref!([1, ..]) => 1,
        _ if false => 2,
        _ => 3,
    }
}
""",
                tmpdir,
                dump_mir_fn="vec_deref_guard_probe",
            ),
            "mir_uninhabited_exhaustive_fake_read_for_matched_place": run_rustc(
                """pub enum Void {}
pub fn uninhabited_probe(v: Void) -> u32 {
    match v {}
}
""",
                tmpdir,
                dump_mir_fn="uninhabited_probe",
            ),
            "mir_or_pattern_guard_built_vs_cleanup": run_rustc(
                """pub enum Two {
    A(String),
    B(String),
}
pub fn or_guard_probe(t: Two, gate: &mut u32) -> String {
    match t {
        Two::A(s) | Two::B(s) if {
            *gate += 1;
            s.len() > 2
        } => s,
        _ => String::from("fallback"),
    }
}
""",
                tmpdir,
                dump_mir_fn="or_guard_probe",
            ),
        }

        b_experiments = {
            "mut_scrutinee_write_to_ref_mut_binding_in_guard_rejected_e0594": run_rustc(
                """pub fn probe(mut x: Option<Box<u32>>) {
    match x {
        Some(ref mut v) if {
            *v = Box::new(99);
            true
        } => {
            let _ = v;
        }
        _ => {}
    }
}
""",
                tmpdir,
            ),
            "mut_by_val_binding_write_in_guard_rejected_e0594": run_rustc(
                """pub fn probe(x: Option<Box<u32>>) -> Box<u32> {
    match x {
        Some(mut v) if {
            v = Box::new(99);
            let _ = &v;
            true
        } => v,
        _ => Box::new(0),
    }
}
""",
                tmpdir,
            ),
            "cell_interior_mut_and_mut_arm_body_ok": run_rustc(
                """use std::cell::Cell;

struct CellMatched {
    flag: bool,
    cell: Cell<u32>,
}

fn main() {
    let cell = Cell::new(Some(Box::new(10u32)));
    let guard_seen = match cell.take() {
        Some(v) if {
            cell.set(Some(Box::new(17u32)));
            *v == 10
        } => {
            let mut inner = 0u32;
            if let Some(after) = cell.take() {
                inner = *after;
            }
            inner
        }
        _ => 0,
    };

    let s = CellMatched { flag: true, cell: Cell::new(5) };
    let interior_via_ref = match s {
        CellMatched { flag: true, ref cell } if {
            cell.set(cell.get() + 12);
            cell.get() == 17
        } => cell.get(),
        _ => 0,
    };

    let mut opt = Some(Box::new(10u32));
    let body_mut = match opt {
        Some(ref mut v) if **v > 5 => {
            *v = Box::new(99u32);
            **v
        }
        _ => 0,
    };

    println!(
        "CELL_GUARD_VAL={} INTERIOR_REF_VAL={} MUT_BODY_OK={}",
        guard_seen, interior_via_ref, body_mut
    );
}
""",
                tmpdir,
                crate_type="bin",
                run_binary=True,
            ),
            "cell_interior_mut_fallthrough_observed": run_rustc(
                """use std::cell::Cell;

struct MatchedCellField {
    tag: bool,
    c: Cell<u32>,
}

fn main() {
    let s = MatchedCellField { tag: true, c: Cell::new(5) };
    let out = match s {
        MatchedCellField { tag: true, .. } if {
            s.c.set(17);
            false
        } => 0,
        MatchedCellField { tag: true, .. } => s.c.get(),
        _ => 1,
    };
    println!("INTERIOR_MUT_ACROSS_FALLTHROUGH={}", out);
}
""",
                tmpdir,
                crate_type="bin",
                run_binary=True,
            ),
            "or_pattern_guard_per_subbranch_and_move_after_ref_within_guard": run_rustc(
                """enum PairStr {
    Left(String),
    Right(String),
}

fn check_once(s: &str, ctr: &mut u32) -> bool {
    *ctr += 1;
    s == "hi"
}

fn main() {
    let mut once_ctr = 0u32;
    let moved = match PairStr::Right(String::from("hi")) {
        PairStr::Left(s) | PairStr::Right(s) if check_once(&s, &mut once_ctr) => s,
        _ => String::from("miss"),
    };

    let mut sub_ctr = 0u32;
    let picked = match (Some(1u32), Some(2u32)) {
        (Some(x), _) | (_, Some(x)) if {
            sub_ctr += 1;
            x > 1
        } => x,
        _ => 0,
    };

    let mut short_ctr = 0u32;
    let short_val = match (Some(10u32), Some(20u32)) {
        (Some(x), _) | (_, Some(x)) if {
            short_ctr += 1;
            x > 5
        } => x,
        _ => 0,
    };

    let mut miss_ctr = 0u32;
    let miss_val = match (Some(1u32), Some(1u32)) {
        (Some(x), _) | (_, Some(x)) if {
            miss_ctr += 1;
            x > 5
        } => x,
        _ => 99,
    };

    println!(
        "OR_CHECKS_ONCE={} OR_MOVE_OUT={} OR_SUBBRANCH_CHECKS={} PICKED={} SHORT_CHECKS={} SHORT_VAL={} MISS_CHECKS={} MISS_VAL={} RES=ok",
        once_ctr, moved, sub_ctr, picked, short_ctr, short_val, miss_ctr, miss_val
    );
}
""",
                tmpdir,
                crate_type="bin",
                run_binary=True,
            ),
        }

        payload = {
            "rustc_version": rustc_vv,
            "rustc_commit_hash": commit_hash,
            "experiments": {
                "a_fake_borrow_e0510_vs_e0506_and_mir_cleanup": a_experiments,
                "b_cell_interior_mutability_ref_within_guard_and_or_patterns": b_experiments,
            },
        }

    out_file = Path(__file__).resolve().parent / "probe_results.json"
    out_file.write_text(json.dumps(payload, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print(f"Wrote {out_file} ({out_file.stat().st_size} bytes)")
    for grp, cases in payload["experiments"].items():
        for name, res in cases.items():
            rc = res.get("compile_returncode")
            rrc = res.get("run_returncode")
            extra = f" run_rc={rrc} stdout={res.get('run_stdout', '').strip()!r}" if rrc is not None else ""
            err_head = res.get("compile_stderr", "").splitlines()[0] if res.get("compile_stderr") else ""
            print(f"  [{grp}] {name}: compile_rc={rc}{extra} {err_head}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
