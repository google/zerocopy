#!/usr/bin/env python3
"""Live rustc verification probe for MIR drop elaboration, dynamic drop flags,
partial moves (vs. E0509), ManuallyDrop/MaybeUninit suppression, and drop order.
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


def find_rustc() -> str:
    env_rustc = os.environ.get("RUSTC")
    if env_rustc and os.path.isfile(env_rustc):
        return env_rustc
    which_rustc = shutil.which("rustc")
    if which_rustc:
        return which_rustc
    cargo_rustc = os.path.expanduser("~/.cargo/bin/rustc")
    if os.path.isfile(cargo_rustc):
        return cargo_rustc
    raise RuntimeError("rustc executable not found in RUSTC, PATH, or ~/.cargo/bin/rustc")


def sanitize_text(text: str, tmpdir: str) -> str:
    text = text.replace(tmpdir, "<tmp>")
    # Normalize any user home prefix if rustc embeds it in paths.
    home = os.path.expanduser("~")
    if home and home != "/":
        text = text.replace(home, "<home>")
    return text


def run_compile_and_exec(
    rustc: str,
    code: str,
    edition: str = "2024",
    extra_args: list[str] | None = None,
    dump_mir_funcs: list[str] | None = None,
) -> dict:
    extra_args = list(extra_args or [])
    with tempfile.TemporaryDirectory() as tmpdir:
        src_path = os.path.join(tmpdir, "probe.rs")
        bin_path = os.path.join(tmpdir, "probe")
        mir_dir = os.path.join(tmpdir, "mir_dump")
        with open(src_path, "w", encoding="utf-8") as fh:
            fh.write(code)

        cmd = [rustc, f"--edition={edition}", src_path, "-o", bin_path] + extra_args
        if dump_mir_funcs is not None:
            os.makedirs(mir_dir, exist_ok=True)
            cmd.extend(["-Zdump-mir=ElaborateDrops", f"-Zdump-mir-dir={mir_dir}"])

        comp = subprocess.run(cmd, capture_output=True, text=True, check=False)
        result: dict = {
            "edition": edition,
            "extra_args": extra_args,
            "compile_returncode": comp.returncode,
            "compile_stdout": sanitize_text(comp.stdout, tmpdir).strip(),
            "compile_stderr": sanitize_text(comp.stderr, tmpdir).strip(),
        }

        if comp.returncode == 0 and os.path.isfile(bin_path):
            run_proc = subprocess.run([bin_path], capture_output=True, text=True, check=False)
            result["run_returncode"] = run_proc.returncode
            result["run_stdout"] = sanitize_text(run_proc.stdout, tmpdir).strip()
            result["run_stderr"] = sanitize_text(run_proc.stderr, tmpdir).strip()

        if dump_mir_funcs is not None and os.path.isdir(mir_dir):
            mir_dumps: dict[str, str] = {}
            for fn in sorted(os.listdir(mir_dir)):
                if not fn.endswith(".mir"):
                    continue
                if any(f".{target}." in fn for target in dump_mir_funcs):
                    raw = Path(mir_dir, fn).read_text(encoding="utf-8")
                    mir_dumps[fn] = sanitize_text(raw, tmpdir).strip()
            result["mir_dumps"] = mir_dumps

        return result


PROBE_A_CODE = r"""
use std::cell::RefCell;
use std::mem::{ManuallyDrop, MaybeUninit, needs_drop};

struct Track<'a> {
    log: &'a RefCell<Vec<&'static str>>,
    label: &'static str,
}

impl Drop for Track<'_> {
    fn drop(&mut self) {
        self.log.borrow_mut().push(self.label);
    }
}

struct FieldsOrder<'a> {
    f1: Track<'a>,
    f2: Track<'a>,
    f3: Track<'a>,
}

enum EnumOrder<'a> {
    Two(Track<'a>, Track<'a>),
    #[allow(dead_code)]
    Empty,
}

#[allow(dead_code)]
struct NoDropPair {
    x: u32,
    y: bool,
}

#[inline(never)]
fn locals_order(log: &RefCell<Vec<&'static str>>) {
    let _a = Track { log, label: "a" };
    let _b = Track { log, label: "b" };
    let _c = Track { log, label: "c" };
}

#[inline(never)]
fn shadowing_and_nested_order(log: &RefCell<Vec<&'static str>>) {
    let _x = Track { log, label: "outer_x" };
    {
        let _inner = Track { log, label: "inner_scope" };
    }
    let _x = Track { log, label: "shadow_x" };
}

#[inline(never)]
fn struct_order(log: &RefCell<Vec<&'static str>>) {
    let _s = FieldsOrder {
        f1: Track { log, label: "f1" },
        f2: Track { log, label: "f2" },
        f3: Track { log, label: "f3" },
    };
}

#[inline(never)]
fn tuple_order(log: &RefCell<Vec<&'static str>>) {
    let _t = (
        Track { log, label: "t0" },
        Track { log, label: "t1" },
        Track { log, label: "t2" },
    );
}

#[inline(never)]
fn array_order(log: &RefCell<Vec<&'static str>>) {
    let _arr = [
        Track { log, label: "arr0" },
        Track { log, label: "arr1" },
        Track { log, label: "arr2" },
    ];
}

#[inline(never)]
fn enum_order(log: &RefCell<Vec<&'static str>>) {
    let _e = EnumOrder::Two(
        Track { log, label: "e0" },
        Track { log, label: "e1" },
    );
}

#[inline(never)]
fn drop_replace_order(log: &RefCell<Vec<&'static str>>) {
    let mut r = Track { log, label: "r_old" };
    r = Track { log, label: "r_new" };
    log.borrow_mut().push("after_assign");
    let _keep = &r;
}

#[inline(never)]
fn md_suppressed_probe(log: &RefCell<Vec<&'static str>>) {
    let _md = ManuallyDrop::new(Track { log, label: "md_suppressed" });
}

#[inline(never)]
fn md_explicit_probe(log: &RefCell<Vec<&'static str>>) {
    let mut md = ManuallyDrop::new(Track { log, label: "md_explicit" });
    unsafe {
        ManuallyDrop::drop(&mut md);
    }
    log.borrow_mut().push("after_explicit_drop");
}

fn main() {
    let run = |f: fn(&RefCell<Vec<&'static str>>)| -> Vec<&'static str> {
        let log = RefCell::new(Vec::new());
        f(&log);
        log.into_inner()
    };
    println!("LOCALS={:?}", run(locals_order));
    println!("SHADOW_NESTED={:?}", run(shadowing_and_nested_order));
    println!("STRUCT_FIELDS={:?}", run(struct_order));
    println!("TUPLE={:?}", run(tuple_order));
    println!("ARRAY={:?}", run(array_order));
    println!("ENUM_FIELDS={:?}", run(enum_order));
    println!("DROP_REPLACE={:?}", run(drop_replace_order));
    println!("MD_SUPPRESSED={:?}", run(md_suppressed_probe));
    println!("MD_EXPLICIT={:?}", run(md_explicit_probe));
    println!(
        "NEEDS_DROP track={} md={} mu={} arr0={} arr3={} tup={} nodrop={}",
        needs_drop::<Track<'static>>(),
        needs_drop::<ManuallyDrop<Track<'static>>>(),
        needs_drop::<MaybeUninit<Track<'static>>>(),
        needs_drop::<[Track<'static>; 0]>(),
        needs_drop::<[Track<'static>; 3]>(),
        needs_drop::<(u32, Track<'static>)>(),
        needs_drop::<NoDropPair>(),
    );
}
"""

PROBE_B_PARTIAL_CODE = r"""
use std::cell::RefCell;

struct Track<'a> {
    log: &'a RefCell<Vec<&'static str>>,
    label: &'static str,
}

impl Drop for Track<'_> {
    fn drop(&mut self) {
        self.log.borrow_mut().push(self.label);
    }
}

struct Pair<'a> {
    p0: Track<'a>,
    p1: Track<'a>,
}

#[inline(never)]
fn partial_move_probe(log: &RefCell<Vec<&'static str>>) {
    let pair = Pair {
        p0: Track { log, label: "p0" },
        p1: Track { log, label: "p1" },
    };
    let moved_p0 = pair.p0;
    log.borrow_mut().push("end_inner_fn");
    drop(moved_p0);
}

#[inline(never)]
fn partial_move_reinit_probe(log: &RefCell<Vec<&'static str>>) {
    let mut pair = Pair {
        p0: Track { log, label: "p0_orig" },
        p1: Track { log, label: "p1_orig" },
    };
    let moved_p0 = pair.p0;
    drop(moved_p0);
    pair.p0 = Track { log, label: "p0_reinit" };
    log.borrow_mut().push("end_reinit_fn");
}

#[inline(never)]
fn partial_move_box_deref_probe(log: &RefCell<Vec<&'static str>>) {
    let boxed = Box::new(Track { log, label: "boxed" });
    let unboxed = *boxed;
    log.borrow_mut().push("after_unbox");
    drop(unboxed);
    log.borrow_mut().push("after_unboxed_drop");
}

#[inline(never)]
fn partial_move_array_pattern_probe(log: &RefCell<Vec<&'static str>>) {
    let arr = [
        Track { log, label: "a0" },
        Track { log, label: "a1" },
        Track { log, label: "a2" },
    ];
    let [_, moved_mid, _] = arr;
    drop(moved_mid);
    log.borrow_mut().push("after_mid_drop");
}

fn main() {
    let run = |f: fn(&RefCell<Vec<&'static str>>)| -> Vec<&'static str> {
        let log = RefCell::new(Vec::new());
        f(&log);
        log.into_inner()
    };
    println!("PARTIAL_MOVE={:?}", run(partial_move_probe));
    println!("PARTIAL_MOVE_REINIT={:?}", run(partial_move_reinit_probe));
    println!("BOX_DEREF_MOVE={:?}", run(partial_move_box_deref_probe));
    println!("ARRAY_PATTERN_MOVE={:?}", run(partial_move_array_pattern_probe));
}
"""

PROBE_B_E0509_CODE = r"""
struct Inner(#[allow(dead_code)] u32);

struct OuterWithDrop {
    a: Inner,
    #[allow(dead_code)]
    b: Inner,
}

impl Drop for OuterWithDrop {
    fn drop(&mut self) {}
}

fn main() {
    let o = OuterWithDrop { a: Inner(1), b: Inner(2) };
    let _moved = o.a;
}
"""

PROBE_B_E0509_REINIT_CODE = r"""
struct Inner(#[allow(dead_code)] u32);

struct OuterWithDrop {
    a: Inner,
    #[allow(dead_code)]
    b: Inner,
}

impl Drop for OuterWithDrop {
    fn drop(&mut self) {}
}

fn main() {
    let mut o = OuterWithDrop { a: Inner(1), b: Inner(2) };
    o.a = Inner(3);
    let _ = o;
}
"""

PROBE_C_CODE = r"""
use std::cell::RefCell;
use std::mem::MaybeUninit;
use std::panic::{AssertUnwindSafe, catch_unwind};

struct Track<'a> {
    log: &'a RefCell<Vec<&'static str>>,
    label: &'static str,
    panic_on_drop: bool,
}

impl Drop for Track<'_> {
    fn drop(&mut self) {
        self.log.borrow_mut().push(self.label);
        if self.panic_on_drop {
            panic!("boom on {}", self.label);
        }
    }
}

struct Pair<'a> {
    p0: Track<'a>,
    p1: Track<'a>,
}

struct Triple<'a> {
    f1: Track<'a>,
    f2: Track<'a>,
    f3: Track<'a>,
}

#[inline(never)]
fn cond_init(cond: bool, log: &RefCell<Vec<&'static str>>) {
    let x: Track<'_>;
    if cond {
        x = Track { log, label: "dyn", panic_on_drop: false };
        let _ = &x;
    }
    log.borrow_mut().push("exit_scope");
}

#[inline(never)]
fn cond_move_and_reinit(do_move: bool, do_reinit: bool, log: &RefCell<Vec<&'static str>>) {
    let mut x = Track { log, label: "v1", panic_on_drop: false };
    if do_move {
        drop(x);
    }
    if do_reinit {
        x = Track { log, label: "v2", panic_on_drop: false };
        let _ = &x;
    }
}

#[inline(never)]
fn loop_cond_init(n: usize, log: &RefCell<Vec<&'static str>>) {
    let mut x: Track<'_>;
    for i in 0..n {
        if i % 2 == 0 {
            x = Track { log, label: "even", panic_on_drop: false };
            let _ = &x;
        }
    }
    log.borrow_mut().push("after_loop");
}

#[inline(never)]
fn unwind_partial_move(log: &RefCell<Vec<&'static str>>) {
    let pair = Pair {
        p0: Track { log, label: "p0", panic_on_drop: false },
        p1: Track { log, label: "p1", panic_on_drop: false },
    };
    let moved = pair.p0;
    drop(moved);
    log.borrow_mut().push("before_panic");
    panic!("unwind after partial move");
}

#[inline(never)]
fn unwind_field_ladder(log: &RefCell<Vec<&'static str>>) {
    let _t = Triple {
        f1: Track { log, label: "f1_panics", panic_on_drop: true },
        f2: Track { log, label: "f2", panic_on_drop: false },
        f3: Track { log, label: "f3", panic_on_drop: false },
    };
}

#[inline(never)]
fn mu_uninit_and_ignored(log: &RefCell<Vec<&'static str>>) {
    let _u: MaybeUninit<Track<'_>> = MaybeUninit::uninit();
    let _w = MaybeUninit::new(Track { log, label: "mu_ignored", panic_on_drop: false });
}

#[inline(never)]
fn mu_explicit(log: &RefCell<Vec<&'static str>>) {
    let mut mu = MaybeUninit::new(Track { log, label: "mu_explicit", panic_on_drop: false });
    unsafe {
        mu.assume_init_drop();
    }
    log.borrow_mut().push("after_mu_drop");
}

fn main() {
    let l1 = RefCell::new(Vec::new());
    cond_init(true, &l1);
    let l2 = RefCell::new(Vec::new());
    cond_init(false, &l2);

    let mut cmr = Vec::new();
    for &(m, r) in &[(false, false), (true, false), (true, true), (false, true)] {
        let l = RefCell::new(Vec::new());
        cond_move_and_reinit(m, r, &l);
        cmr.push(format!("({}, {})={:?}", m, r, l.into_inner()));
    }

    let l_loop = RefCell::new(Vec::new());
    loop_cond_init(3, &l_loop);

    let l_unw_pm = RefCell::new(Vec::new());
    let _ = catch_unwind(AssertUnwindSafe(|| unwind_partial_move(&l_unw_pm)));

    let l_unw_fld = RefCell::new(Vec::new());
    let _ = catch_unwind(AssertUnwindSafe(|| unwind_field_ladder(&l_unw_fld)));

    let l3 = RefCell::new(Vec::new());
    mu_uninit_and_ignored(&l3);
    let l4 = RefCell::new(Vec::new());
    mu_explicit(&l4);

    println!("COND_TRUE={:?}", l1.into_inner());
    println!("COND_FALSE={:?}", l2.into_inner());
    println!("COND_MOVE_REINIT={}", cmr.join(" "));
    println!("LOOP_COND_INIT={:?}", l_loop.into_inner());
    println!("UNWIND_PARTIAL_MOVE={:?}", l_unw_pm.into_inner());
    println!("UNWIND_FIELD_LADDER={:?}", l_unw_fld.into_inner());
    println!("MU_IGNORED={:?}", l3.into_inner());
    println!("MU_EXPLICIT={:?}", l4.into_inner());
}
"""


def main() -> int:
    rustc = find_rustc()
    vv = subprocess.run([rustc, "-vV"], capture_output=True, text=True, check=True).stdout.strip()
    sha_match = re.search(r"commit-hash:\s*([0-9a-f]{40})", vv)
    rust_commit_sha = sha_match.group(1) if sha_match else "unknown"

    results = {
        "probe_id": "rustc-mir-drop-elaboration-probe",
        "rustc_commit_sha": rust_commit_sha,
        "rustc_version": vv,
        "experiments": {
            "a_deterministic_drop_order": run_compile_and_exec(
                rustc,
                PROBE_A_CODE,
                edition="2024",
                dump_mir_funcs=[
                    "locals_order",
                    "struct_order",
                    "array_order",
                    "drop_replace_order",
                    "md_suppressed_probe",
                ],
            ),
            "b_partial_move_and_e0509": {
                "partial_move_without_drop_impl": run_compile_and_exec(
                    rustc,
                    PROBE_B_PARTIAL_CODE,
                    edition="2024",
                    dump_mir_funcs=[
                        "partial_move_probe",
                        "partial_move_box_deref_probe",
                        "partial_move_array_pattern_probe",
                    ],
                ),
                "partial_move_with_drop_impl_e0509": run_compile_and_exec(
                    rustc,
                    PROBE_B_E0509_CODE,
                    edition="2024",
                ),
                "drop_impl_field_assign_valid": run_compile_and_exec(
                    rustc,
                    PROBE_B_E0509_REINIT_CODE,
                    edition="2024",
                ),
            },
            "c_conditional_init_drop_flag_unwind_and_maybe_uninit": run_compile_and_exec(
                rustc,
                PROBE_C_CODE,
                edition="2024",
                dump_mir_funcs=[
                    "cond_init",
                    "cond_move_and_reinit",
                    "unwind_partial_move",
                    "unwind_field_ladder",
                    "mu_uninit_and_ignored",
                ],
            ),
        },
    }

    out_path = Path(__file__).resolve().parent / "probe_results.json"
    out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} ({out_path.stat().st_size} bytes)")
    for exp_name, exp_val in results["experiments"].items():
        if "compile_returncode" in exp_val:
            print(
                f"[{exp_name}] comp_rc={exp_val['compile_returncode']} "
                f"run_rc={exp_val.get('run_returncode', 'N/A')}"
            )
            if exp_val.get("run_stdout"):
                print(exp_val["run_stdout"])
            if exp_val["compile_returncode"] != 0:
                print(exp_val["compile_stderr"])
        else:
            for sub_name, sub_val in exp_val.items():
                print(
                    f"[{exp_name}.{sub_name}] comp_rc={sub_val['compile_returncode']} "
                    f"run_rc={sub_val.get('run_returncode', 'N/A')}"
                )
                if sub_val.get("run_stdout"):
                    print(sub_val["run_stdout"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
