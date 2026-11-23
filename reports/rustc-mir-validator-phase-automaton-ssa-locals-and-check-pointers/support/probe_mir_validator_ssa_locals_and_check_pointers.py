#!/usr/bin/env python3
"""Live rustc & Miri differential probe for MIR Validator, SsaLocals, and CheckPointers.

Reproduces primary-source invariants of:
  - compiler/rustc_mir_transform/src/validate.rs (Validator, CfgChecker, TypeChecker)
  - compiler/rustc_mir_transform/src/ssa.rs (SsaLocals, compute_copy_classes, Freeze vs !Freeze)
  - compiler/rustc_mir_transform/src/check_pointers.rs (CheckAlignment, CheckNull, BorrowedFieldProjectionMode)

All temporary files live in an automatically cleaned TemporaryDirectory and paths are
sanitized to `<TMP>` so output JSON is portable and host-agnostic.
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


def _sanitize(text: str, tmpdir: str) -> str:
    text = text.replace(tmpdir, "<TMP>")
    home = str(Path.home())
    if home:
        text = text.replace(home, "<HOME>")
    # Strip rustc remapped source prefixes (e.g. /rustc/<40-hex>/ and suffixed variants).
    text = re.sub(r"/rustc(?:-[a-z0-9_]+)?/[0-9a-f]{40}/", "<RUSTC_SRC>/", text)
    return text


def _extract_broken_mir_lines(stderr: str) -> list[str]:
    lines = stderr.splitlines()
    out: list[str] = []
    capture = 0
    for line in lines:
        if "broken MIR" in line or "internal compiler error:" in line or line.startswith("error["):
            out.append(line)
            capture = 3
        elif capture > 0:
            if line.strip().startswith("note:") or line.strip().startswith("-->") or line.strip().startswith("|"):
                out.append(line)
            elif line.strip():
                out.append(line)
            capture -= 1
    return out[:12]


def _run(cmd: list[str], cwd: Path, env: dict[str, str] | None = None, timeout: int = 60) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )


def _run_rustc_probe(
    tmpdir: Path,
    name: str,
    src: str,
    extra_args: list[str],
    crate_type: str = "lib",
) -> dict[str, Any]:
    rs_path = tmpdir / f"{name}.rs"
    rs_path.write_text(src, encoding="utf-8")
    out_path = tmpdir / f"{name}.out"
    cmd = [
        "rustc",
        "--edition=2021",
        f"--crate-type={crate_type}",
        "-o",
        str(out_path),
        *extra_args,
        str(rs_path),
    ]
    env = os.environ.copy()
    env["RUST_BACKTRACE"] = "0"
    proc = _run(cmd, tmpdir, env=env)
    stderr_s = _sanitize(proc.stderr, str(tmpdir))
    stdout_s = _sanitize(proc.stdout, str(tmpdir))
    return {
        "name": name,
        "args": extra_args,
        "rc": proc.returncode,
        "has_broken_mir": "broken MIR" in stderr_s,
        "broken_mir_lines": _extract_broken_mir_lines(stderr_s),
        "stderr_head": "\n".join(stderr_s.splitlines()[:18]),
        "stdout_head": "\n".join(stdout_s.splitlines()[:18]),
        "out_path": str(out_path) if out_path.exists() else None,
    }


def run_validator_probes(tmpdir: Path) -> dict[str, Any]:
    results: dict[str, Any] = {}

    # V1: START_BLOCK predecessor attempt in custom_mir (proves mir! structurally omits bb0 binding)
    v1_src = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn start_block_pred() -> u32 {
    mir! {
        {
            Goto(bb1)
        }
        bb1 = {
            RET = 1_u32;
            Goto(bb0)
        }
    }
}
"""
    results["v1_start_block_pred_custom_mir_hir_reject"] = _run_rustc_probe(
        tmpdir, "v1_start_block_pred", v1_src, ["-Zvalidate-mir=yes"]
    )

    # V2: (false, true, Normal) edge violation
    v2_src = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn normal_to_cleanup() -> u32 {
    mir! {
        {
            Goto(clean_bb)
        }
        clean_bb (cleanup) = {
            UnwindResume()
        }
    }
}
"""
    results["v2_normal_to_cleanup_edge"] = _run_rustc_probe(
        tmpdir, "v2_normal_to_cleanup", v2_src, ["-Zvalidate-mir=yes"]
    )

    # V3: (true, false, Normal) edge violation
    v3_src = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[inline(never)]
fn may_panic() {}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn cleanup_to_normal() -> u32 {
    mir! {
        let _u: ();
        {
            Call(_u = may_panic(), ReturnTo(ok_bb), UnwindCleanup(clean_bb))
        }
        ok_bb = {
            RET = 1_u32;
            Return()
        }
        clean_bb (cleanup) = {
            Goto(ok_bb)
        }
    }
}
"""
    results["v3_cleanup_to_normal_edge"] = _run_rustc_probe(
        tmpdir, "v3_cleanup_to_normal", v3_src, ["-Zvalidate-mir=yes"]
    )

    # V4: (false, false, Unwind) edge violation
    v4_src = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[inline(never)]
fn may_panic() {}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn unwind_to_normal() -> u32 {
    mir! {
        let _u: ();
        {
            Call(_u = may_panic(), ReturnTo(ok_bb), UnwindCleanup(bad_target))
        }
        ok_bb = {
            RET = 1_u32;
            Return()
        }
        bad_target = {
            RET = 2_u32;
            Return()
        }
    }
}
"""
    results["v4_unwind_to_normal_edge"] = _run_rustc_probe(
        tmpdir, "v4_unwind_to_normal", v4_src, ["-Zvalidate-mir=yes"]
    )

    # V5: UnwindAction::Cleanup inside a cleanup block
    v5_src = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[inline(never)]
fn may_panic() {}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn unwind_cleanup_in_cleanup() -> u32 {
    mir! {
        let _u: ();
        {
            Call(_u = may_panic(), ReturnTo(ok_bb), UnwindCleanup(clean1))
        }
        ok_bb = {
            RET = 0_u32;
            Return()
        }
        clean1 (cleanup) = {
            Call(_u = may_panic(), ReturnTo(clean2), UnwindCleanup(clean2))
        }
        clean2 (cleanup) = {
            UnwindResume()
        }
    }
}
"""
    results["v5_unwind_cleanup_in_cleanup"] = _run_rustc_probe(
        tmpdir, "v5_unwind_cleanup_in_cleanup", v5_src, ["-Zvalidate-mir=yes"]
    )

    # V6: Return from cleanup block
    v6_src = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[inline(never)]
fn may_panic() {}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn return_from_cleanup() -> u32 {
    mir! {
        let _u: ();
        {
            Call(_u = may_panic(), ReturnTo(ok_bb), UnwindCleanup(clean_bb))
        }
        ok_bb = {
            RET = 1_u32;
            Return()
        }
        clean_bb (cleanup) = {
            RET = 2_u32;
            Return()
        }
    }
}
"""
    results["v6_return_from_cleanup"] = _run_rustc_probe(
        tmpdir, "v6_return_from_cleanup", v6_src, ["-Zvalidate-mir=yes"]
    )

    # V7: UnwindResume in extern "C" (non-unwinding) function at Runtime(PostCleanup)
    v7_src = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[inline(never)]
fn may_panic() {}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub extern "C" fn resume_in_nounwind() -> u32 {
    mir! {
        let _u: ();
        {
            Call(_u = may_panic(), ReturnTo(ok_bb), UnwindCleanup(clean_bb))
        }
        ok_bb = {
            RET = 1_u32;
            Return()
        }
        clean_bb (cleanup) = {
            UnwindResume()
        }
    }
}
"""
    results["v7_resume_in_nounwind_extern_c"] = _run_rustc_probe(
        tmpdir, "v7_resume_in_nounwind", v7_src, ["-Zvalidate-mir=yes"]
    )

    # V8: Cleanup control-flow diamond violation (unwind_edge_count >= 2, out-degree 2 after contraction)
    v8_src = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[inline(never)]
fn may_panic() {}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn cleanup_diamond(flag: bool) -> u32 {
    mir! {
        let _u: ();
        {
            Call(_u = may_panic(), ReturnTo(bb_mid), UnwindCleanup(clean_a))
        }
        bb_mid = {
            Call(_u = may_panic(), ReturnTo(bb_ok), UnwindCleanup(clean_b))
        }
        bb_ok = {
            RET = 0_u32;
            Return()
        }
        clean_a (cleanup) = {
            match flag {
                true => clean_b,
                _ => clean_c,
            }
        }
        clean_b (cleanup) = {
            UnwindResume()
        }
        clean_c (cleanup) = {
            Call(_u = may_panic(), ReturnTo(clean_c2), UnwindTerminate(InCleanup))
        }
        clean_c2 (cleanup) = {
            UnwindResume()
        }
    }
}
"""
    # Better diamond: three distinct unwind pads clean_a, clean_b, clean_c where clean_a branches to clean_b and clean_c!
    v8_src_clean = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[inline(never)]
fn may_panic() {}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn cleanup_diamond(flag: bool) -> u32 {
    mir! {
        let _u: ();
        {
            Call(_u = may_panic(), ReturnTo(bb1), UnwindCleanup(clean_a))
        }
        bb1 = {
            Call(_u = may_panic(), ReturnTo(bb2), UnwindCleanup(clean_b))
        }
        bb2 = {
            Call(_u = may_panic(), ReturnTo(bb_ok), UnwindCleanup(clean_c))
        }
        bb_ok = {
            RET = 0_u32;
            Return()
        }
        clean_a (cleanup) = {
            match flag {
                true => clean_b,
                _ => clean_c,
            }
        }
        clean_b (cleanup) = {
            UnwindResume()
        }
        clean_c (cleanup) = {
            UnwindResume()
        }
    }
}
"""
    results["v8_cleanup_control_flow_diamond"] = _run_rustc_probe(
        tmpdir, "v8_cleanup_diamond", v8_src_clean, ["-Zvalidate-mir=yes"]
    )

    # V9: Runtime(Optimized) nested Deref projection (*(*p))
    v9_src = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn runtime_nested_deref(p: &&u32) -> u32 {
    mir! {
        {
            RET = *(*p);
            Return()
        }
    }
}
"""
    results["v9_runtime_nested_deref"] = _run_rustc_probe(
        tmpdir, "v9_runtime_nested_deref", v9_src, ["-Zvalidate-mir=yes"]
    )

    # V10: Runtime(Initial) Box deref banned after ElaborateBoxDerefs
    v10_src = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "initial")]
pub fn runtime_box_deref(b: Box<u32>) -> u32 {
    mir! {
        {
            RET = *b;
            Return()
        }
    }
}
"""
    results["v10_runtime_box_deref"] = _run_rustc_probe(
        tmpdir, "v10_runtime_box_deref", v10_src, ["-Zvalidate-mir=yes"]
    )

    # V11: Unconditional validation at Runtime(Optimized) WITHOUT -Zvalidate-mir=yes (pass_manager.rs:409)
    results["v11_unconditional_optimized_validation_without_flag"] = _run_rustc_probe(
        tmpdir, "v11_no_flag_broken", v2_src, []
    )

    # V12: UnwindAction::Terminate(InCleanup) in a non-cleanup block
    v12_src = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[inline(never)]
fn may_panic() {}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn terminate_incleanup_in_normal() -> u32 {
    mir! {
        let _u: ();
        {
            Call(_u = may_panic(), ReturnTo(ok_bb), UnwindTerminate(UnwindTerminateReason::InCleanup))
        }
        ok_bb = {
            RET = 1_u32;
            Return()
        }
    }
}
"""
    results["v12_terminate_incleanup_in_normal_block"] = _run_rustc_probe(
        tmpdir, "v12_terminate_incleanup_in_normal", v12_src, ["-Zvalidate-mir=yes"]
    )

    # Clean out_path keys
    for v in results.values():
        v.pop("out_path", None)
    return results


def run_ssa_probes(tmpdir: Path) -> dict[str, Any]:
    results: dict[str, Any] = {}

    # S1: Freeze (u32) vs !Freeze (Cell<u32>) under GVN + runtime + Miri
    s1_src = """use std::cell::Cell;

#[inline(never)]
fn touch_u32(r: &u32) {
    std::hint::black_box(r);
}

#[inline(never)]
fn mutate_cell(r: &Cell<u32>) {
    r.set(100);
}

#[inline(never)]
pub fn freeze_shared_borrow() -> u32 {
    let x: u32 = 42;
    let r: &u32 = &x;
    touch_u32(r);
    x + 1
}

#[inline(never)]
pub fn non_freeze_cell_shared_borrow() -> u32 {
    let c: Cell<u32> = Cell::new(42);
    let r: &Cell<u32> = &c;
    mutate_cell(r);
    c.get()
}

fn main() {
    println!("FREEZE={} CELL={}", freeze_shared_borrow(), non_freeze_cell_shared_borrow());
}
"""
    dump_dir = tmpdir / "mir_dump_s1"
    dump_dir.mkdir(exist_ok=True)
    s1_bin = _run_rustc_probe(
        tmpdir,
        "s1_freeze_vs_cell",
        s1_src,
        [
            "-C", "opt-level=2",
            "-Zmir-opt-level=2",
            "-Zdump-mir=GVN",
            f"-Zdump-mir-dir={dump_dir}",
            "-Zdump-mir-exclude-pass-number",
        ],
        crate_type="bin",
    )
    bin_path = s1_bin.pop("out_path", None)
    run_stdout = ""
    run_rc = -1
    if bin_path:
        exec_proc = _run([bin_path], tmpdir)
        run_rc = exec_proc.returncode
        run_stdout = exec_proc.stdout.strip()

    freeze_after = ""
    cell_after = ""
    for p in sorted(dump_dir.glob("*.after.mir")):
        txt = p.read_text(encoding="utf-8", errors="replace")
        if "freeze_shared_borrow" in p.name and "non_freeze" not in p.name:
            freeze_after = txt
        elif "non_freeze_cell_shared_borrow" in p.name:
            cell_after = txt

    # Also run under cargo miri!
    miri_dir = tmpdir / "miri_s1_crate"
    (miri_dir / "src").mkdir(parents=True, exist_ok=True)
    (miri_dir / "Cargo.toml").write_text(
        '[package]\nname = "miri_s1"\nversion = "0.1.0"\nedition = "2021"\n',
        encoding="utf-8",
    )
    (miri_dir / "src" / "main.rs").write_text(s1_src, encoding="utf-8")
    miri_env = os.environ.copy()
    miri_env["MIRIFLAGS"] = "-Zmiri-tree-borrows"
    miri_proc = _run(["cargo", "miri", "run", "--offline"], miri_dir, env=miri_env, timeout=120)

    results["s1_freeze_vs_nonfreeze_cell"] = {
        "compile_rc": s1_bin["rc"],
        "native_run_rc": run_rc,
        "native_stdout": run_stdout,
        "miri_rc": miri_proc.returncode,
        "miri_stdout": miri_proc.stdout.strip(),
        "miri_stderr_head": "\n".join(_sanitize(miri_proc.stderr, str(tmpdir)).splitlines()[:10]),
        "freeze_folded_const_43_in_gvn": "const 43_u32" in freeze_after,
        "non_freeze_folded_const_43_in_gvn": "const 43_u32" in cell_after,
        "freeze_gvn_after": freeze_after,
        "non_freeze_gvn_after": cell_after[:1800],
    }

    # S2: CopyProp RETURN_PLACE barrier (temp vs arg) & borrowed_locals address-identity preservation
    s2_src = """#[inline(never)]
fn observe_addrs(a: &u64, b: &u64) -> bool {
    std::ptr::eq(a, b)
}

#[inline(never)]
pub fn copy_chain_temp_to_ret(x: u64) -> u64 {
    let t1 = x.wrapping_add(7);
    let t2 = t1;
    let t3 = t2;
    t3
}

#[inline(never)]
pub fn copy_arg_to_ret(arg: u64) -> u64 {
    let a = arg;
    a
}

#[inline(never)]
pub fn copy_borrowed_distinct_addrs(x: u64) -> bool {
    let a = x.wrapping_add(1);
    let b = a;
    observe_addrs(&a, &b)
}

fn main() {
    println!(
        "TEMP={} ARG={} SAME_ADDR={}",
        copy_chain_temp_to_ret(5),
        copy_arg_to_ret(9),
        copy_borrowed_distinct_addrs(11)
    );
}
"""
    dump_dir_s2 = tmpdir / "mir_dump_s2"
    dump_dir_s2.mkdir(exist_ok=True)
    s2_bin = _run_rustc_probe(
        tmpdir,
        "s2_copy_prop",
        s2_src,
        [
            "-C", "opt-level=2",
            "-Zmir-opt-level=2",
            "-Zdump-mir=CopyProp",
            f"-Zdump-mir-dir={dump_dir_s2}",
            "-Zdump-mir-exclude-pass-number",
        ],
        crate_type="bin",
    )
    bin_s2 = s2_bin.pop("out_path", None)
    s2_exec = _run([bin_s2], tmpdir) if bin_s2 else None
    s2_dumps: dict[str, str] = {}
    for p in sorted(dump_dir_s2.glob("*.mir")):
        for key in ("copy_chain_temp_to_ret", "copy_arg_to_ret", "copy_borrowed_distinct_addrs"):
            if key in p.name:
                tag = "before" if ".before." in p.name else "after"
                s2_dumps[f"{key}_{tag}"] = p.read_text(encoding="utf-8", errors="replace")

    results["s2_copy_prop_return_place_and_borrowed_barrier"] = {
        "compile_rc": s2_bin["rc"],
        "run_rc": s2_exec.returncode if s2_exec else -1,
        "stdout": s2_exec.stdout.strip() if s2_exec else "",
        "dumps": s2_dumps,
    }

    # S3: Unreachable basic block survival in SsaLocals (GVN + CopyProp)
    s3_src = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn with_unreachable_block(x: u32) -> u32 {
    mir! {
        let dead_local: u32;
        {
            RET = x;
            Return()
        }
        unreachable_bb = {
            dead_local = x;
            RET = dead_local;
            Return()
        }
    }
}
"""
    results["s3_unreachable_block_ssa_survival"] = _run_rustc_probe(
        tmpdir,
        "s3_unreachable_block",
        s3_src,
        ["-Zmir-opt-level=2", "-Zvalidate-mir=yes"],
        crate_type="lib",
    )
    results["s3_unreachable_block_ssa_survival"].pop("out_path", None)
    return results


def run_check_pointers_probes(tmpdir: Path) -> dict[str, Any]:
    results: dict[str, Any] = {}

    # P1: CheckAlignment & CheckNull MIR instrumentation across u32, u8 (excluded), () ZST, and &(*ptr).b (FollowProjections vs NoFollowProjections)
    p1_src = """#[repr(C)]
pub struct Pair {
    pub a: u32,
    pub b: u8,
}

#[inline(never)]
pub unsafe fn read_u32(p: *const u32) -> u32 {
    *p
}

#[inline(never)]
pub unsafe fn read_u8(p: *const u8) -> u8 {
    *p
}

#[inline(never)]
pub unsafe fn read_zst(p: *const ()) -> () {
    *p
}

#[inline(never)]
pub unsafe fn borrow_zst<'a>(p: *const ()) -> &'a () {
    &*p
}

#[inline(never)]
pub unsafe fn borrow_u8_field<'a>(p: *const Pair) -> &'a u8 {
    &(*p).b
}

#[inline(never)]
pub unsafe fn read_u8_field(p: *const Pair) -> u8 {
    (*p).b
}
"""
    dump_dir_p1 = tmpdir / "mir_dump_p1"
    dump_dir_p1.mkdir(exist_ok=True)
    p1_res = _run_rustc_probe(
        tmpdir,
        "p1_check_pointers",
        p1_src,
        [
            "-Zub-checks=yes",
            "-Zmir-opt-level=0",
            "-Zdump-mir=Check",
            f"-Zdump-mir-dir={dump_dir_p1}",
            "-Zdump-mir-exclude-pass-number",
        ],
        crate_type="lib",
    )
    p1_res.pop("out_path", None)

    summary_p1: dict[str, Any] = {}
    for fn_name in ("read_u32", "read_u8", "read_zst", "borrow_zst", "borrow_u8_field", "read_u8_field"):
        fn_info: dict[str, Any] = {}
        for pass_name in ("CheckAlignment", "CheckNull"):
            before_files = list(dump_dir_p1.glob(f"*{fn_name}.*.{pass_name}.*before.mir")) + list(dump_dir_p1.glob(f"*{fn_name}.{pass_name}.*before.mir"))
            after_files = list(dump_dir_p1.glob(f"*{fn_name}.*.{pass_name}.*after.mir")) + list(dump_dir_p1.glob(f"*{fn_name}.{pass_name}.*after.mir"))
            if before_files and after_files:
                btxt = before_files[0].read_text(encoding="utf-8", errors="replace")
                atxt = after_files[0].read_text(encoding="utf-8", errors="replace")
                bbody = "\n".join(btxt.splitlines()[1:])
                abody = "\n".join(atxt.splitlines()[1:])
                fn_info[pass_name] = {
                    "changed": bbody != abody,
                    "has_misaligned_assert": "misaligned pointer dereference" in atxt,
                    "has_null_assert": "null pointer dereference" in atxt,
                    "has_unwind_unreachable": "unwind unreachable" in atxt,
                    "has_align_const": "SizedTypeProperties>::ALIGN" in atxt,
                    "has_size_const": "SizedTypeProperties>::SIZE" in atxt,
                    "after_mir": atxt,
                }
        summary_p1[fn_name] = fn_info

    results["p1_mir_instrumentation_matrix"] = {
        "compile_rc": p1_res["rc"],
        "functions": summary_p1,
    }

    # P2: Runtime UB-check trap on misaligned & null dereference (safe child execution)
    p2_src = """use std::env;
#[inline(never)]
unsafe fn load_u32(p: *const u32) -> u32 {
    *p
}
fn main() {
    let mode = env::args().nth(1).unwrap_or_default();
    match mode.as_str() {
        "misaligned" => {
            let buf: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
            let unaligned = unsafe { buf.as_ptr().add(1) as *const u32 };
            let v = unsafe { load_u32(unaligned) };
            println!("VAL={v}");
        }
        "null" => {
            let v = unsafe { load_u32(std::ptr::null()) };
            println!("VAL={v}");
        }
        "null_zst_read" => {
            let p: *const () = std::ptr::null();
            let () = unsafe { *p };
            println!("ZST_READ_OK");
        }
        "null_zst_borrow" => {
            let p: *const () = std::ptr::null();
            let r: &() = unsafe { &*p };
            std::hint::black_box(r);
            println!("ZST_BORROW_OK");
        }
        "misaligned_borrow_u8_field" => {
            #[repr(C)]
            struct Pair { a: u32, b: u8 }
            let buf: [u8; 16] = [0xAA; 16];
            let unaligned = unsafe { buf.as_ptr().add(1) as *const Pair };
            // BorrowedFieldProjectionMode::FollowProjections checks align_of::<u8>() == 1!
            let r: &u8 = unsafe { &(*unaligned).b };
            println!("BORROW_U8_FIELD={}", *r);
        }
        _ => {}
    }
}
"""
    p2_bin = _run_rustc_probe(
        tmpdir,
        "p2_ub_check_runtime",
        p2_src,
        ["-Zub-checks=yes", "-C", "opt-level=0"],
        crate_type="bin",
    )
    bin_p2 = p2_bin.pop("out_path", None)
    p2_cases: dict[str, Any] = {}
    if bin_p2:
        for mode in ("misaligned", "null", "null_zst_read", "null_zst_borrow", "misaligned_borrow_u8_field"):
            proc = _run([bin_p2, mode], tmpdir)
            p2_cases[mode] = {
                "rc": proc.returncode,
                "stdout": proc.stdout.strip(),
                "stderr_head": "\n".join(_sanitize(proc.stderr, str(tmpdir)).splitlines()[:8]),
            }
    results["p2_runtime_ub_checks"] = {
        "compile_rc": p2_bin["rc"],
        "cases": p2_cases,
    }

    # P3: Empirical check of check_pointers.rs:87 statement-only visitor vs terminator Place
    p3_src = """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
extern crate core;
use core::intrinsics::mir::*;

#[inline(never)]
fn sink(v: u32) -> u32 { v }

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub unsafe fn call_arg_deref_terminator(p: *const u32) -> u32 {
    mir! {
        {
            Call(RET = sink(*p), ReturnTo(bb1), UnwindContinue())
        }
        bb1 = {
            Return()
        }
    }
}
"""
    dump_dir_p3 = tmpdir / "mir_dump_p3"
    dump_dir_p3.mkdir(exist_ok=True)
    p3_res = _run_rustc_probe(
        tmpdir,
        "p3_terminator_bypass",
        p3_src,
        [
            "-Zub-checks=yes",
            "-Zmir-opt-level=0",
            "-Zvalidate-mir=yes",
            "-Zdump-mir=Check",
            f"-Zdump-mir-dir={dump_dir_p3}",
            "-Zdump-mir-exclude-pass-number",
        ],
        crate_type="lib",
    )
    p3_res.pop("out_path", None)
    p3_passes: dict[str, Any] = {}
    for pass_name in ("CheckAlignment", "CheckNull"):
        bf = list(dump_dir_p3.glob(f"*call_arg_deref_terminator.*{pass_name}.*before.mir"))
        af = list(dump_dir_p3.glob(f"*call_arg_deref_terminator.*{pass_name}.*after.mir"))
        if bf and af:
            btxt = bf[0].read_text(encoding="utf-8", errors="replace")
            atxt = af[0].read_text(encoding="utf-8", errors="replace")
            bbody = "\n".join(btxt.splitlines()[1:])
            abody = "\n".join(atxt.splitlines()[1:])
            p3_passes[pass_name] = {
                "changed": bbody != abody,
                "before_mir": btxt,
                "after_mir": atxt,
            }
    results["p3_terminator_statement_only_gap"] = {
        "compile_rc": p3_res["rc"],
        "has_broken_mir": p3_res["has_broken_mir"],
        "stderr_head": p3_res["stderr_head"],
        "passes": p3_passes,
    }

    return results


def main() -> int:
    rustc_ver = subprocess.check_output(["rustc", "--version", "--verbose"], text=True).strip()
    try:
        miri_ver = subprocess.check_output(["cargo", "miri", "--version"], text=True).strip()
    except Exception as exc:
        miri_ver = f"unavailable ({exc})"

    with tempfile.TemporaryDirectory(prefix="rustc_mir_valssa_probe_") as td:
        tmpdir = Path(td)
        payload = {
            "rustc_version": rustc_ver,
            "miri_version": miri_ver,
            "validator_probes": run_validator_probes(tmpdir),
            "ssa_locals_probes": run_ssa_probes(tmpdir),
            "check_pointers_probes": run_check_pointers_probes(tmpdir),
        }

    out_arg = sys.argv[1] if len(sys.argv) > 1 else None
    rendered = json.dumps(payload, indent=2, sort_keys=False) + "\n"
    if out_arg:
        Path(out_arg).write_text(rendered, encoding="utf-8")
        print(f"Wrote {out_arg} ({len(rendered)} bytes)")
    else:
        print(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
