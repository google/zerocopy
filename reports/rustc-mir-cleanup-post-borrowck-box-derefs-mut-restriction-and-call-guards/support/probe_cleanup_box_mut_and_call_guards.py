#!/usr/bin/env python3
"""Live rustc + Miri differential probe for post-borrowck & pre-codegen MIR passes.

Empirically characterizes:
  1. CleanupPostBorrowck (administrative statement erasure to Nop,
     ArrayToPointer/MutToConstPointer -> PtrToPtr lowering vs. preserved Unsize,
     FalseEdge/FalseUnwind -> Goto collapsing, and Coverage BlockMarker erasure
     vs. preserved VirtualCounter).
  2. ElaborateBoxDerefs (basic-block Box dereference lowering across sized,
     nested, slice/DST, and ZST boxes vs. 4-level VarDebugInfo projection
     through NonNull/PatternKind::NotNull, plus live Miri execution under both
     Stacked Borrows and Tree Borrows on valid Box derefs and UB cases).
  3. CheckMutRestriction (#![feature(mut_restriction)] across direct field
     mutation, indexed field projection, struct aggregate construction,
     tuple-struct constructor-as-value, union restricted vs. unrestricted field
     construction, and permitted whole-ADT overwrite). Accurately classifies
     whether the host toolchain enforces CheckMutRestriction, accepts syntax
     fail-open (predating check_mut_restriction.rs), or rejects the feature.
  4. RemoveNoopLandingPads & AddCallGuards::CriticalCallEdges across BOTH
     runtime-lowering (2-2-001) and pre-codegen (3-2-023) passes under both
     panic=unwind and panic=abort, covering noop landing-pad pruning, live Drop
     guards, single-predecessor invokes, and InlineAsm label/may_unwind
     critical edges with and without output operands.

All temporary compilation artifacts live inside tempfile.TemporaryDirectory()
and are removed on exit. Host-specific paths are scrubbed before serialization.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any


def sanitize(text: str, tmpdir: str) -> str:
    """Scrub temporary directories and home/host paths from captured output."""
    out = text.replace(tmpdir, "<TMPDIR>")
    home = os.path.expanduser("~")
    if home and home != "/":
        out = out.replace(home, "<HOME>")
    out = re.sub(r"/rustc/[0-9a-f]{40}/", "/rustc/<COMMIT>/", out)
    out = re.sub(r"/rustc-dev/[0-9a-f]{40}/", "/rustc-dev/<COMMIT>/", out)
    return out


def run_cmd(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    merged_env = os.environ.copy()
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    if cargo_bin not in merged_env.get("PATH", ""):
        merged_env["PATH"] = f"{cargo_bin}:{merged_env.get('PATH', '')}"
    if env:
        merged_env.update(env)
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=merged_env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )


def count_bbs(mir_text: str) -> int:
    return len(re.findall(r"^\s+bb\d+(?:\s+\(cleanup\))?:", mir_text, re.MULTILINE))


def find_mir_pairs(mir_dir: Path, fn_substr: str, pass_name: str) -> list[dict[str, Any]]:
    """Return all ordered (before, after) dump pairs for a function and pass."""
    befores = sorted(mir_dir.glob(f"*{fn_substr}*.{pass_name}.before.mir"))
    pairs: list[dict[str, Any]] = []
    for bp in befores:
        ap = Path(str(bp).replace(".before.mir", ".after.mir"))
        pairs.append(
            {
                "before_name": bp.name,
                "after_name": ap.name if ap.exists() else None,
                "before_text": bp.read_text(encoding="utf-8"),
                "after_text": ap.read_text(encoding="utf-8") if ap.exists() else "",
            }
        )
    return pairs


def probe_cleanup_post_borrowck(tmp: Path) -> dict[str, Any]:
    src = tmp / "cleanup_probe.rs"
    src.write_text(
        """
#![allow(dead_code, unused_variables, unused_assignments)]

pub struct DropGuard;
impl Drop for DropGuard {
    #[inline(never)]
    fn drop(&mut self) {}
}

#[inline(never)]
pub fn cleanup_full_matrix(opt: Option<&u32>, arr: &[u32; 4], m: &mut u32) -> u32 {
    let _g = DropGuard;
    let typed_val: u32 = *m;
    let p_arr: *const u32 = arr as *const u32;
    let p_mut: *mut u32 = m;
    let p_const: *const u32 = p_mut;
    let slice: &[u32] = arr;
    let matched = match opt {
        Some(v) if *v > 10 => *v,
        Some(v) => v.wrapping_add(1),
        None => 0,
    };
    let mut cnt = matched & 3;
    loop {
        if cnt == 0 {
            break;
        }
        cnt -= 1;
    }
    let mut sum = typed_val.wrapping_add(matched).wrapping_add(cnt).wrapping_add(slice.len() as u32);
    unsafe {
        sum = sum.wrapping_add(*p_arr).wrapping_add(*p_const);
    }
    sum
}

#[inline(never)]
pub fn cov_branch(a: bool, b: bool) -> u32 {
    if a && b { 1 } else { 2 }
}
""",
        encoding="utf-8",
    )

    mir_dir = tmp / "mir_cleanup"
    mir_dir.mkdir()
    p = run_cmd(
        [
            "rustc",
            "--crate-type=lib",
            "--edition=2021",
            "-Z",
            "dump-mir=CleanupPostBorrowck",
            "-Z",
            f"dump-mir-dir={mir_dir}",
            "--out-dir",
            str(tmp),
            str(src),
        ]
    )
    pairs = find_mir_pairs(mir_dir, "cleanup_full_matrix", "CleanupPostBorrowck")
    before_txt = pairs[0]["before_text"] if pairs else ""
    after_txt = pairs[0]["after_text"] if pairs else ""

    def metrics(txt: str) -> dict[str, int]:
        return {
            "fake_read": len(re.findall(r"FakeRead\(", txt)),
            "fake_borrow": len(re.findall(r"&fake\b", txt)),
            "ascribe_user_type": len(re.findall(r"AscribeUserType\(", txt)),
            "user_ty_decl": len(re.findall(r"user_ty:", txt)),
            "false_edge": len(re.findall(r"falseEdge\s*->", txt)),
            "false_unwind": len(re.findall(r"falseUnwind\s*->", txt)),
            "coercion_array_to_ptr": len(re.findall(r"PointerCoercion\(ArrayToPointer", txt)),
            "coercion_mut_to_const": len(re.findall(r"PointerCoercion\(MutToConstPointer", txt)),
            "coercion_unsize": len(re.findall(r"PointerCoercion\(Unsize", txt)),
            "ptr_to_ptr": len(re.findall(r"\(PtrToPtr\)", txt)),
            "nop_stmts": len(re.findall(r"^\s+nop;$", txt, re.MULTILINE)),
            "goto_terms": len(re.findall(r"^\s+goto -> bb\d+;$", txt, re.MULTILINE)),
            "bb_count": count_bbs(txt),
        }

    # Branch-coverage marker erasure sub-probe
    cov_dir = tmp / "mir_cleanup_cov"
    cov_dir.mkdir()
    p_cov = run_cmd(
        [
            "rustc",
            "--crate-type=lib",
            "--edition=2021",
            "-C",
            "instrument-coverage",
            "-Z",
            "coverage-options=branch",
            "-Z",
            "dump-mir=CleanupPostBorrowck",
            "-Z",
            f"dump-mir-dir={cov_dir}",
            "--out-dir",
            str(tmp),
            str(src),
        ]
    )
    cov_pairs = find_mir_pairs(cov_dir, "cov_branch", "CleanupPostBorrowck")
    cov_before = cov_pairs[0]["before_text"] if cov_pairs else ""
    cov_after = cov_pairs[0]["after_text"] if cov_pairs else ""

    def cov_metrics(txt: str) -> dict[str, int]:
        return {
            "block_marker": len(re.findall(r"Coverage::BlockMarker", txt)),
            "span_marker": len(re.findall(r"Coverage::SpanMarker", txt)),
            "point_marker": len(re.findall(r"Coverage::Point", txt)),
            "virtual_counter": len(re.findall(r"Coverage::VirtualCounter", txt)),
            "nop_stmts": len(re.findall(r"^\s+nop;$", txt, re.MULTILINE)),
        }

    return {
        "rc": p.returncode,
        "stderr": sanitize(p.stderr, str(tmp)),
        "before_file": pairs[0]["before_name"] if pairs else None,
        "after_file": pairs[0]["after_name"] if pairs else None,
        "before_metrics": metrics(before_txt),
        "after_metrics": metrics(after_txt),
        "coverage_branch_probe": {
            "rc": p_cov.returncode,
            "before_file": cov_pairs[0]["before_name"] if cov_pairs else None,
            "after_file": cov_pairs[0]["after_name"] if cov_pairs else None,
            "before": cov_metrics(cov_before),
            "after": cov_metrics(cov_after),
        },
        "before_excerpt": sanitize("\n".join(before_txt.splitlines()[:115]), str(tmp)),
        "after_excerpt": sanitize("\n".join(after_txt.splitlines()[:115]), str(tmp)),
    }


def probe_elaborate_box_derefs(tmp: Path) -> dict[str, Any]:
    src = tmp / "box_deref_probe.rs"
    src.write_text(
        """
#![allow(dead_code, unused_variables, internal_features)]
#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;

#[inline(never)]
pub fn box_tuple_and_nested(mut b: Box<(u32, u32)>, mut bb: Box<Box<u32>>, bs: Box<[u32]>, bz: Box<()>) -> u32 {
    (*b).0 = (*b).0.wrapping_add(10);
    **bb = (**bb).wrapping_add(5);
    let first = if !bs.is_empty() { (*bs)[0] } else { 0 };
    let _u: () = *bz;
    (*b).0.wrapping_add((*b).1).wrapping_add(**bb).wrapping_add(first)
}

#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
pub fn custom_box_var_debug(b: Box<u32>) -> u32 {
    mir! {
        debug inner => *b;
        {
            RET = *b;
            Return()
        }
    }
}
""",
        encoding="utf-8",
    )

    mir_dir = tmp / "mir_box"
    mir_dir.mkdir()
    p = run_cmd(
        [
            "rustc",
            "--crate-type=lib",
            "--edition=2021",
            "-C",
            "debuginfo=2",
            "-Z",
            "dump-mir=ElaborateBoxDerefs",
            "-Z",
            f"dump-mir-dir={mir_dir}",
            "--out-dir",
            str(tmp),
            str(src),
        ]
    )

    p1 = find_mir_pairs(mir_dir, "box_tuple_and_nested", "ElaborateBoxDerefs")
    p2 = find_mir_pairs(mir_dir, "custom_box_var_debug", "ElaborateBoxDerefs")
    b1_before = p1[0]["before_text"] if p1 else ""
    b1_after = p1[0]["after_text"] if p1 else ""
    b2_before = p2[0]["before_text"] if p2 else ""
    b2_after = p2[0]["after_text"] if p2 else ""

    dbg_before_lines = [ln.strip() for ln in b2_before.splitlines() if "debug " in ln]
    dbg_after_lines = [ln.strip() for ln in b2_after.splitlines() if "debug " in ln]

    return {
        "rc": p.returncode,
        "stderr": sanitize(p.stderr, str(tmp)),
        "before_file": p1[0]["before_name"] if p1 else None,
        "after_file": p1[0]["after_name"] if p1 else None,
        "uses_box_deref_transmute": "(BoxDerefTransmute)" in b1_after,
        "uses_generic_transmute": "(Transmute)" in b1_after,
        "uses_box_raw": "BoxRaw<" in b1_after,
        "uses_unique_nonnull_chain": "Unique<" in b1_after and "NonNull<" in b1_after,
        "cast_lines_after": [ln.strip() for ln in b1_after.splitlines() if "Transmute)" in ln],
        "var_debug_before_file": p2[0]["before_name"] if p2 else None,
        "var_debug_after_file": p2[0]["after_name"] if p2 else None,
        "var_debug_before_lines": dbg_before_lines,
        "var_debug_after_lines": dbg_after_lines,
        "var_debug_has_pattern_not_null": any("is !null" in ln for ln in dbg_after_lines),
        "var_debug_after_mir": sanitize(b2_after, str(tmp)),
        "before_excerpt": sanitize("\n".join(b1_before.splitlines()[:80]), str(tmp)),
        "after_excerpt": sanitize("\n".join(b1_after.splitlines()[:100]), str(tmp)),
    }


def probe_miri_box_deref(tmp: Path) -> dict[str, Any]:
    """Run live cargo miri (Stacked Borrows & Tree Borrows) on valid and UB Box derefs."""
    pkg_ok = tmp / "miri_box_ok"
    (pkg_ok / "src").mkdir(parents=True)
    (pkg_ok / "Cargo.toml").write_text(
        '[package]\nname = "miri_box_ok"\nversion = "0.1.0"\nedition = "2021"\n',
        encoding="utf-8",
    )
    (pkg_ok / "src" / "main.rs").write_text(
        """
fn mutate_boxes(mut b: Box<(u32, u32)>, mut bb: Box<Box<u32>>, mut bs: Box<[u32]>, bz: Box<()>) -> u32 {
    (*b).0 += 10;
    (*b).1 += 20;
    **bb += 7;
    (*bs)[0] += 3;
    (*bs)[1] += 4;
    let () = *bz;
    let addr_before = &raw const (*b).0 as usize;
    (*b).0 += 1;
    let addr_after = &raw const (*b).0 as usize;
    assert_eq!(addr_before, addr_after);
    (*b).0 + (*b).1 + **bb + (*bs)[0] + (*bs)[1]
}

fn main() {
    let b = Box::new((1u32, 2u32));
    let bb = Box::new(Box::new(3u32));
    let bs: Box<[u32]> = vec![4u32, 5u32].into_boxed_slice();
    let bz = Box::new(());
    let total = mutate_boxes(b, bb, bs, bz);
    println!("CHECKSUM={total}");
}
""",
        encoding="utf-8",
    )

    native_bin = tmp / "miri_box_ok_native"
    p_comp = run_cmd(["rustc", "--edition=2021", str(pkg_ok / "src" / "main.rs"), "-o", str(native_bin)])
    p_native = run_cmd([str(native_bin)]) if p_comp.returncode == 0 else p_comp

    p_miri_sb = run_cmd(["cargo", "miri", "run", "--offline"], cwd=pkg_ok, timeout=180)
    p_miri_tb = run_cmd(
        ["cargo", "miri", "run", "--offline"],
        cwd=pkg_ok,
        env={"MIRIFLAGS": "-Zmiri-tree-borrows"},
        timeout=180,
    )

    def run_miri_ub(name: str, main_rs: str) -> dict[str, Any]:
        pkg = tmp / name
        (pkg / "src").mkdir(parents=True)
        (pkg / "Cargo.toml").write_text(
            f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "2021"\n',
            encoding="utf-8",
        )
        (pkg / "src" / "main.rs").write_text(main_rs, encoding="utf-8")
        p = run_cmd(["cargo", "miri", "run", "--offline"], cwd=pkg, timeout=180)
        clean = sanitize(p.stderr, str(tmp))
        excerpt = "\n".join(
            ln
            for ln in clean.splitlines()
            if "error:" in ln or "Undefined Behavior" in ln or "dangling" in ln or "aligned" in ln
        )[:1200]
        return {
            "rc": p.returncode,
            "detected_ub": "Undefined Behavior" in clean,
            "stderr_excerpt": excerpt,
        }

    ub_dangling = run_miri_ub(
        "miri_box_ub_dangling",
        """
fn main() {
    let b = Box::new(42u32);
    let raw = Box::into_raw(b);
    unsafe {
        drop(Box::from_raw(raw));
        let dangling: Box<u32> = Box::from_raw(raw);
        let v = *dangling;
        std::mem::forget(dangling);
        println!("{v}");
    }
}
""",
    )

    ub_unaligned = run_miri_ub(
        "miri_box_ub_unaligned",
        """
#[repr(align(8))]
struct Aligned([u8; 8]);

fn main() {
    let mut buf = Aligned([0u8; 8]);
    let unaligned_ptr = unsafe { buf.0.as_mut_ptr().add(1) as *mut u32 };
    unsafe {
        let bad_box: Box<u32> = std::mem::transmute(unaligned_ptr);
        let v = *bad_box;
        std::mem::forget(bad_box);
        println!("{v}");
    }
}
""",
    )

    # Discriminator for CastKind::Transmute (1.98.0-nightly) vs CastKind::BoxDerefTransmute (HEAD):
    # Temporarily overwrite a live local Box<u32>'s pointer with an unaligned non-null pointer,
    # take `&raw const (*b)`, then restore the valid pointer before drop.
    pkg_gap = tmp / "miri_box_transmute_gap"
    (pkg_gap / "src").mkdir(parents=True)
    (pkg_gap / "Cargo.toml").write_text(
        '[package]\nname = "miri_box_transmute_gap"\nversion = "0.1.0"\nedition = "2021"\n',
        encoding="utf-8",
    )
    (pkg_gap / "src" / "main.rs").write_text(
        """
#[repr(align(8))]
struct Aligned([u8; 8]);

fn main() {
    let mut buf = Aligned([0u8; 8]);
    let unaligned: *mut u32 = unsafe { buf.0.as_mut_ptr().add(1) as *mut u32 };
    let mut b: Box<u32> = Box::new(42);
    unsafe {
        let b_slot: *mut *mut u32 = (&raw mut b).cast::<*mut u32>();
        let orig = b_slot.read();
        b_slot.write(unaligned);
        let raw_p: *const u32 = &raw const (*b);
        let mod4 = (raw_p as usize) % 4;
        b_slot.write(orig);
        println!("UNALIGNED_BOX_RAW_DEREF_MOD4={mod4}");
    }
}
""",
        encoding="utf-8",
    )
    p_gap = run_cmd(["cargo", "miri", "run", "--offline"], cwd=pkg_gap, timeout=180)
    gap_clean_stderr = sanitize(p_gap.stderr, str(tmp))
    ub_gap = {
        "rc": p_gap.returncode,
        "stdout": p_gap.stdout.strip(),
        "detected_ub": "Undefined Behavior" in gap_clean_stderr,
        "stderr_excerpt": "\n".join(
            ln
            for ln in gap_clean_stderr.splitlines()
            if "error:" in ln or "Undefined Behavior" in ln or "align" in ln
        )[:1200],
    }

    return {
        "native_ok": {"rc": p_native.returncode, "stdout": p_native.stdout.strip()},
        "miri_stacked_borrows_ok": {
            "rc": p_miri_sb.returncode,
            "stdout": p_miri_sb.stdout.strip(),
        },
        "miri_tree_borrows_ok": {
            "rc": p_miri_tb.returncode,
            "stdout": p_miri_tb.stdout.strip(),
        },
        "miri_dangling_box_ub": ub_dangling,
        "miri_unaligned_box_ub": ub_unaligned,
        "miri_box_transmute_raw_deref_discriminator": ub_gap,
    }


def probe_check_mut_restriction(tmp: Path) -> dict[str, Any]:
    cases = {
        "direct_field_mut_err": (
            True,
            """
#![feature(mut_restriction)]
pub mod inner {
    pub struct S { pub mut(in crate::inner) x: u32, pub y: u32 }
    impl S { pub fn new(x: u32) -> Self { Self { x, y: 0 } } }
}
pub fn bad_mut(s: &mut inner::S) { s.x = 42; }
""",
        ),
        "index_proj_field_mut_err": (
            True,
            """
#![feature(mut_restriction)]
pub mod inner {
    pub struct S { pub mut(in crate::inner) arr: [u32; 4] }
    impl S { pub fn new() -> Self { Self { arr: [0; 4] } } }
}
pub fn bad_idx_mut(s: &mut inner::S) { s.arr[0] = 42; }
""",
        ),
        "struct_aggregate_err": (
            True,
            """
#![feature(mut_restriction)]
pub mod inner {
    pub struct S { pub mut(in crate::inner) x: u32, pub y: u32 }
}
pub fn bad_aggr() -> inner::S { inner::S { x: 1, y: 2 } }
""",
        ),
        "tuple_ctor_fn_val_err": (
            True,
            """
#![feature(mut_restriction)]
pub mod inner {
    pub struct Tup(pub mut(in crate::inner) u32);
}
pub fn bad_ctor() -> fn(u32) -> inner::Tup { inner::Tup }
""",
        ),
        "whole_struct_overwrite_allowed": (
            False,
            """
#![feature(mut_restriction)]
pub mod inner {
    pub struct S { pub mut(in crate::inner) x: u32, pub y: u32 }
    impl S { pub fn new(x: u32) -> Self { Self { x, y: 0 } } }
}
pub fn ok_overwrite(s: &mut inner::S) { *s = inner::S::new(99); }
""",
        ),
        "union_unrestricted_field_allowed": (
            False,
            """
#![feature(mut_restriction)]
pub mod inner {
    pub union U { pub a: u32, pub mut(in crate::inner) b: u32 }
}
pub fn ok_union() -> inner::U { inner::U { a: 1 } }
""",
        ),
        "union_restricted_field_err": (
            True,
            """
#![feature(mut_restriction)]
pub mod inner {
    pub union U { pub a: u32, pub mut(in crate::inner) b: u32 }
}
pub fn bad_union() -> inner::U { inner::U { b: 1 } }
""",
        ),
    }

    results: dict[str, Any] = {}
    any_unknown_feature = False
    for name, (expect_err, code) in cases.items():
        path = tmp / f"mut_res_{name}.rs"
        path.write_text(code, encoding="utf-8")
        p = run_cmd(
            [
                "rustc",
                "--crate-type=lib",
                "--edition=2021",
                "--out-dir",
                str(tmp),
                str(path),
            ]
        )
        stderr_clean = sanitize(p.stderr, str(tmp))
        if "unknown feature" in stderr_clean:
            any_unknown_feature = True
        results[name] = {
            "expected_error": expect_err,
            "rc": p.returncode,
            "matched_expectation": (p.returncode != 0) if expect_err else (p.returncode == 0),
            "stderr": stderr_clean,
        }

    all_matched = all(v["matched_expectation"] for v in results.values())
    all_rc_zero = all(v["rc"] == 0 for v in results.values())
    if any_unknown_feature:
        status = "unknown_feature"
    elif all_matched:
        status = "enforced"
    elif all_rc_zero:
        status = "syntax_accepted_lint_absent_fail_open"
    else:
        status = "partial_mismatch"

    return {
        "status": status,
        "all_expectations_matched": all_matched,
        "cases": results,
    }


def probe_call_guards_and_landing_pads(tmp: Path) -> dict[str, Any]:
    src = tmp / "call_guards_probe.rs"
    src.write_text(
        """
#![allow(dead_code)]
#![feature(asm_goto_with_outputs, asm_unwind)]

#[inline(never)]
pub fn may_unwind(x: u32) -> u32 {
    if x == 999 { panic!("boom"); }
    x.wrapping_add(1)
}

pub struct Guard(pub u32);
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        core::hint::black_box(self.0);
    }
}

#[inline(never)]
pub fn critical_noop_lp(b: bool) -> u32 {
    let r = if b { may_unwind(1) } else { 0 };
    r.wrapping_add(2)
}

#[inline(never)]
pub fn critical_real_drop_guard(b: bool) -> u32 {
    let _g = Guard(7);
    let r = if b { may_unwind(1) } else { 0 };
    r.wrapping_add(2)
}

#[inline(never)]
pub fn non_critical_invoke_single_pred() -> u32 {
    let _g = Guard(9);
    let r = may_unwind(1);
    r.wrapping_add(2)
}

#[inline(never)]
pub fn asm_label_with_output(b: bool, mut x: u64) -> u64 {
    if b {
        unsafe {
            core::arch::asm!(
                "add {0}, 1",
                "jmp {lbl}",
                inout(reg) x,
                lbl = label {
                    x = x.wrapping_add(10);
                },
            );
        }
    }
    x
}

#[inline(never)]
pub fn asm_label_no_output(b: bool) -> u64 {
    let mut r = 1u64;
    if b {
        unsafe {
            core::arch::asm!(
                "jmp {lbl}",
                lbl = label {
                    r = 2;
                },
            );
        }
    }
    r
}

#[inline(never)]
pub fn asm_may_unwind_with_output(b: bool, mut x: u64) -> u64 {
    let _g = Guard(11);
    if b {
        unsafe {
            core::arch::asm!(
                "add {0}, 1",
                inout(reg) x,
                options(may_unwind),
            );
        }
    }
    x
}

#[inline(never)]
pub fn asm_may_unwind_no_output(b: bool) -> u64 {
    let _g = Guard(13);
    let mut x = 1u64;
    if b {
        unsafe {
            core::arch::asm!(
                "nop",
                options(may_unwind),
            );
        }
        x = 2;
    }
    x
}
""",
        encoding="utf-8",
    )

    mir_dir = tmp / "mir_cg"
    mir_dir.mkdir()
    p = run_cmd(
        [
            "rustc",
            "--crate-type=lib",
            "--edition=2021",
            "-C",
            "opt-level=2",
            "-Z",
            "dump-mir=RemoveNoopLandingPads|AddCallGuards",
            "-Z",
            f"dump-mir-dir={mir_dir}",
            "--out-dir",
            str(tmp),
            str(src),
        ]
    )

    mir_dir_abort = tmp / "mir_cg_abort"
    mir_dir_abort.mkdir()
    p_abort = run_cmd(
        [
            "rustc",
            "--crate-type=lib",
            "--edition=2021",
            "-C",
            "opt-level=2",
            "-C",
            "panic=abort",
            "-Z",
            "dump-mir=RemoveNoopLandingPads|AddCallGuards",
            "-Z",
            f"dump-mir-dir={mir_dir_abort}",
            "--out-dir",
            str(tmp),
            str(src),
        ]
    )

    fns = [
        "critical_noop_lp",
        "critical_real_drop_guard",
        "non_critical_invoke_single_pred",
        "asm_label_with_output",
        "asm_label_no_output",
        "asm_may_unwind_with_output",
        "asm_may_unwind_no_output",
    ]
    fn_summary: dict[str, Any] = {}
    for fn in fns:
        lp_pairs = find_mir_pairs(mir_dir, fn, "RemoveNoopLandingPads")
        cg_pairs = find_mir_pairs(mir_dir, fn, "AddCallGuards")
        lp_abort_pairs = find_mir_pairs(mir_dir_abort, fn, "RemoveNoopLandingPads")
        cg_abort_pairs = find_mir_pairs(mir_dir_abort, fn, "AddCallGuards")

        def summarize_cg(pairs: list[dict[str, Any]]) -> list[dict[str, Any]]:
            out_list = []
            for pair in pairs:
                bb_b = count_bbs(pair["before_text"])
                bb_a = count_bbs(pair["after_text"])
                out_list.append(
                    {
                        "before_file": pair["before_name"],
                        "after_file": pair["after_name"],
                        "bb_before": bb_b,
                        "bb_after": bb_a,
                        "split_delta": bb_a - bb_b,
                    }
                )
            return out_list

        def summarize_lp(pairs: list[dict[str, Any]]) -> list[dict[str, Any]]:
            out_list = []
            for pair in pairs:
                out_list.append(
                    {
                        "before_file": pair["before_name"],
                        "after_file": pair["after_name"],
                        "cleanup_before": len(re.findall(r"unwind: bb\d+", pair["before_text"])),
                        "cleanup_after": len(re.findall(r"unwind: bb\d+", pair["after_text"])),
                        "continue_before": len(re.findall(r"unwind continue", pair["before_text"])),
                        "continue_after": len(re.findall(r"unwind continue", pair["after_text"])),
                    }
                )
            return out_list

        entry: dict[str, Any] = {
            "unwind_remove_noop_lp": summarize_lp(lp_pairs),
            "unwind_add_call_guards": summarize_cg(cg_pairs),
            "abort_remove_noop_lp": summarize_lp(lp_abort_pairs),
            "abort_add_call_guards": summarize_cg(cg_abort_pairs),
        }
        if cg_pairs and fn in (
            "critical_noop_lp",
            "critical_real_drop_guard",
            "asm_label_with_output",
            "asm_may_unwind_with_output",
        ):
            entry["final_cg_before_mir"] = sanitize(cg_pairs[-1]["before_text"], str(tmp))
            entry["final_cg_after_mir"] = sanitize(cg_pairs[-1]["after_text"], str(tmp))
        fn_summary[fn] = entry

    return {
        "rc_unwind": p.returncode,
        "stderr_unwind": sanitize(p.stderr, str(tmp)),
        "rc_abort": p_abort.returncode,
        "stderr_abort": sanitize(p_abort.stderr, str(tmp)),
        "functions": fn_summary,
    }


def main() -> int:
    rustc_vv = run_cmd(["rustc", "-Vv"])
    miri_v = run_cmd(["cargo", "miri", "--version"])
    with tempfile.TemporaryDirectory(prefix="probe_cleanup_box_mut_cg_") as td:
        tmp = Path(td)
        out: dict[str, Any] = {
            "rustc_vv": rustc_vv.stdout.strip(),
            "miri_version": miri_v.stdout.strip(),
            "probes": {
                "cleanup_post_borrowck": probe_cleanup_post_borrowck(tmp),
                "elaborate_box_derefs": probe_elaborate_box_derefs(tmp),
                "miri_box_deref": probe_miri_box_deref(tmp),
                "check_mut_restriction": probe_check_mut_restriction(tmp),
                "call_guards_and_landing_pads": probe_call_guards_and_landing_pads(tmp),
            },
        }

    out_path = Path(__file__).resolve().parent / "probe_results.json"
    out_path.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} ({out_path.stat().st_size} bytes)")

    cpb = out["probes"]["cleanup_post_borrowck"]
    print("CleanupPostBorrowck rc:", cpb["rc"])
    print("  before:", cpb["before_metrics"])
    print("  after :", cpb["after_metrics"])
    print("  cov_branch:", cpb["coverage_branch_probe"])

    ebd = out["probes"]["elaborate_box_derefs"]
    print(
        "ElaborateBoxDerefs rc:",
        ebd["rc"],
        "BoxDerefTransmute:",
        ebd["uses_box_deref_transmute"],
        "Transmute:",
        ebd["uses_generic_transmute"],
        "Unique+NonNull:",
        ebd["uses_unique_nonnull_chain"],
        "VarDebugNotNull:",
        ebd["var_debug_has_pattern_not_null"],
    )
    print("  var_debug_before:", ebd["var_debug_before_lines"])
    print("  var_debug_after :", ebd["var_debug_after_lines"])

    mb = out["probes"]["miri_box_deref"]
    print(
        "Miri Box ok (native/SB/TB):",
        mb["native_ok"]["stdout"],
        mb["miri_stacked_borrows_ok"]["stdout"],
        mb["miri_tree_borrows_ok"]["stdout"],
        "UB dangling:",
        mb["miri_dangling_box_ub"]["detected_ub"],
        "UB unaligned:",
        mb["miri_unaligned_box_ub"]["detected_ub"],
        "Raw-deref discriminator:",
        mb["miri_box_transmute_raw_deref_discriminator"]["rc"],
        mb["miri_box_transmute_raw_deref_discriminator"]["stdout"],
        mb["miri_box_transmute_raw_deref_discriminator"]["detected_ub"],
    )

    cmr = out["probes"]["check_mut_restriction"]
    print("CheckMutRestriction status:", cmr["status"], "all_matched:", cmr["all_expectations_matched"])

    cg = out["probes"]["call_guards_and_landing_pads"]
    print("CallGuards rc_unwind:", cg["rc_unwind"], "rc_abort:", cg["rc_abort"])
    for fn, info in cg["functions"].items():
        u_lp = [(x["cleanup_before"], x["cleanup_after"]) for x in info["unwind_remove_noop_lp"]]
        u_cg = [(x["bb_before"], x["bb_after"], x["split_delta"]) for x in info["unwind_add_call_guards"]]
        a_cg = [(x["bb_before"], x["bb_after"], x["split_delta"]) for x in info["abort_add_call_guards"]]
        print(f"  {fn}: unwind_lp={u_lp} unwind_cg={u_cg} abort_lp_runs={len(info['abort_remove_noop_lp'])} abort_cg={a_cg}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
