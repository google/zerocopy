#!/usr/bin/env python3
"""Live rustc + Miri differential probe for:
  1. SingleUseConsts (DeadLocal & non-dominating uninit UB erasure under -Zmir-preserve-ub=yes,
     -Zmir-preserve-ub=yes unenforced mir-opt-level=0 claim, VarDebugInfo rewriting)
  2. MatchBranchSimplification (indirect *null_ptr discriminant UB erasure under -Zmir-preserve-ub=yes,
     plus all 5 unification arms: identical_stmts, unify_if_equal_const, unify_by_eq_op,
     unify_by_int_to_int positive/negative can_cast, unify_by_copy)
  3. SimplifyConstCondition (Assume(false) MirPatch::apply bb.statements.clear() prior-UB wipe,
     SwitchInt/passing-Assert folding, failing-Assert non-folding, immediate-predecessor has_place_const)
  4. CostChecker (single-call +25 bonus vs two-call inlining cliff, intrinsic INSTR_COST=5 exemption,
     RuntimeChecks::UbChecks +25 bonus, optional overflow-check +20 delta, exact threshold cliffs)

Usage:
  python3 probe_match_branches_simplify_single_use_consts_and_cost.py [--out probe_results.json]
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _find_rustc() -> str:
    rustc = os.environ.get("RUSTC") or shutil.which("rustc")
    if not rustc:
        raise RuntimeError("rustc not found in PATH or RUSTC env var")
    return rustc


def _find_miri(rustc: str) -> tuple[str, str]:
    sysroot = subprocess.check_output([rustc, "--print", "sysroot"], text=True).strip()
    miri_bin = os.environ.get("MIRI") or str(Path(sysroot) / "bin" / "miri")
    if not Path(miri_bin).is_file():
        raise RuntimeError(f"miri binary not found at {miri_bin}")
    miri_sysroot = os.environ.get("MIRI_SYSROOT")
    if not miri_sysroot:
        cargo = shutil.which("cargo")
        if cargo:
            res = subprocess.run(
                [cargo, "miri", "setup", "--print-sysroot"],
                capture_output=True,
                text=True,
                check=False,
            )
            if res.returncode == 0 and res.stdout.strip():
                miri_sysroot = res.stdout.strip()
    if not miri_sysroot or not Path(miri_sysroot).is_dir():
        raise RuntimeError("Unable to locate Miri sysroot; run `cargo miri setup` first.")
    return miri_bin, miri_sysroot


def _sanitize_text(text: str, tmpdir: Path) -> str:
    s = text.replace(str(tmpdir), "<TMPDIR>")
    # Strip any absolute home directory prefixes that could appear in diagnostics.
    s = re.sub(r"/(?:home|Users|usr/local/google/home)/[^/\s:]+", "<HOME>", s)
    return s.strip()


def _extract_ub_summary(stderr: str, tmpdir: Path) -> str:
    lines = _sanitize_text(stderr, tmpdir).splitlines()
    picked: list[str] = []
    for line in lines:
        if (
            line.startswith("error: Undefined Behavior:")
            or "Undefined Behavior occurred here" in line
            or line.startswith("warning: You have explicitly enabled MIR optimizations")
        ):
            picked.append(line)
    return "\n".join(picked)


def _run_miri(
    miri_bin: str,
    miri_sysroot: str,
    src_path: Path,
    extra_flags: list[str],
    tmpdir: Path,
) -> dict[str, Any]:
    cmd = [
        miri_bin,
        "--edition=2021",
        "--sysroot",
        miri_sysroot,
        *extra_flags,
        str(src_path),
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
    return {
        "flags": extra_flags,
        "rc": proc.returncode,
        "stdout": _sanitize_text(proc.stdout, tmpdir),
        "ub_summary": _extract_ub_summary(proc.stderr, tmpdir),
        "has_miri_opt_warning": "You have explicitly enabled MIR optimizations" in proc.stderr,
    }


def _run_rustc(
    rustc: str,
    src_path: Path,
    out_path: Path,
    extra_flags: list[str],
    tmpdir: Path,
) -> dict[str, Any]:
    cmd = [
        rustc,
        "--edition=2021",
        "--crate-type=lib",
        *extra_flags,
        str(src_path),
        "-o",
        str(out_path),
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        raise RuntimeError(
            f"rustc failed (rc={proc.returncode}): {' '.join(extra_flags)}\n{proc.stderr}"
        )
    return {
        "flags": extra_flags,
        "rc": proc.returncode,
        "stderr": _sanitize_text(proc.stderr, tmpdir),
    }


def _read_single_glob(directory: Path, pattern: str) -> str:
    matches = sorted(directory.glob(pattern))
    if not matches:
        raise RuntimeError(f"Expected MIR dump matching {pattern!r} in {directory}")
    return matches[0].read_text(encoding="utf-8")


def _probe_single_use_consts(
    rustc: str, miri_bin: str, miri_sysroot: str, tmpdir: Path
) -> dict[str, Any]:
    # 1A: DeadLocal UB erasure
    dead_local_src = tmpdir / "p1a_dead_local.rs"
    dead_local_src.write_text(
        """#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
#[inline(never)]
pub fn dead_local_const() -> u32 {
    mir! {
        let x: u32;
        {
            StorageLive(x);
            x = 77_u32;
            StorageDead(x);
            RET = x;
            Return()
        }
    }
}

fn main() {
    println!("DEAD_LOCAL={}", dead_local_const());
}
""",
        encoding="utf-8",
    )

    # 1B: Non-dominating uninitialized memory UB erasure
    nondom_src = tmpdir / "p1b_nondom.rs"
    nondom_src.write_text(
        """#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
#[inline(never)]
fn nondom_uninit_const(take_init: bool) -> u32 {
    mir! {
        let x: u32;
        {
            StorageLive(x);
            match take_init {
                true => bb_init,
                _ => bb_use,
            }
        }
        bb_init = {
            x = 88_u32;
            Goto(bb_use)
        }
        bb_use = {
            RET = x;
            StorageDead(x);
            Return()
        }
    }
}

fn main() {
    let take_init = core::hint::black_box(false);
    println!("NONDOM={}", nondom_uninit_const(take_init));
}
""",
        encoding="utf-8",
    )

    # 1C: -Zmir-preserve-ub=yes alone (without -Zmir-opt-level=0) still runs SingleUseConsts!
    preserve_alone_dir = tmpdir / "d_preserve_alone"
    preserve_alone_dir.mkdir()
    _run_rustc(
        rustc,
        dead_local_src,
        tmpdir / "lib_preserve_alone.rlib",
        [
            "-Zmir-preserve-ub=yes",
            "-Zdump-mir=dead_local_const",
            f"-Zdump-mir-dir={preserve_alone_dir}",
        ],
        tmpdir,
    )
    preserve_alone_passes = sorted(p.name for p in preserve_alone_dir.glob("*.after.mir"))
    preserve_alone_opt_mir = _read_single_glob(
        preserve_alone_dir, "*dead_local_const*runtime-optimized.after.mir"
    )

    # 1D: VarDebugInfoContents::Place -> Const & never-used const removal
    debug_src = tmpdir / "p1d_debug.rs"
    debug_src.write_text(
        """#[no_mangle]
pub fn suc_debug(x: u32) -> u32 {
    let single = 42_u32;
    let _unused = 99_u32;
    x.wrapping_add(single)
}
""",
        encoding="utf-8",
    )
    dbg_dir = tmpdir / "d_suc_debug"
    dbg_dir.mkdir()
    _run_rustc(
        rustc,
        debug_src,
        tmpdir / "lib_suc_debug.rlib",
        [
            "-Cdebuginfo=2",
            "-Zmir-opt-level=0",
            "-Zmir-enable-passes=+SingleUseConsts",
            "-Zdump-mir=suc_debug",
            f"-Zdump-mir-dir={dbg_dir}",
        ],
        tmpdir,
    )
    dbg_before = _read_single_glob(dbg_dir, "*suc_debug*SingleUseConsts.before.mir")
    dbg_after = _read_single_glob(dbg_dir, "*suc_debug*SingleUseConsts.after.mir")

    return {
        "dead_local_ub_erasure": {
            "mir_opt_0_preserve_ub": _run_miri(
                miri_bin, miri_sysroot, dead_local_src,
                ["-Zmir-opt-level=0", "-Zmir-preserve-ub=yes"], tmpdir,
            ),
            "mir_opt_1_preserve_ub": _run_miri(
                miri_bin, miri_sysroot, dead_local_src,
                ["-Zmir-opt-level=1", "-Zmir-preserve-ub=yes"], tmpdir,
            ),
            "isolated_single_use_consts_at_opt_0": _run_miri(
                miri_bin, miri_sysroot, dead_local_src,
                ["-Zmir-opt-level=0", "-Zmir-preserve-ub=yes", "-Zmir-enable-passes=+SingleUseConsts"],
                tmpdir,
            ),
        },
        "non_dominating_uninit_ub_erasure": {
            "mir_opt_0_preserve_ub": _run_miri(
                miri_bin, miri_sysroot, nondom_src,
                ["-Zmir-opt-level=0", "-Zmir-preserve-ub=yes"], tmpdir,
            ),
            "mir_opt_1_preserve_ub": _run_miri(
                miri_bin, miri_sysroot, nondom_src,
                ["-Zmir-opt-level=1", "-Zmir-preserve-ub=yes"], tmpdir,
            ),
            "isolated_single_use_consts_at_opt_0": _run_miri(
                miri_bin, miri_sysroot, nondom_src,
                ["-Zmir-opt-level=0", "-Zmir-preserve-ub=yes", "-Zmir-enable-passes=+SingleUseConsts"],
                tmpdir,
            ),
        },
        "mir_preserve_ub_alone_does_not_imply_opt_0": {
            "ran_single_use_consts": any("SingleUseConsts.after.mir" in n for n in preserve_alone_passes),
            "ran_simplify_const_condition": any(
                "SimplifyConstCondition" in n for n in preserve_alone_passes
            ),
            "optimized_mir_erased_dead_read_to_const_77": (
                "_0 = const 77_u32;" in preserve_alone_opt_mir
                and "StorageDead" not in preserve_alone_opt_mir
            ),
            "optimized_mir_excerpt": preserve_alone_opt_mir.strip(),
        },
        "var_debug_info_rewrite": {
            "before_has_place_single": "debug single => _2;" in dbg_before,
            "before_has_place_unused": "debug _unused => _3;" in dbg_before,
            "after_has_const_single": "debug single => const 42_u32;" in dbg_after,
            "after_has_const_unused": "debug _unused => const 99_u32;" in dbg_after,
            "after_has_propagated_operand": "_5 = const 42_u32;" in dbg_after,
            "after_nop_count": dbg_after.count("nop;"),
        },
    }


def _probe_match_branch_simplification(
    rustc: str, miri_bin: str, miri_sysroot: str, tmpdir: Path
) -> dict[str, Any]:
    # 2A: Pure surface Rust indirect *null_ptr discriminant UB erasure
    null_discr_src = tmpdir / "p2a_mbs_null.rs"
    null_discr_src.write_text(
        """#[inline(never)]
unsafe fn mbs_null_surface(p: *const u8) -> u32 {
    match *p {
        0 => 99_u32,
        _ => 99_u32,
    }
}

fn main() {
    let p: *const u8 = core::hint::black_box(core::ptr::null());
    println!("MBS_NULL={}", unsafe { mbs_null_surface(p) });
}
""",
        encoding="utf-8",
    )

    # 2B: All 5 unification arms in MIR dumps
    arms_src = tmpdir / "p2b_arms.rs"
    arms_src.write_text(
        """#[repr(u8)]
#[derive(Copy, Clone)]
pub enum Tri { A = 1, B = 2, C = 3 }

#[repr(i8)]
#[derive(Copy, Clone)]
pub enum SignedNeg { NegOne = -1, Zero = 0, One = 1 }

#[derive(Clone, Copy)]
pub enum Foo { A(u32), B }

#[no_mangle]
pub unsafe fn arm1_identical(p: *const u8) -> u32 {
    match *p { 0 => 99, _ => 99 }
}

#[no_mangle]
pub fn arm3_eq_op(x: u32) -> bool {
    match x { 42 => true, _ => false }
}

#[no_mangle]
pub fn arm3_ne_enum(x: Tri) -> bool {
    match x { Tri::A => false, Tri::B => true, Tri::C => true }
}

#[no_mangle]
pub fn arm4_int_to_int_ok(x: Tri) -> i16 {
    match x { Tri::A => 1_i16, Tri::B => 2_i16, Tri::C => 3_i16 }
}

#[no_mangle]
pub fn arm4_int_to_int_fail(x: SignedNeg) -> u16 {
    // Signed -1_i8 sign-extends to 0xFFFF_u16 (65535), NOT 255_u16; can_cast must reject.
    match x { SignedNeg::NegOne => 255_u16, SignedNeg::Zero => 0_u16, SignedNeg::One => 1_u16 }
}

#[no_mangle]
pub fn arm5_unify_by_copy(a: &Foo) -> Foo {
    match a {
        Foo::A(x) => Foo::A(*x),
        Foo::B => Foo::B,
    }
}
""",
        encoding="utf-8",
    )
    arms_dir = tmpdir / "d_mbs_arms"
    arms_dir.mkdir()
    _run_rustc(
        rustc,
        arms_src,
        tmpdir / "lib_mbs_arms.rlib",
        ["-O", "-Zmir-opt-level=2", "-Zdump-mir=arm", f"-Zdump-mir-dir={arms_dir}"],
        tmpdir,
    )

    # Arm 2 isolated (const { 5 + 5 } stays Const::Unevaluated before MBS when GVN is off)
    arm2_src = tmpdir / "p2b_arm2.rs"
    arm2_src.write_text(
        """#[no_mangle]
pub fn arm2_equal_const(x: u8) -> u32 {
    match x {
        0 => 10_u32,
        _ => const { 5_u32 + 5_u32 },
    }
}
""",
        encoding="utf-8",
    )
    arm2_dir = tmpdir / "d_mbs_arm2"
    arm2_dir.mkdir()
    _run_rustc(
        rustc,
        arm2_src,
        tmpdir / "lib_mbs_arm2.rlib",
        [
            "-Zmir-opt-level=0",
            "-Zmir-enable-passes=+MatchBranchSimplification",
            "-Zdump-mir=arm2_equal_const",
            f"-Zdump-mir-dir={arm2_dir}",
        ],
        tmpdir,
    )

    def _mbs_pair(d: Path, fn_name: str) -> tuple[str, str]:
        return (
            _read_single_glob(d, f"*{fn_name}*MatchBranchSimplification.before.mir"),
            _read_single_glob(d, f"*{fn_name}*MatchBranchSimplification.after.mir"),
        )

    a1_b, a1_a = _mbs_pair(arms_dir, "arm1_identical")
    a2_b, a2_a = _mbs_pair(arm2_dir, "arm2_equal_const")
    a3e_b, a3e_a = _mbs_pair(arms_dir, "arm3_eq_op")
    a3n_b, a3n_a = _mbs_pair(arms_dir, "arm3_ne_enum")
    a4ok_b, a4ok_a = _mbs_pair(arms_dir, "arm4_int_to_int_ok")
    a4no_b, a4no_a = _mbs_pair(arms_dir, "arm4_int_to_int_fail")
    a5_b, a5_a = _mbs_pair(arms_dir, "arm5_unify_by_copy")

    return {
        "indirect_null_discr_ub_erasure": {
            "mir_opt_0_preserve_ub": _run_miri(
                miri_bin, miri_sysroot, null_discr_src,
                ["-Zmir-opt-level=0", "-Zmir-preserve-ub=yes"], tmpdir,
            ),
            "mir_opt_2_preserve_ub": _run_miri(
                miri_bin, miri_sysroot, null_discr_src,
                ["-Zmir-opt-level=2", "-Zmir-preserve-ub=yes"], tmpdir,
            ),
            "isolated_mbs_at_opt_0": _run_miri(
                miri_bin, miri_sysroot, null_discr_src,
                [
                    "-Zmir-opt-level=0",
                    "-Zmir-preserve-ub=yes",
                    "-Zmir-enable-passes=+MatchBranchSimplification",
                ],
                tmpdir,
            ),
        },
        "five_unification_arms": {
            "arm1_identical_stmts": {
                "before_has_switch_deref": "switchInt(copy (*_1))" in a1_b,
                "after_drops_deref_and_no_placemention": (
                    "(*_1)" not in a1_a
                    and "PlaceMention" not in a1_a
                    and "_0 = const 99_u32;" in a1_a
                ),
            },
            "arm2_unify_if_equal_const": {
                "before_has_unevaluated_const": "constant#0" in a2_b,
                "after_emits_no_retag_const": "_0 = no_retag const 10_u32;" in a2_a,
                "after_drops_switch": "switchInt" not in a2_a,
            },
            "arm3_unify_by_eq_op": {
                "eq_before_has_switch": "switchInt(copy _1) -> [42:" in a3e_b,
                "eq_after_has_discr_local_and_eq": (
                    "no_retag copy _1;" in a3e_a and "Eq(copy _2, const 42_u32);" in a3e_a
                ),
                "ne_enum_before_has_unreachable_otherwise": "unreachable;" in a3n_b,
                "ne_enum_after_erases_unreachable_and_emits_ne": (
                    "unreachable;" not in a3n_a and "Ne(copy _3, const 1_u8);" in a3n_a
                ),
            },
            "arm4_unify_by_int_to_int": {
                "ok_before_has_unreachable_otherwise": "unreachable;" in a4ok_b,
                "ok_after_emits_int_to_int_cast": (
                    "as i16 (IntToInt);" in a4ok_a and "unreachable;" not in a4ok_a
                ),
                "fail_signed_truncation_unchanged": (
                    "switchInt" in a4no_a and "(IntToInt)" not in a4no_a
                ),
            },
            "arm5_unify_by_copy": {
                "before_has_discriminant_and_enum_const": (
                    "_2 = discriminant((*_1));" in a5_b and "const Foo::B" in a5_b
                ),
                "after_emits_no_retag_copy_deref": (
                    "_0 = no_retag copy (*_1);" in a5_a and "switchInt" not in a5_a
                ),
            },
        },
    }


def _probe_simplify_const_condition(
    rustc: str, miri_bin: str, miri_sysroot: str, tmpdir: Path
) -> dict[str, Any]:
    # 3A: Assume(false) wipes prior null-pointer dereference via MirPatch::apply bb.statements.clear()
    assume_src = tmpdir / "p3a_assume_wipe.rs"
    assume_src.write_text(
        """#![feature(core_intrinsics)]

#[inline(never)]
pub unsafe fn assume_false_wipe(p: *const u32) -> u32 {
    let v = *p;
    core::intrinsics::assume(false);
    v
}

fn main() {
    let p: *const u32 = core::hint::black_box(core::ptr::null());
    println!("ASSUME={}", unsafe { assume_false_wipe(p) });
}
""",
        encoding="utf-8",
    )

    assume_dump = tmpdir / "d_assume_wipe"
    assume_dump.mkdir()
    _run_rustc(
        rustc,
        assume_src,
        tmpdir / "lib_assume_wipe.rlib",
        [
            "-Zmir-opt-level=0",
            "-Zmir-enable-passes=+SimplifyConstCondition-after-inst-simplify",
            "-Zdump-mir=assume_false_wipe",
            f"-Zdump-mir-dir={assume_dump}",
        ],
        tmpdir,
    )
    aw_before = _read_single_glob(
        assume_dump, "*assume_false_wipe*SimplifyConstCondition-after-inst-simplify.before.mir"
    )
    aw_after = _read_single_glob(
        assume_dump, "*assume_false_wipe*SimplifyConstCondition-after-inst-simplify.after.mir"
    )

    # 3B: SwitchInt, immediate-predecessor has_place_const, passing Assert vs failing Assert
    scc_src = tmpdir / "p3b_scc.rs"
    scc_src.write_text(
        """#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
#[no_mangle]
pub fn scc_switch_immediate() -> u32 {
    mir! {
        let c: u8;
        {
            c = 1_u8;
            match c {
                0 => bb0,
                1 => bb1,
                _ => bb2,
            }
        }
        bb0 = { RET = 10_u32; Return() }
        bb1 = { RET = 20_u32; Return() }
        bb2 = { RET = 30_u32; Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
#[no_mangle]
pub fn scc_switch_intervening() -> u32 {
    mir! {
        let c: u8;
        let other: u32;
        {
            c = 1_u8;
            other = 0_u32;
            match c {
                0 => bb0,
                1 => bb1,
                _ => bb2,
            }
        }
        bb0 = { RET = 10_u32; Return() }
        bb1 = { RET = 20_u32; Return() }
        bb2 = { RET = 30_u32; Return() }
    }
}

#[no_mangle]
pub fn scc_assert_pass(x: u32) -> u32 {
    x / 1
}

#[allow(unconditional_panic)]
#[no_mangle]
pub fn scc_assert_fail(x: u32) -> u32 {
    x / 0
}
""",
        encoding="utf-8",
    )
    scc_dir = tmpdir / "d_scc"
    scc_dir.mkdir()
    _run_rustc(
        rustc,
        scc_src,
        tmpdir / "lib_scc.rlib",
        [
            "-Zmir-opt-level=0",
            "-Zmir-enable-passes=+DataflowConstProp,+SimplifyConstCondition-after-const-prop",
            "-Zdump-mir=scc_",
            f"-Zdump-mir-dir={scc_dir}",
        ],
        tmpdir,
    )

    def _scc_pair(fn_name: str) -> tuple[str, str]:
        return (
            _read_single_glob(
                scc_dir, f"*{fn_name}*SimplifyConstCondition-after-const-prop.before.mir"
            ),
            _read_single_glob(
                scc_dir, f"*{fn_name}*SimplifyConstCondition-after-const-prop.after.mir"
            ),
        )

    sw_i_b, sw_i_a = _scc_pair("scc_switch_immediate")
    sw_n_b, sw_n_a = _scc_pair("scc_switch_intervening")
    ap_b, ap_a = _scc_pair("scc_assert_pass")
    af_b, af_a = _scc_pair("scc_assert_fail")

    # Also test scc_switch_intervening WITHOUT DataflowConstProp (pure SimplifyConstCondition)
    scc_iso_dir = tmpdir / "d_scc_iso"
    scc_iso_dir.mkdir()
    _run_rustc(
        rustc,
        scc_src,
        tmpdir / "lib_scc_iso.rlib",
        [
            "-Zmir-opt-level=0",
            "-Zmir-enable-passes=+SimplifyConstCondition-after-inst-simplify",
            "-Zdump-mir=scc_switch_",
            f"-Zdump-mir-dir={scc_iso_dir}",
        ],
        tmpdir,
    )
    sw_iso_imm_a = _read_single_glob(
        scc_iso_dir, "*scc_switch_immediate*SimplifyConstCondition-after-inst-simplify.after.mir"
    )
    sw_iso_int_a = _read_single_glob(
        scc_iso_dir, "*scc_switch_intervening*SimplifyConstCondition-after-inst-simplify.after.mir"
    )

    return {
        "assume_false_wipes_prior_ub": {
            "mir_opt_0_preserve_ub": _run_miri(
                miri_bin, miri_sysroot, assume_src,
                ["-Zmir-opt-level=0", "-Zmir-preserve-ub=yes"], tmpdir,
            ),
            "mir_opt_1_preserve_ub": _run_miri(
                miri_bin, miri_sysroot, assume_src,
                ["-Zmir-opt-level=1", "-Zmir-preserve-ub=yes"], tmpdir,
            ),
            "isolated_scc_at_opt_0": _run_miri(
                miri_bin, miri_sysroot, assume_src,
                [
                    "-Zmir-opt-level=0",
                    "-Zmir-preserve-ub=yes",
                    "-Zmir-enable-passes=+SimplifyConstCondition-after-inst-simplify",
                ],
                tmpdir,
            ),
            "mir_before_has_deref_and_assume": (
                "(*_1)" in aw_before and "assume(const false)" in aw_before
            ),
            "mir_after_clears_all_stmts_to_unreachable": (
                "(*_1)" not in aw_after
                and "assume(" not in aw_after
                and "unreachable;" in aw_after
            ),
        },
        "immediate_predecessor_has_place_const": {
            "immediate_switch_folded_to_goto": (
                "goto -> bb2;" in sw_iso_imm_a and "switchInt" not in sw_iso_imm_a
            ),
            "intervening_stmt_switch_not_folded": "switchInt(copy _1)" in sw_iso_int_a,
        },
        "assert_folding_asymmetry": {
            "passing_assert_before": "assert(!const false," in ap_b,
            "passing_assert_folded_to_goto": "goto -> bb1;" in ap_a and "assert(" not in ap_a,
            "failing_assert_before": "assert(!const true," in af_b,
            "failing_assert_preserved_not_unreachable": (
                "assert(!const true," in af_a and "unreachable;" not in af_a
            ),
        },
    }


def _probe_cost_checker(rustc: str, tmpdir: Path) -> dict[str, Any]:
    cost_src = tmpdir / "p4_cost.rs"
    cost_src.write_text(
        """#![feature(core_intrinsics)]

#[inline(never)]
#[no_mangle]
pub fn ext_leaf(x: u32) -> u32 {
    x ^ 0x9E37_79B9
}

// 22 Assigns (110) + 1 Call (25) - single-call bonus (25) = cost 110.
// 2 basic blocks (<= 3): default hint_threshold=100 -> effective 125 => INLINED.
#[inline]
pub fn one_call_under_bonus(x: u32) -> u32 {
    let a0 = x ^ 1; let a1 = a0 ^ 2; let a2 = a1 ^ 3; let a3 = a2 ^ 4;
    let a4 = a3 ^ 5; let a5 = a4 ^ 6; let a6 = a5 ^ 7; let a7 = a6 ^ 8;
    let a8 = a7 ^ 9; let a9 = a8 ^ 10; let a10 = a9 ^ 11; let a11 = a10 ^ 12;
    let a12 = a11 ^ 13; let a13 = a12 ^ 14; let a14 = a13 ^ 15; let a15 = a14 ^ 16;
    let a16 = a15 ^ 17; let a17 = a16 ^ 18; let a18 = a17 ^ 19; let a19 = a18 ^ 20;
    let r = ext_leaf(a19);
    r ^ a0 ^ a1
}

// 21 Assigns (105) + 2 Calls (50) - 0 bonus = cost 155 > 125 => NOT INLINED at default T=100.
#[inline]
pub fn two_calls_no_bonus(x: u32) -> u32 {
    let a0 = x ^ 1; let a1 = a0 ^ 2; let a2 = a1 ^ 3; let a3 = a2 ^ 4;
    let a4 = a3 ^ 5; let a5 = a4 ^ 6; let a6 = a5 ^ 7; let a7 = a6 ^ 8;
    let a8 = a7 ^ 9; let a9 = a8 ^ 10; let a10 = a9 ^ 11; let a11 = a10 ^ 12;
    let a12 = a11 ^ 13; let a13 = a12 ^ 14; let a14 = a13 ^ 15; let a15 = a14 ^ 16;
    let a16 = a15 ^ 17; let a17 = a16 ^ 18; let a18 = a17 ^ 19;
    let r1 = ext_leaf(a18);
    let r2 = ext_leaf(r1);
    r2 ^ a0 ^ a1
}

// Same 2-call shape as two_calls_no_bonus, using intrinsic ctpop (INSTR_COST=5 each):
// 21 Assigns (105) + 2 * 5 (10) = cost 115 <= 125 => INLINED at default T=100.
#[inline]
pub fn two_intrinsics_exempt(x: u32) -> u32 {
    let a0 = x ^ 1; let a1 = a0 ^ 2; let a2 = a1 ^ 3; let a3 = a2 ^ 4;
    let a4 = a3 ^ 5; let a5 = a4 ^ 6; let a6 = a5 ^ 7; let a7 = a6 ^ 8;
    let a8 = a7 ^ 9; let a9 = a8 ^ 10; let a10 = a9 ^ 11; let a11 = a10 ^ 12;
    let a12 = a11 ^ 13; let a13 = a12 ^ 14; let a14 = a13 ^ 15; let a15 = a14 ^ 16;
    let a16 = a15 ^ 17; let a17 = a16 ^ 18; let a18 = a17 ^ 19;
    let r1 = core::intrinsics::ctpop(a18);
    let r2 = core::intrinsics::ctpop(r1);
    r2 ^ a0 ^ a1
}

#[no_mangle]
pub fn caller_one(x: u32) -> u32 { one_call_under_bonus(x) }
#[no_mangle]
pub fn caller_two(x: u32) -> u32 { two_calls_no_bonus(x) }
#[no_mangle]
pub fn caller_intrinsics(x: u32) -> u32 { two_intrinsics_exempt(x) }
""",
        encoding="utf-8",
    )

    def _run_cost_at_threshold(t: int | None) -> dict[str, Any]:
        d = tmpdir / f"d_cost_{t if t is not None else 'default'}"
        d.mkdir()
        flags = ["-O", "-Zmir-opt-level=2", "-Zdump-mir=caller_", f"-Zdump-mir-dir={d}"]
        if t is not None:
            flags.append(f"-Zinline-mir-hint-threshold={t}")
        _run_rustc(rustc, cost_src, tmpdir / f"lib_cost_{t}.rlib", flags, tmpdir)
        out: dict[str, Any] = {}
        for caller in ("caller_one", "caller_two", "caller_intrinsics"):
            fi = _read_single_glob(d, f"*{caller}*ForceInline.after.mir")
            inl = _read_single_glob(d, f"*{caller}*3-2-004.Inline.after.mir")
            out[caller] = {
                "force_inline_after_inlined": "inlined " in fi,
                "inline_after_inlined": "inlined " in inl,
                "inline_after_has_ext_leaf": "ext_leaf(" in inl,
                "inline_after_has_ctpop": "ctpop::" in inl,
            }
        return out

    default_res = _run_cost_at_threshold(None)
    cliff_sweep = {
        str(t): {
            "eff_threshold_le_3bb": t + (t // 4),
            "caller_one_inlined": r["caller_one"]["inline_after_inlined"],
            "caller_intrinsics_inlined": r["caller_intrinsics"]["inline_after_inlined"],
            "caller_two_inlined": r["caller_two"]["inline_after_inlined"],
        }
        for t in (87, 88, 91, 92, 100, 123, 124)
        for r in (_run_cost_at_threshold(t),)
    }

    # RuntimeChecks::UbChecks (+25 bonus) + optional overflow-check (+20 delta) cross-crate probe
    dep_src = tmpdir / "p4_dep.rs"
    dep_src.write_text(
        """#![feature(core_intrinsics)]

#[inline(never)]
#[no_mangle]
pub fn ext_leaf(x: u32) -> u32 { x ^ 0x9E37_79B9 }

#[inline]
pub fn ub_dep_fn(x: u32, y: u32) -> u32 {
    let a0 = x ^ 1; let a1 = a0 ^ 2; let a2 = a1 ^ 3; let a3 = a2 ^ 4;
    let a4 = a3 ^ 5; let a5 = a4 ^ 6; let a6 = a5 ^ 7; let a7 = a6 ^ 8;
    let a8 = a7 ^ 9; let a9 = a8 ^ 10; let a10 = a9 ^ 11; let a11 = a10 ^ 12;
    if core::intrinsics::ub_checks() {
        let r1 = ext_leaf(a11);
        ext_leaf(r1)
    } else {
        a11 ^ y
    }
}

#[inline]
pub fn ovf_dep_fn(x: u32, y: u32) -> u32 {
    // 4 blocks (>3) or 2 blocks: AssertKind::Overflow(Add) incurs INSTR_COST=5 when
    // !preserve_debug && !overflow_checks vs CALL_PENALTY=25 when preserve_debug=true (+20 delta).
    let a = x + y;
    let b = a + 1;
    let c = b + 2;
    c + 3
}
""",
        encoding="utf-8",
    )
    dep_rlib = tmpdir / "libp4_dep.rlib"
    # Compile dep with -Zmir-opt-level=0 -Coverflow-checks=yes so both RuntimeChecks::UbChecks
    # and AssertKind::Overflow(Add) remain present in encoded optimized_mir.
    _run_rustc(
        rustc,
        dep_src,
        dep_rlib,
        ["-Zmir-opt-level=0", "-Coverflow-checks=yes"],
        tmpdir,
    )
    user_src = tmpdir / "p4_user.rs"
    user_src.write_text(
        """extern crate p4_dep;
#[no_mangle]
pub fn call_ub_dep(x: u32, y: u32) -> u32 { p4_dep::ub_dep_fn(x, y) }
#[no_mangle]
pub fn call_ovf_dep(x: u32, y: u32) -> u32 { p4_dep::ovf_dep_fn(x, y) }
""",
        encoding="utf-8",
    )

    def _first_inline_threshold(fn_name: str, preserve_debug: str, lo: int, hi: int) -> int:
        # Binary search exact minimum hint_threshold T (for >3-block callees, eff == T).
        while lo < hi:
            mid = (lo + hi) // 2
            d = tmpdir / f"d_bs_{fn_name}_{preserve_debug}_{mid}"
            d.mkdir(exist_ok=True)
            _run_rustc(
                rustc,
                user_src,
                tmpdir / f"lib_u_{fn_name}_{preserve_debug}_{mid}.rlib",
                [
                    "-O",
                    "-Zmir-opt-level=2",
                    f"-Zinline-mir-preserve-debug={preserve_debug}",
                    f"-Zinline-mir-hint-threshold={mid}",
                    f"--extern=p4_dep={dep_rlib}",
                    f"-Zdump-mir={fn_name}",
                    f"-Zdump-mir-dir={d}",
                ],
                tmpdir,
            )
            inl = _read_single_glob(d, f"*{fn_name}*3-2-004.Inline.after.mir")
            if "inlined " in inl:
                hi = mid
            else:
                lo = mid + 1
        return lo

    ub_t_no = _first_inline_threshold("call_ub_dep", "no", 100, 260)
    ub_t_yes = _first_inline_threshold("call_ub_dep", "yes", 100, 260)
    ovf_t_no = _first_inline_threshold("call_ovf_dep", "no", 20, 260)
    ovf_t_yes = _first_inline_threshold("call_ovf_dep", "yes", 20, 260)

    return {
        "default_hint_threshold_100": default_res,
        "exact_threshold_cliff_sweep": cliff_sweep,
        "runtime_checks_ub_checks_bonus": {
            "preserve_debug_no_min_threshold": ub_t_no,
            "preserve_debug_yes_min_threshold": ub_t_yes,
            "observed_delta": ub_t_yes - ub_t_no,
            "expected_delta_call_penalty": 25,
        },
        "optional_overflow_check_delta": {
            "overflow_asserts_count": 4,
            "preserve_debug_no_min_threshold": ovf_t_no,
            "preserve_debug_yes_min_threshold": ovf_t_yes,
            "observed_delta": ovf_t_yes - ovf_t_no,
            "expected_delta_4x20": 80,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, help="Optional output JSON file path")
    args = parser.parse_args()

    rustc = _find_rustc()
    miri_bin, miri_sysroot = _find_miri(rustc)
    rustc_ver = subprocess.check_output([rustc, "--version", "--verbose"], text=True).strip()
    miri_ver = subprocess.check_output([miri_bin, "--version"], text=True).strip()

    with tempfile.TemporaryDirectory(prefix="probe_mbs_") as td:
        tmpdir = Path(td)
        results = {
            "rustc_version_verbose": rustc_ver,
            "miri_version": miri_ver,
            "single_use_consts": _probe_single_use_consts(rustc, miri_bin, miri_sysroot, tmpdir),
            "match_branch_simplification": _probe_match_branch_simplification(
                rustc, miri_bin, miri_sysroot, tmpdir
            ),
            "simplify_const_condition": _probe_simplify_const_condition(
                rustc, miri_bin, miri_sysroot, tmpdir
            ),
            "cost_checker": _probe_cost_checker(rustc, tmpdir),
        }

    rendered = json.dumps(results, indent=2, sort_keys=False) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
