#!/usr/bin/env python3
"""Empirical rustc + Miri + crate-scale probe for non-diverging MIR intrinsics.

Records machine-readable ground truth for `StatementKind::Intrinsic(
NonDivergingIntrinsic::{Assume, CopyNonOverlapping})` on the nightly toolchain
found on `PATH` (or `~/.cargo/bin`):

1. `LowerIntrinsics`: which `Call` terminators become `StatementKind::Intrinsic`
   statements (direct `core::intrinsics::{assume, copy_nonoverlapping,
   unreachable}` calls) and which stay `Call`s until `Inline` (the stable
   wrappers `core::hint::assert_unchecked`, `core::ptr::copy_nonoverlapping`,
   `core::hint::unreachable_unchecked`).
2. `UnreachableEnumBranching` and `UnreachablePropagation`: golden before/after
   blocks for every structural case of `remove_successors_from_switch`, each
   compared against an executable reference model of that function
   (`model_remove_successors`).
3. `CheckAlignment` / `CheckNull`: whether the MIR pointer-check passes
   instrument a `copy_nonoverlapping` statement (they do not; they instrument
   raw-pointer dereference places), plus a native debug-assertions run showing
   which checks the library wrapper performs.
4. A Miri operational matrix over `assume`, `copy_nonoverlapping` (null,
   misaligned, dangling, overlapping, uninitialized-overlapping, zero-sized and
   size-overflow operands) and `unreachable`, across three interpreter modes,
   plus the compile-time `invalid_null_arguments` lint row.
5. A Miri differential of the switch-pruning specimens at `-Zmir-opt-level=0`
   versus `-Zmir-opt-level=2`, including the degenerate zero-arm `SwitchInt`
   whose discriminant read `UnreachablePropagation` drops.
6. A whole-crate `google/zerocopy` census: `assume` / `copy_nonoverlapping`
   statements and `unreachable` terminators at `Runtime(PostCleanup)` and
   `Runtime(Optimized)`, a per-pass ledger over every dumped pass of the
   optimization pipeline, and an at-scale comparison of
   `model_remove_successors` with what `UnreachablePropagation` actually did
   to every reachable `SwitchInt` in the crate.

Usage:
    python3 probe_nondiverging_intrinsics.py --out probe_results.json \
        [--zerocopy-dir /path/to/zerocopy-checkout/zerocopy] [--skip-zerocopy]

The probe writes only inside a temporary directory and the `--out` file. All
absolute paths are scrubbed from the recorded output.
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
from pathlib import Path
from typing import Any

ZEROCOPY_COMMIT = "907b9175fee081872ec883ca4709e6ad922f8ed0"
ZEROCOPY_VERSION = "0.8.64"
ZEROCOPY_FEATURES = ["alloc", "simd"]
ZEROCOPY_REPOSITORY = "google/zerocopy"
ZEROCOPY_TARBALL_URL = (
    f"https://github.com/{ZEROCOPY_REPOSITORY}/archive/{ZEROCOPY_COMMIT}.tar.gz"
)

# ---------------------------------------------------------------------------
# Process helpers
# ---------------------------------------------------------------------------


def run_cmd(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 900,
) -> subprocess.CompletedProcess[str]:
    merged = os.environ.copy()
    if env:
        merged.update(env)
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=merged,
        text=True,
        capture_output=True,
        check=False,
        timeout=timeout,
    )


class Scrubber:
    """Replaces machine-specific absolute paths with stable placeholders."""

    def __init__(self) -> None:
        self.replacements: list[tuple[str, str]] = []

    def add(self, raw: str | Path, token: str) -> None:
        raw = str(raw)
        if raw and raw != "/":
            self.replacements.append((raw, token))
            self.replacements.sort(key=lambda item: -len(item[0]))

    def __call__(self, text: str) -> str:
        out = text
        for raw, token in self.replacements:
            out = out.replace(raw, token)
        out = re.sub(r"/(?:tmp)/[A-Za-z0-9_./-]+", "<TMP>", out)
        out = re.sub(r"/(?:home)/[^/\s\"']+", "<HOME>", out)
        return out


def resolve_toolchain() -> dict[str, Any]:
    rustc = shutil.which("rustc")
    if not rustc:
        fallback = Path.home() / ".cargo" / "bin" / "rustc"
        if not fallback.exists():
            raise RuntimeError("rustc not found on PATH or in ~/.cargo/bin")
        rustc = str(fallback)
    cargo = shutil.which("cargo") or str(Path(rustc).with_name("cargo"))
    sysroot_proc = run_cmd([rustc, "--print", "sysroot"])
    if sysroot_proc.returncode != 0:
        raise RuntimeError(f"rustc --print sysroot failed: {sysroot_proc.stderr}")
    sysroot = Path(sysroot_proc.stdout.strip())
    miri = sysroot / "bin" / "miri"
    if not miri.exists():
        raise RuntimeError(
            "miri not found in the toolchain sysroot; install the `miri` component"
        )
    miri_sysroot = os.environ.get("MIRI_SYSROOT")
    if not miri_sysroot:
        setup = run_cmd([cargo, "miri", "setup", "--print-sysroot"], timeout=1800)
        if setup.returncode != 0:
            raise RuntimeError(f"cargo miri setup failed: {setup.stderr[-2000:]}")
        miri_sysroot = setup.stdout.strip().splitlines()[-1]
    return {
        "rustc": rustc,
        "cargo": cargo,
        "sysroot": sysroot,
        "miri": str(miri),
        "miri_sysroot": miri_sysroot,
        "rustc_vv": run_cmd([rustc, "-vV"]).stdout.strip().splitlines(),
        "miri_version": run_cmd([str(miri), "--version"]).stdout.strip(),
    }


# ---------------------------------------------------------------------------
# MIR dump parsing
# ---------------------------------------------------------------------------

RE_BLOCK_START = re.compile(r"^\s*bb(\d+)(?: \(cleanup\))?: \{\s*$")
RE_BLOCK_END = re.compile(r"^\s*\}\s*$")
RE_ASSUME_STMT = re.compile(r"^\s*assume\((.*)\);")
RE_CNO_STMT = re.compile(r"^\s*copy_nonoverlapping\(dst = ")
RE_UNREACHABLE = re.compile(r"^\s*unreachable;")
RE_SWITCH = re.compile(r"^\s*switchInt\((.*?)\) -> (.*);\s*$")
RE_GOTO = re.compile(r"^\s*goto -> bb(\d+);")
RE_CALL = re.compile(r"^\s*[^=;]+ = [^;]*\) -> (?:\[return: |unwind )")
RE_ASSIGN = re.compile(r"^\s*(_\d+) = (.*);\s*$")
RE_BB_REF = re.compile(r"bb(\d+)")
RE_DUMP_NAME = re.compile(
    r"^(?P<crate>[^.]+)\.(?P<body>.+)\.(?P<index>\d+-\d+-\d+)\."
    r"(?P<pass>[A-Za-z0-9-]+)\.(?P<when>before|after)\.mir$"
)


def parse_blocks(text: str) -> dict[int, list[str]]:
    """Returns `{block index: [statement lines..., terminator line]}`."""
    blocks: dict[int, list[str]] = {}
    current: int | None = None
    for raw in text.splitlines():
        if current is None:
            start = RE_BLOCK_START.match(raw)
            if start:
                current = int(start.group(1))
                blocks[current] = []
            continue
        if RE_BLOCK_END.match(raw):
            current = None
            continue
        line = raw.strip()
        if line:
            blocks[current].append(line)
    return blocks


def count_constructs(text: str) -> dict[str, int]:
    counts = {
        "assume_stmts": 0,
        "copy_nonoverlapping_stmts": 0,
        "unreachable_terms": 0,
        "switch_int_terms": 0,
        "call_terms": 0,
    }
    for line in text.splitlines():
        if RE_ASSUME_STMT.match(line):
            counts["assume_stmts"] += 1
        elif RE_CNO_STMT.match(line):
            counts["copy_nonoverlapping_stmts"] += 1
        elif RE_UNREACHABLE.match(line):
            counts["unreachable_terms"] += 1
        elif RE_SWITCH.match(line):
            counts["switch_int_terms"] += 1
        elif RE_CALL.match(line):
            counts["call_terms"] += 1
    return counts


def parse_switch(line: str) -> tuple[str, list[tuple[int, int]], int] | None:
    """Parses `switchInt(D) -> [v: bbN, ..., otherwise: bbM];` (or `-> bbM;`)."""
    match = RE_SWITCH.match(line)
    if not match:
        return None
    discr, rhs = match.group(1), match.group(2).strip()
    if rhs.startswith("["):
        targets: list[tuple[int, int]] = []
        otherwise: int | None = None
        for part in rhs.strip("[]").split(","):
            key, _, block = part.strip().partition(": bb")
            if key == "otherwise":
                otherwise = int(block)
            else:
                targets.append((int(key), int(block)))
        if otherwise is None:
            return None
        return discr, targets, otherwise
    single = re.fullmatch(r"bb(\d+)", rhs)
    if single:
        return discr, [], int(single.group(1))
    return None


def model_remove_successors(
    targets: list[tuple[int, int]],
    otherwise: int,
    unreachable: set[int],
) -> dict[str, Any]:
    """Executable reference model of `remove_successors_from_switch`.

    Mirrors `compiler/rustc_mir_transform/src/unreachable_prop.rs`: unreachable
    valued arms are dropped; while `otherwise` is reachable each dropped arm
    records `assume(discr != value)`; one surviving valued arm with an
    unreachable `otherwise` records `assume(discr == value)` and becomes `goto`.
    """
    otherwise_unreachable = otherwise in unreachable
    assumes: list[tuple[str, int]] = []
    reachable: list[tuple[int, int]] = []
    for value, block in targets:
        if block in unreachable:
            if not otherwise_unreachable:
                assumes.append(("Ne", value))
        else:
            reachable.append((value, block))
    num_targets = len(reachable) + 1
    if num_targets == 1 and otherwise_unreachable:
        terminator: tuple[Any, ...] = ("unreachable",)
        fully_unreachable = True
    elif num_targets == 1:
        terminator = ("goto", otherwise)
        fully_unreachable = False
    elif num_targets == 2 and otherwise_unreachable:
        value, block = reachable[0]
        assumes.append(("Eq", value))
        terminator = ("goto", block)
        fully_unreachable = False
    elif num_targets == len(targets) + 1:
        return {"changed": False, "assumes": [], "fully_unreachable": False}
    else:
        terminator = ("switchInt", tuple(reachable), otherwise)
        fully_unreachable = False
    return {
        "changed": True,
        "assumes": assumes,
        "terminator": terminator,
        "fully_unreachable": fully_unreachable,
    }


def reachable_blocks(blocks: dict[int, list[str]]) -> set[int]:
    seen: set[int] = set()
    stack = [0]
    while stack:
        block = stack.pop()
        if block in seen or block not in blocks or not blocks[block]:
            continue
        seen.add(block)
        stack.extend(int(m) for m in RE_BB_REF.findall(blocks[block][-1]))
    return seen


def model_unreachable_propagation(
    blocks: dict[int, list[str]],
) -> dict[int, dict[str, Any]]:
    """Predicts, per reachable `SwitchInt` block, what the pass rewrites.

    The pass visits blocks in post-order; a block is unreachable when it ends
    in `unreachable`, in a `goto` to an unreachable block, or in a `SwitchInt`
    whose every successor is unreachable. That set is the least fixpoint
    computed here over the blocks reachable from `bb0`.
    """
    reach = reachable_blocks(blocks)
    unreachable: set[int] = set()
    changed = True
    while changed:
        changed = False
        for block in sorted(reach):
            if block in unreachable:
                continue
            term = blocks[block][-1]
            hit = False
            if RE_UNREACHABLE.match(term):
                hit = True
            else:
                goto = RE_GOTO.match(term)
                switch = parse_switch(term)
                if goto:
                    hit = int(goto.group(1)) in unreachable
                elif switch:
                    _, targets, otherwise = switch
                    hit = otherwise in unreachable and all(
                        b in unreachable for _, b in targets
                    )
            if hit:
                unreachable.add(block)
                changed = True
    predictions: dict[int, dict[str, Any]] = {}
    for block in sorted(reach):
        switch = parse_switch(blocks[block][-1])
        if switch:
            _, targets, otherwise = switch
            predictions[block] = model_remove_successors(
                targets, otherwise, unreachable
            )
    return predictions


def observed_rewrite(before: list[str], after: list[str]) -> dict[str, Any]:
    """Summarises what the pass did to one block."""
    if after == before:
        return {"changed": False, "assumes": []}
    if RE_UNREACHABLE.match(after[-1]) and len(after) == 1:
        return {"changed": True, "assumes": [], "terminator": ("unreachable",)}
    added = after[len(before) - 1 : -1]
    prefix_kept = after[: len(before) - 1] == before[:-1]
    assumes: list[str] = []
    well_formed = prefix_kept and len(added) % 2 == 0
    for index in range(0, len(added) - 1, 2):
        assign = RE_ASSIGN.match(added[index])
        assume = RE_ASSUME_STMT.match(added[index + 1])
        if not assign or not assume:
            well_formed = False
            break
        op = assign.group(2).split("(", 1)[0]
        if assume.group(1) != f"move {assign.group(1)}":
            well_formed = False
        assumes.append(op)
    term = after[-1]
    goto = RE_GOTO.match(term)
    switch = parse_switch(term)
    if goto:
        terminator: tuple[Any, ...] = ("goto", int(goto.group(1)))
    elif switch:
        terminator = ("switchInt", tuple(switch[1]), switch[2])
    elif RE_UNREACHABLE.match(term):
        terminator = ("unreachable",)
    else:
        terminator = ("other",)
    return {
        "changed": True,
        "assumes": assumes,
        "terminator": terminator,
        "well_formed": well_formed,
    }


def compare_model_to_pass(before_text: str, after_text: str) -> dict[str, int]:
    before = parse_blocks(before_text)
    after = parse_blocks(after_text)
    stats = collections.Counter()
    for block, predicted in model_unreachable_propagation(before).items():
        stats["switch_int_terminators"] += 1
        if predicted.get("fully_unreachable"):
            # Unreachable blocks are emptied; the terminator becomes `unreachable`.
            observed = {"changed": True, "assumes": [], "terminator": ("unreachable",)}
            ok = after.get(block) == ["unreachable;"]
        else:
            observed = observed_rewrite(before[block], after.get(block, []))
            ok = observed["changed"] == predicted["changed"]
            if ok and predicted["changed"]:
                ok = (
                    observed.get("well_formed", True)
                    and observed["assumes"] == [op for op, _ in predicted["assumes"]]
                    and observed["terminator"] == predicted["terminator"]
                )
        if predicted["changed"]:
            stats["model_predicts_rewrite"] += 1
            stats["model_predicted_assumes"] += len(predicted["assumes"])
            stats[f"model_case_{predicted['terminator'][0]}"] += 1
        stats["agree" if ok else "disagree"] += 1
    return dict(stats)


# ---------------------------------------------------------------------------
# Specimen sources
# ---------------------------------------------------------------------------

SPECIMEN_CRATE = r"""#![crate_type = "rlib"]
#![feature(core_intrinsics, custom_mir)]
#![allow(internal_features)]
use core::convert::Infallible;
use core::intrinsics::mir::*;

// --- LowerIntrinsics: direct intrinsic calls versus stable wrappers ---------
pub unsafe fn direct_assume(c: bool) { core::intrinsics::assume(c) }
pub unsafe fn direct_copy_nonoverlapping(src: *const u64, dst: *mut u64, n: usize) {
    core::intrinsics::copy_nonoverlapping(src, dst, n)
}
pub unsafe fn direct_unreachable() -> ! { core::intrinsics::unreachable() }
pub unsafe fn wrapper_assert_unchecked(c: bool) { core::hint::assert_unchecked(c) }
pub unsafe fn wrapper_ptr_copy_nonoverlapping(src: *const u64, dst: *mut u64, n: usize) {
    core::ptr::copy_nonoverlapping(src, dst, n)
}
pub unsafe fn wrapper_unreachable_unchecked() -> ! { core::hint::unreachable_unchecked() }

// --- UnreachablePropagation: every case of remove_successors_from_switch ----
pub fn up_two_arms_otherwise_unreachable(x: u8) -> u8 {
    match x { 0 => 10, 1 => 11, _ => unsafe { core::intrinsics::unreachable() } }
}
pub fn up_one_arm_otherwise_unreachable(x: u8) -> u8 {
    match x { 5 => 50, _ => unsafe { core::intrinsics::unreachable() } }
}
pub fn up_removed_arm_otherwise_reachable(x: u8) -> u8 {
    match x { 0 => unsafe { core::intrinsics::unreachable() }, 1 => 11, _ => 99 }
}
pub fn up_all_arms_unreachable_otherwise_reachable(x: u8) -> u8 {
    match x {
        0 => unsafe { core::intrinsics::unreachable() },
        1 => unsafe { core::intrinsics::unreachable() },
        _ => 99,
    }
}
pub fn up_everything_unreachable(x: u8) -> u8 {
    match x {
        0 => unsafe { core::intrinsics::unreachable() },
        _ => unsafe { core::intrinsics::unreachable() },
    }
}
pub fn up_bool_discriminant(x: bool) -> u8 {
    if x { 1 } else { unsafe { core::intrinsics::unreachable() } }
}
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn up_degenerate_zero_arm_switch(x: u8) -> u8 {
    mir! {
        {
            match x {
                _ => bb1,
            }
        }
        bb1 = {
            RET = 7_u8;
            Return()
        }
    }
}

// --- UnreachableEnumBranching: uninhabited variants -------------------------
pub enum E3 { A, B(Infallible), C }
pub fn ueb_uninhabited_middle_variant(e: E3) -> u8 {
    match e { E3::A => 1, E3::B(_) => 2, E3::C => 3 }
}
pub fn ueb_result_infallible(r: Result<u32, Infallible>) -> u32 {
    match r { Ok(v) => v, Err(_) => 7 }
}
pub enum Ord3 { Less, Equal, Greater }
pub fn ueb_otherwise_is_last_variant(c: Ord3) -> u8 {
    match c { Ord3::Less => 1, Ord3::Equal => 2, _ => 3 }
}
"""

LOWER_INTRINSICS_FNS = [
    "direct_assume",
    "direct_copy_nonoverlapping",
    "direct_unreachable",
    "wrapper_assert_unchecked",
    "wrapper_ptr_copy_nonoverlapping",
    "wrapper_unreachable_unchecked",
]
UNREACHABLE_PROP_FNS = [
    "up_two_arms_otherwise_unreachable",
    "up_one_arm_otherwise_unreachable",
    "up_removed_arm_otherwise_reachable",
    "up_all_arms_unreachable_otherwise_reachable",
    "up_everything_unreachable",
    "up_bool_discriminant",
    "up_degenerate_zero_arm_switch",
]
ENUM_BRANCHING_FNS = [
    "ueb_uninhabited_middle_variant",
    "ueb_result_infallible",
    "ueb_otherwise_is_last_variant",
]

POINTER_CHECK_CRATE = r"""#![crate_type = "rlib"]
#![feature(core_intrinsics)]
#![allow(internal_features)]
pub unsafe fn direct_copy_nonoverlapping(src: *const u64, dst: *mut u64, n: usize) {
    core::intrinsics::copy_nonoverlapping(src, dst, n)
}
pub unsafe fn deref_read(p: *const u64) -> u64 { *p }
pub unsafe fn deref_write(p: *mut u64) { *p = 1 }
"""

NATIVE_PRECONDITION_BIN = r"""#![feature(core_intrinsics)]
#![allow(internal_features, invalid_null_arguments)]
use std::hint::black_box;

#[repr(align(8))]
struct Aligned([u8; 32]);

fn main() {
    let case = std::env::args().nth(1).unwrap();
    let buf = Aligned([7; 32]);
    let mut dst_buf = Aligned([0; 32]);
    let aligned_src = black_box(buf.0.as_ptr() as *const u64);
    let misaligned_src = black_box(buf.0.as_ptr().wrapping_add(1) as *const u64);
    let null_src = black_box(core::ptr::null::<u64>());
    let dst = black_box(dst_buf.0.as_mut_ptr() as *mut u64);
    unsafe {
        match case.as_str() {
            "wrapper_zero_count_misaligned" => core::ptr::copy_nonoverlapping(misaligned_src, dst, 0),
            "wrapper_zero_count_null" => core::ptr::copy_nonoverlapping(null_src, dst, 0),
            "wrapper_count1_null" => core::ptr::copy_nonoverlapping(null_src, dst, 1),
            "wrapper_count1_overlap" => core::ptr::copy_nonoverlapping(dst as *const u64, dst, 1),
            "wrapper_count1_disjoint" => core::ptr::copy_nonoverlapping(aligned_src, dst, 1),
            "intrinsic_zero_count_misaligned" => {
                core::intrinsics::copy_nonoverlapping(misaligned_src, dst, 0)
            }
            "intrinsic_zero_count_null" => core::intrinsics::copy_nonoverlapping(null_src, dst, 0),
            _ => std::process::exit(99),
        }
    }
    println!("completed {case} first_dst_byte={}", dst_buf.0[0]);
}
"""

NATIVE_CASES_DEBUG = [
    "wrapper_zero_count_misaligned",
    "wrapper_zero_count_null",
    "wrapper_count1_null",
    "wrapper_count1_overlap",
    "wrapper_count1_disjoint",
    "intrinsic_zero_count_misaligned",
    "intrinsic_zero_count_null",
]
# Without debug assertions nothing is checked, so only run cases that touch no
# invalid memory (zero-length copies and the valid control).
NATIVE_CASES_RELEASE = [
    "wrapper_zero_count_misaligned",
    "wrapper_zero_count_null",
    "wrapper_count1_disjoint",
    "intrinsic_zero_count_misaligned",
    "intrinsic_zero_count_null",
]

MIRI_PRELUDE = "#![allow(invalid_null_arguments)]\nuse core::hint::black_box;\n"
MIRI_ALIGNED = "#[repr(align(8))]\nstruct Aligned([u8; 32]);\n"

MIRI_SPECIMENS: list[tuple[str, str, str]] = [
    (
        "assume_false",
        "ub",
        "fn main() { let c = black_box(false); unsafe { core::hint::assert_unchecked(c) } }\n",
    ),
    (
        "assume_true",
        "ok",
        "fn main() { let c = black_box(true); unsafe { core::hint::assert_unchecked(c) } }\n",
    ),
    (
        "unreachable_reached",
        "ub",
        "fn main() { if black_box(true) { unsafe { core::hint::unreachable_unchecked() } } }\n",
    ),
    (
        "copy_zero_count_null_src",
        "ok",
        "fn main() {\n    let mut d: u64 = 0;\n    let s: *const u64 = core::ptr::null();\n"
        "    unsafe { core::ptr::copy_nonoverlapping(s, &raw mut d, 0) }\n}\n",
    ),
    (
        "copy_zero_count_null_dst",
        "ok",
        "fn main() {\n    let s: u64 = 1;\n    let d: *mut u64 = core::ptr::null_mut();\n"
        "    unsafe { core::ptr::copy_nonoverlapping(&raw const s, d, 0) }\n}\n",
    ),
    (
        "copy_zero_count_null_src_opaque",
        "ok",
        "#[inline(never)]\nfn opaque_null() -> *const u64 { black_box(core::ptr::null()) }\n"
        "fn main() {\n    let mut d: u64 = 0;\n"
        "    unsafe { core::ptr::copy_nonoverlapping(opaque_null(), &raw mut d, 0) }\n}\n",
    ),
    (
        "copy_zero_count_misaligned_src",
        "ub",
        MIRI_ALIGNED
        + "fn main() {\n    let b = Aligned([0; 32]);\n    let mut d: u64 = 0;\n"
        "    let s = b.0.as_ptr().wrapping_add(1) as *const u64;\n"
        "    unsafe { core::ptr::copy_nonoverlapping(s, &raw mut d, 0) }\n}\n",
    ),
    (
        "copy_zero_count_misaligned_dst",
        "ub",
        MIRI_ALIGNED
        + "fn main() {\n    let mut b = Aligned([0; 32]);\n    let s: u64 = 0;\n"
        "    let d = b.0.as_mut_ptr().wrapping_add(1) as *mut u64;\n"
        "    unsafe { core::ptr::copy_nonoverlapping(&raw const s, d, 0) }\n}\n",
    ),
    (
        "copy_zero_count_dangling_aligned",
        "ok",
        "fn main() {\n    let s = core::ptr::NonNull::<u64>::dangling().as_ptr() as *const u64;\n"
        "    let d = core::ptr::NonNull::<u64>::dangling().as_ptr();\n"
        "    unsafe { core::ptr::copy_nonoverlapping(s, d, 0) }\n}\n",
    ),
    (
        "copy_zst_null_count5",
        "ok",
        "fn main() {\n    let s: *const () = black_box(core::ptr::null());\n"
        "    let d: *mut () = black_box(core::ptr::null_mut());\n"
        "    unsafe { core::ptr::copy_nonoverlapping(s, d, 5) }\n}\n",
    ),
    (
        "copy_count1_null_src",
        "ub",
        "fn main() {\n    let mut d: u64 = 0;\n    let s: *const u64 = black_box(core::ptr::null());\n"
        "    unsafe { core::ptr::copy_nonoverlapping(s, &raw mut d, 1) }\n}\n",
    ),
    (
        "copy_count1_dangling_src",
        "ub",
        "fn main() {\n    let mut d: u64 = 0;\n"
        "    let s = core::ptr::NonNull::<u64>::dangling().as_ptr() as *const u64;\n"
        "    unsafe { core::ptr::copy_nonoverlapping(s, &raw mut d, 1) }\n}\n",
    ),
    (
        "copy_count1_overlap_initialized",
        "ub",
        "fn main() {\n    let mut x: u64 = 7;\n    let p = &raw mut x;\n"
        "    unsafe { core::ptr::copy_nonoverlapping(p, p, 1) }\n}\n",
    ),
    (
        "copy_count2_partial_overlap_initialized",
        "ub",
        "fn main() {\n    let mut a = [1u64, 2, 3];\n    let p = a.as_mut_ptr();\n"
        "    unsafe { core::ptr::copy_nonoverlapping(p, p.add(1), 2) }\n}\n",
    ),
    (
        "copy_count1_overlap_uninitialized",
        "ok_interpreter_gap",
        "fn main() {\n    let mut x = core::mem::MaybeUninit::<u64>::uninit();\n"
        "    let p = x.as_mut_ptr();\n"
        "    unsafe { core::ptr::copy_nonoverlapping(p, p, 1) }\n}\n",
    ),
    (
        "copy_count2_disjoint",
        "ok",
        "fn main() {\n    let a = [11u64, 22];\n    let mut b = [0u64; 2];\n"
        "    unsafe { core::ptr::copy_nonoverlapping(a.as_ptr(), b.as_mut_ptr(), 2) }\n"
        "    assert_eq!(b, [11, 22]);\n}\n",
    ),
    (
        "copy_size_overflow",
        "ub",
        "fn main() {\n    let s = core::ptr::NonNull::<u64>::dangling().as_ptr() as *const u64;\n"
        "    let d = core::ptr::NonNull::<u64>::dangling().as_ptr();\n"
        "    unsafe { core::ptr::copy_nonoverlapping(s, d, black_box(usize::MAX)) }\n}\n",
    ),
]

MIRI_MODES: list[tuple[str, list[str]]] = [
    ("stacked_borrows_mir_opt_0", []),
    ("tree_borrows_mir_opt_0", ["-Zmiri-tree-borrows"]),
    ("stacked_borrows_mir_opt_2_inlined", ["-Zmir-opt-level=2", "-Copt-level=2"]),
]

LINT_SPECIMEN = (
    "fn main() {\n    let mut d: u64 = 0;\n    let s: *const u64 = core::ptr::null();\n"
    "    unsafe { core::ptr::copy_nonoverlapping(s, &raw mut d, 0) }\n}\n"
)

PRUNING_DIFFERENTIAL_TEMPLATE = r"""#![feature(core_intrinsics, custom_mir)]
#![allow(internal_features)]
use core::intrinsics::mir::*;

#[inline(never)]
pub fn up_one_arm_otherwise_unreachable(x: u8) -> u8 {
    match x { 5 => 50, _ => unsafe { core::intrinsics::unreachable() } }
}
#[inline(never)]
pub fn up_removed_arm_otherwise_reachable(x: u8) -> u8 {
    match x { 0 => unsafe { core::intrinsics::unreachable() }, 1 => 11, _ => 99 }
}
#[inline(never)]
pub fn up_all_arms_unreachable_otherwise_reachable(x: u8) -> u8 {
    match x {
        0 => unsafe { core::intrinsics::unreachable() },
        1 => unsafe { core::intrinsics::unreachable() },
        _ => 99,
    }
}
#[inline(never)]
pub fn up_two_arms_otherwise_unreachable(x: u8) -> u8 {
    match x { 0 => 10, 1 => 11, _ => unsafe { core::intrinsics::unreachable() } }
}
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
#[inline(never)]
pub fn up_degenerate_zero_arm_switch_uninit(_unused: u8) -> u8 {
    mir! {
        let x: u8;
        {
            StorageLive(x);
            match x {
                _ => bb1,
            }
        }
        bb1 = {
            RET = 7_u8;
            Return()
        }
    }
}
fn main() {
    let x: u8 = core::hint::black_box(__INPUT__);
    let r = __FUNCTION__(x);
    println!("result={r}");
}
"""

PRUNING_DIFFERENTIAL_CASES: list[tuple[str, int]] = [
    ("up_one_arm_otherwise_unreachable", 5),
    ("up_one_arm_otherwise_unreachable", 6),
    ("up_removed_arm_otherwise_reachable", 0),
    ("up_removed_arm_otherwise_reachable", 1),
    ("up_removed_arm_otherwise_reachable", 2),
    ("up_all_arms_unreachable_otherwise_reachable", 0),
    ("up_all_arms_unreachable_otherwise_reachable", 1),
    ("up_all_arms_unreachable_otherwise_reachable", 2),
    ("up_two_arms_otherwise_unreachable", 1),
    ("up_two_arms_otherwise_unreachable", 2),
    ("up_degenerate_zero_arm_switch_uninit", 0),
]
PRUNING_DIFFERENTIAL_MODES: list[tuple[str, list[str]]] = [
    ("mir_opt_0", ["-Zmir-opt-level=0"]),
    (
        "mir_opt_0_plus_unreachable_propagation",
        ["-Zmir-opt-level=0", "-Zmir-enable-passes=+UnreachablePropagation"],
    ),
    ("mir_opt_2", ["-Zmir-opt-level=2"]),
]

# ---------------------------------------------------------------------------
# Parts 1 and 2: pass specimens
# ---------------------------------------------------------------------------


def find_dump(dump_dir: Path, crate: str, fn_name: str, suffix: str) -> Path | None:
    matches = sorted(dump_dir.glob(f"{crate}.{fn_name}.*.{suffix}.mir"))
    return matches[0] if matches else None


def blocks_of(path: Path | None) -> dict[str, list[str]] | None:
    if path is None:
        return None
    parsed = parse_blocks(path.read_text(encoding="utf-8"))
    return {f"bb{index}": lines for index, lines in sorted(parsed.items())}


def run_pass_specimens(tc: dict[str, Any], work: Path) -> dict[str, Any]:
    src = work / "pass_specimens.rs"
    src.write_text(SPECIMEN_CRATE, encoding="utf-8")
    dump_dir = work / "pass_specimens_mir"
    flags = [
        "-C",
        "opt-level=2",
        "-Zdump-mir=LowerIntrinsics|UnreachableEnumBranching|UnreachablePropagation"
        "|runtime-post-cleanup|runtime-optimized",
        f"-Zdump-mir-dir={dump_dir}",
    ]
    proc = run_cmd(
        [tc["rustc"], "--edition=2021", str(src), *flags, "-o", str(work / "libps.rlib")]
    )
    if proc.returncode != 0:
        raise RuntimeError(f"pass specimen crate failed to compile: {proc.stderr}")
    crate = "pass_specimens"

    lowering: dict[str, Any] = {}
    for name in LOWER_INTRINSICS_FNS:
        before = find_dump(dump_dir, crate, name, "LowerIntrinsics.before")
        after = find_dump(dump_dir, crate, name, "LowerIntrinsics.after")
        optimized = find_dump(dump_dir, crate, name, "runtime-optimized.after")
        post_cleanup = find_dump(dump_dir, crate, name, "runtime-post-cleanup.after")
        assert before and after and post_cleanup, name
        before_counts = count_constructs(before.read_text(encoding="utf-8"))
        after_counts = count_constructs(after.read_text(encoding="utf-8"))
        lowering[name] = {
            "lower_intrinsics_before": {
                "counts": before_counts,
                "bb0": blocks_of(before)["bb0"],
            },
            "lower_intrinsics_after": {
                "counts": after_counts,
                "bb0": blocks_of(after)["bb0"],
            },
            "lowered_to_statement_or_terminator_by_lower_intrinsics": (
                after_counts["call_terms"] < before_counts["call_terms"]
            ),
            "runtime_post_cleanup_counts": count_constructs(
                post_cleanup.read_text(encoding="utf-8")
            ),
            # Bodies whose entry block already ends in `unreachable` skip the
            # optimization pipeline, so no `runtime-optimized` dump exists.
            "runtime_optimized_counts": (
                count_constructs(optimized.read_text(encoding="utf-8"))
                if optimized
                else None
            ),
        }

    pruning: dict[str, Any] = {}
    for name in UNREACHABLE_PROP_FNS + ENUM_BRANCHING_FNS:
        ueb_before = find_dump(dump_dir, crate, name, "UnreachableEnumBranching.before")
        ueb_after = find_dump(dump_dir, crate, name, "UnreachableEnumBranching.after")
        up_before = find_dump(dump_dir, crate, name, "UnreachablePropagation.before")
        up_after = find_dump(dump_dir, crate, name, "UnreachablePropagation.after")
        optimized = find_dump(dump_dir, crate, name, "runtime-optimized.after")
        assert ueb_before and ueb_after and up_before and up_after and optimized, name
        up_before_text = up_before.read_text(encoding="utf-8")
        up_after_text = up_after.read_text(encoding="utf-8")
        pruning[name] = {
            "unreachable_enum_branching_before_bb0": blocks_of(ueb_before)["bb0"],
            "unreachable_enum_branching_after_bb0": blocks_of(ueb_after)["bb0"],
            "unreachable_propagation_before": blocks_of(up_before),
            "unreachable_propagation_after": blocks_of(up_after),
            "runtime_optimized": blocks_of(optimized),
            "assume_stmts_added_by_unreachable_propagation": (
                count_constructs(up_after_text)["assume_stmts"]
                - count_constructs(up_before_text)["assume_stmts"]
            ),
            "reference_model_vs_pass": compare_model_to_pass(
                up_before_text, up_after_text
            ),
        }
    return {
        "rustc_flags": flags[:3] + ["-Zdump-mir-dir=<DIR>"],
        "lower_intrinsics": lowering,
        "switch_pruning": pruning,
    }


# ---------------------------------------------------------------------------
# Part 3: CheckAlignment / CheckNull and the library precondition
# ---------------------------------------------------------------------------


def run_pointer_checks(tc: dict[str, Any], work: Path, scrub: Scrubber) -> dict[str, Any]:
    src = work / "pointer_checks.rs"
    src.write_text(POINTER_CHECK_CRATE, encoding="utf-8")
    dump_dir = work / "pointer_checks_mir"
    proc = run_cmd(
        [
            tc["rustc"],
            "--edition=2021",
            str(src),
            "-C",
            "opt-level=0",
            "-C",
            "debug-assertions=on",
            "-Zdump-mir=CheckAlignment|CheckNull",
            f"-Zdump-mir-dir={dump_dir}",
            "-o",
            str(work / "libpc.rlib"),
        ]
    )
    if proc.returncode != 0:
        raise RuntimeError(f"pointer check crate failed to compile: {proc.stderr}")
    instrumentation: dict[str, Any] = {}
    for name in ["direct_copy_nonoverlapping", "deref_read", "deref_write"]:
        before = find_dump(dump_dir, "pointer_checks", name, "CheckAlignment.before")
        mid = find_dump(dump_dir, "pointer_checks", name, "CheckAlignment.after")
        after = find_dump(dump_dir, "pointer_checks", name, "CheckNull.after")
        assert before and mid and after, name

        def asserts(path: Path) -> list[str]:
            found = []
            for line in path.read_text(encoding="utf-8").splitlines():
                match = re.match(r'\s*assert\([^,]+, "([^"]+)"', line)
                if match:
                    found.append(match.group(1))
            return found

        after_text = after.read_text(encoding="utf-8")
        instrumentation[name] = {
            "assert_terminators_before_check_alignment": len(asserts(before)),
            "assert_terminators_after_check_alignment": len(asserts(mid)),
            "assert_terminators_after_check_null": len(asserts(after)),
            "assert_messages_after_check_null": asserts(after),
            "copy_nonoverlapping_stmts_after_check_null": count_constructs(after_text)[
                "copy_nonoverlapping_stmts"
            ],
        }

    native_src = work / "native_precondition.rs"
    native_src.write_text(NATIVE_PRECONDITION_BIN, encoding="utf-8")
    native: dict[str, Any] = {}
    for tag, flags, cases in [
        ("debug_assertions_on_opt_0", ["-C", "opt-level=0", "-C", "debug-assertions=on"], NATIVE_CASES_DEBUG),
        ("debug_assertions_off_opt_2", ["-C", "opt-level=2", "-C", "debug-assertions=off"], NATIVE_CASES_RELEASE),
    ]:
        exe = work / f"native_precondition_{tag}"
        build = run_cmd([tc["rustc"], "--edition=2021", str(native_src), *flags, "-o", str(exe)])
        if build.returncode != 0:
            raise RuntimeError(f"native precondition binary failed: {build.stderr}")
        rows: dict[str, Any] = {}
        for case in cases:
            run = run_cmd([str(exe), case], timeout=60)
            stderr_lines = [scrub(l) for l in run.stderr.strip().splitlines()]
            rows[case] = {
                "returncode": run.returncode,
                "stdout": run.stdout.strip(),
                "stderr_precondition_line": next(
                    (l for l in stderr_lines if "unsafe precondition" in l), None
                ),
            }
        native[tag] = {"rustc_flags": flags, "cases": rows}
    return {"mir_instrumentation": instrumentation, "native_library_precondition": native}


# ---------------------------------------------------------------------------
# Parts 4 and 5: Miri
# ---------------------------------------------------------------------------


def run_miri(
    tc: dict[str, Any], src: Path, extra: list[str], scrub: Scrubber
) -> dict[str, Any]:
    proc = run_cmd(
        [tc["miri"], "--sysroot", tc["miri_sysroot"], "--edition", "2021", *extra, str(src)],
        cwd=src.parent,
        timeout=300,
    )
    errors = [
        scrub(line)
        for line in proc.stderr.splitlines()
        if line.startswith("error:") and "aborting due to" not in line
    ]
    return {
        "returncode": proc.returncode,
        "stdout": proc.stdout.strip(),
        "first_error": errors[0] if errors else None,
    }


def run_miri_matrix(tc: dict[str, Any], work: Path, scrub: Scrubber) -> dict[str, Any]:
    out_dir = work / "miri_matrix"
    out_dir.mkdir()
    rows: dict[str, Any] = {}
    for name, expected, body in MIRI_SPECIMENS:
        src = out_dir / f"{name}.rs"
        src.write_text(MIRI_PRELUDE + body, encoding="utf-8")
        modes = {mode: run_miri(tc, src, flags, scrub) for mode, flags in MIRI_MODES}
        returncodes = sorted({m["returncode"] for m in modes.values()})
        rows[name] = {
            "expected_class": expected,
            "source": MIRI_PRELUDE + body,
            "modes": modes,
            "verdict_identical_across_modes": len(returncodes) == 1,
        }
    lint_src = out_dir / "lint_null_literal_default_lints.rs"
    lint_src.write_text(LINT_SPECIMEN, encoding="utf-8")
    lint = run_cmd(
        [tc["rustc"], "--edition=2021", "--emit=metadata", str(lint_src), "-o", str(out_dir / "lint.rmeta")],
        cwd=out_dir,
    )
    lint_lines = [scrub(l) for l in lint.stderr.splitlines()]
    lint_under_miri = run_miri(tc, lint_src, [], scrub)
    return {
        "modes": {mode: flags for mode, flags in MIRI_MODES},
        "specimens": rows,
        "compile_time_lint_row": {
            "description": (
                "Same program as `copy_zero_count_null_src` without "
                "`#![allow(invalid_null_arguments)]`. `rustc --emit=metadata` "
                "rejects it at compile time; the `miri` driver rejects it with "
                "the same lint before any interpretation starts."
            ),
            "source": LINT_SPECIMEN,
            "rustc_returncode": lint.returncode,
            "first_error": next((l for l in lint_lines if l.startswith("error:")), None),
            "lint_note": next((l.strip() for l in lint_lines if "#[deny(" in l), None),
            "miri_returncode": lint_under_miri["returncode"],
            "miri_first_error": lint_under_miri["first_error"],
        },
    }


def run_pruning_differential(
    tc: dict[str, Any], work: Path, scrub: Scrubber
) -> dict[str, Any]:
    out_dir = work / "pruning_differential"
    out_dir.mkdir()
    rows: list[dict[str, Any]] = []
    for function, value in PRUNING_DIFFERENTIAL_CASES:
        src = out_dir / f"{function}_{value}.rs"
        src.write_text(
            PRUNING_DIFFERENTIAL_TEMPLATE.replace("__INPUT__", str(value)).replace(
                "__FUNCTION__", function
            ),
            encoding="utf-8",
        )
        modes = {
            mode: run_miri(tc, src, flags, scrub)
            for mode, flags in PRUNING_DIFFERENTIAL_MODES
        }
        rows.append(
            {
                "function": function,
                "input": value,
                "modes": modes,
                "ub_verdict_identical_across_modes": len(
                    {m["returncode"] for m in modes.values()}
                )
                == 1,
            }
        )
    return {
        "modes": {mode: flags for mode, flags in PRUNING_DIFFERENTIAL_MODES},
        "source_template": PRUNING_DIFFERENTIAL_TEMPLATE,
        "cases": rows,
    }


# ---------------------------------------------------------------------------
# Part 6: zerocopy census
# ---------------------------------------------------------------------------

LEDGER_KEYS = [
    "bodies",
    "assume_stmts",
    "copy_nonoverlapping_stmts",
    "unreachable_terms",
    "switch_int_terms",
    "bodies_with_assume",
    "bodies_with_copy_nonoverlapping",
    "bodies_with_unreachable_term",
]


def classify_assume_condition(lines: list[str], index: int) -> str:
    """Names the rvalue that defines the operand of the `assume` at `index`."""
    operand = RE_ASSUME_STMT.match(lines[index]).group(1).strip()
    if operand.startswith("const "):
        return operand
    local = operand.split(" ", 1)[-1]
    for prior in range(index - 1, -1, -1):
        assign = RE_ASSIGN.match(lines[prior])
        if assign and assign.group(1) == local:
            rvalue = assign.group(2)
            head = rvalue.split("(", 1)[0]
            if "(" in rvalue and re.fullmatch(r"[A-Za-z]+", head):
                return head
            return "other_rvalue"
    return "defined_outside_block"


def discover_pass_names(tc: dict[str, Any], work: Path) -> list[tuple[str, str]]:
    """Lists `(index, pass)` for every pass dumped for an optimized body."""
    src = work / "pass_discovery.rs"
    src.write_text(
        '#![crate_type = "rlib"]\npub fn f(x: u8) -> u8 { x.wrapping_add(1) }\n',
        encoding="utf-8",
    )
    dump_dir = work / "pass_discovery_mir"
    proc = run_cmd(
        [
            tc["rustc"],
            "--edition=2021",
            str(src),
            "-C",
            "opt-level=2",
            "-Zdump-mir=all",
            f"-Zdump-mir-dir={dump_dir}",
            "-o",
            str(work / "libpd.rlib"),
        ]
    )
    if proc.returncode != 0:
        raise RuntimeError(f"pass discovery failed: {proc.stderr}")
    found: set[tuple[str, str]] = set()
    for path in dump_dir.glob("pass_discovery.f.*.after.mir"):
        match = RE_DUMP_NAME.match(path.name)
        if match and match.group("index").startswith(("3-1-", "3-2-", "3-3-")):
            found.add((match.group("index"), match.group("pass")))
    return sorted(found)


def run_zerocopy_census(
    tc: dict[str, Any], work: Path, zerocopy_dir: Path | None
) -> dict[str, Any]:
    if zerocopy_dir is not None:
        crate_dir = zerocopy_dir
        source = "caller-supplied checkout (--zerocopy-dir)"
    else:
        extract = work / "zc_archive"
        extract.mkdir()
        tar_path = extract / "zerocopy.tar.gz"
        with urllib.request.urlopen(ZEROCOPY_TARBALL_URL, timeout=120) as resp:
            tar_path.write_bytes(resp.read())
        with tarfile.open(tar_path, "r:gz") as tf:
            tf.extractall(path=extract)
        crate_dir = extract / f"zerocopy-{ZEROCOPY_COMMIT}" / "zerocopy"
        source = ZEROCOPY_TARBALL_URL

    build_bin = work / "zc_build_script"
    built = run_cmd([tc["rustc"], "--edition=2021", str(crate_dir / "build.rs"), "-o", str(build_bin)])
    if built.returncode != 0:
        raise RuntimeError(f"zerocopy build.rs failed to compile: {built.stderr}")
    cfg_run = run_cmd([str(build_bin)], cwd=crate_dir, env={"RUSTC": tc["rustc"]})
    if cfg_run.returncode != 0:
        raise RuntimeError(f"zerocopy build.rs failed to run: {cfg_run.stderr}")
    cfgs = [
        line.split("=", 1)[1]
        for line in cfg_run.stdout.splitlines()
        if line.startswith("cargo:rustc-cfg=")
    ]

    passes = discover_pass_names(tc, work)
    pass_names = [name for _, name in passes]
    chunks = [pass_names[i : i + 7] for i in range(0, len(pass_names), 7)]

    ledger: dict[tuple[str, str, str], collections.Counter] = collections.defaultdict(
        collections.Counter
    )
    model_stats: collections.Counter = collections.Counter()
    assume_shapes: dict[str, collections.Counter] = {
        "runtime_optimized": collections.Counter(),
        "added_by_unreachable_propagation": collections.Counter(),
    }
    top_bodies: list[tuple[int, int, str]] = []
    compile_flags = [
        "--edition=2021",
        "--crate-name",
        "zerocopy",
        "--crate-type",
        "rlib",
        *[f'--cfg=feature="{feature}"' for feature in ZEROCOPY_FEATURES],
        *[f"--cfg={cfg}" for cfg in cfgs],
        "-C",
        "opt-level=2",
    ]

    for chunk_index, chunk in enumerate(chunks):
        out_dir = work / f"zc_chunk_{chunk_index}"
        mir_dir = out_dir / "mir"
        out_dir.mkdir()
        proc = run_cmd(
            [
                tc["rustc"],
                str(crate_dir / "src" / "lib.rs"),
                *compile_flags,
                "-Zdump-mir=" + "|".join(chunk),
                f"-Zdump-mir-dir={mir_dir}",
                "-o",
                str(out_dir / "libzerocopy.rlib"),
            ],
            env={"CARGO_PKG_VERSION": ZEROCOPY_VERSION},
            timeout=1800,
        )
        if proc.returncode != 0:
            raise RuntimeError(f"zerocopy chunk {chunk_index} failed: {proc.stderr[-3000:]}")
        wanted = set(chunk)
        up_before: dict[str, str] = {}
        up_after: dict[str, str] = {}
        for path in mir_dir.iterdir():
            match = RE_DUMP_NAME.match(path.name)
            if (
                not match
                or match.group("crate") != "zerocopy"
                or match.group("pass") not in wanted
                or not match.group("index").startswith(("3-1-", "3-2-", "3-3-"))
            ):
                continue
            text = path.read_text(encoding="utf-8")
            counts = count_constructs(text)
            key = (match.group("index"), match.group("pass"), match.group("when"))
            entry = ledger[key]
            entry["bodies"] += 1
            for name in ("assume_stmts", "copy_nonoverlapping_stmts", "unreachable_terms", "switch_int_terms"):
                entry[name] += counts[name]
            entry["bodies_with_assume"] += counts["assume_stmts"] > 0
            entry["bodies_with_copy_nonoverlapping"] += counts["copy_nonoverlapping_stmts"] > 0
            entry["bodies_with_unreachable_term"] += counts["unreachable_terms"] > 0
            if match.group("pass") == "UnreachablePropagation":
                (up_before if match.group("when") == "before" else up_after)[
                    match.group("body")
                ] = text
            if match.group("pass") == "runtime-optimized":
                if counts["assume_stmts"]:
                    top_bodies.append(
                        (counts["assume_stmts"], counts["copy_nonoverlapping_stmts"], match.group("body"))
                    )
                for lines in parse_blocks(text).values():
                    for index, line in enumerate(lines):
                        if RE_ASSUME_STMT.match(line):
                            assume_shapes["runtime_optimized"][
                                classify_assume_condition(lines, index)
                            ] += 1
        for body, before_text in up_before.items():
            after_text = up_after.get(body)
            if after_text is None:
                continue
            for stat, value in compare_model_to_pass(before_text, after_text).items():
                model_stats[stat] += value
            before_blocks = parse_blocks(before_text)
            for block, lines in parse_blocks(after_text).items():
                base = len(before_blocks.get(block, []))
                for index, line in enumerate(lines):
                    if RE_ASSUME_STMT.match(line) and index >= base - 1:
                        assume_shapes["added_by_unreachable_propagation"][
                            classify_assume_condition(lines, index)
                        ] += 1
        shutil.rmtree(out_dir)

    def snapshot(key: tuple[str, str, str]) -> dict[str, int]:
        return {name: int(ledger[key][name]) for name in LEDGER_KEYS}

    rows: list[dict[str, Any]] = []
    chain_ok = True
    previous_after: dict[str, int] | None = None
    for index, name in passes:
        if (index, name, "after") not in ledger:
            continue
        after = snapshot((index, name, "after"))
        is_snapshot_only = (index, name, "before") not in ledger
        row: dict[str, Any] = {"index": index, "pass": name, "after": after}
        if not is_snapshot_only:
            before = snapshot((index, name, "before"))
            row["before"] = before
            row["delta"] = {k: after[k] - before[k] for k in LEDGER_KEYS}
            if (
                index.startswith("3-2-")
                and previous_after is not None
                and previous_after != before
            ):
                chain_ok = False
            if index.startswith("3-2-"):
                previous_after = after
        else:
            row["snapshot_only"] = True
        rows.append(row)

    post_cleanup = next(r for r in rows if r["pass"] == "runtime-post-cleanup")["after"]
    optimized = next(r for r in rows if r["pass"] == "runtime-optimized")["after"]
    opt_rows = [r for r in rows if r["index"].startswith("3-2-") and "delta" in r]
    if opt_rows and opt_rows[-1]["after"] != optimized:
        chain_ok = False
    top_bodies.sort(key=lambda item: (-item[0], item[2]))
    return {
        "subject": {
            "repository": ZEROCOPY_REPOSITORY,
            "revision": ZEROCOPY_COMMIT,
            "version": ZEROCOPY_VERSION,
            "features": ZEROCOPY_FEATURES,
            "build_rs_cfgs": cfgs,
            "source": source,
        },
        "rustc_flags": compile_flags + ["-Zdump-mir=<PASS|...>", "-Zdump-mir-dir=<DIR>"],
        "counting_rules": {
            "assume_stmts": RE_ASSUME_STMT.pattern,
            "copy_nonoverlapping_stmts": RE_CNO_STMT.pattern,
            "unreachable_terms": RE_UNREACHABLE.pattern,
            "switch_int_terms": RE_SWITCH.pattern,
            "body": "one `-Zdump-mir` file whose crate component is `zerocopy`",
        },
        "runtime_post_cleanup": post_cleanup,
        "optimization_pipeline_entry": opt_rows[0]["before"] if opt_rows else None,
        "runtime_optimized": optimized,
        "peak_assume_stmts_in_pipeline": max(
            [r["after"]["assume_stmts"] for r in opt_rows], default=0
        ),
        "pass_ledger": rows,
        "passes_changing_assume_or_copy_or_unreachable": [
            {"index": r["index"], "pass": r["pass"], "delta": {
                k: r["delta"][k]
                for k in ("assume_stmts", "copy_nonoverlapping_stmts", "unreachable_terms", "bodies")
            }}
            for r in rows
            if "delta" in r
            and any(r["delta"][k] for k in ("assume_stmts", "copy_nonoverlapping_stmts", "unreachable_terms"))
        ],
        "ledger_chain_consistent": chain_ok,
        "assume_condition_shapes": {
            key: dict(sorted(value.items(), key=lambda item: (-item[1], item[0])))
            for key, value in assume_shapes.items()
        },
        "bodies_with_most_assume_stmts_at_runtime_optimized": [
            {"body": body, "assume_stmts": assumes, "copy_nonoverlapping_stmts": copies}
            for assumes, copies, body in top_bodies[:15]
        ],
        "reference_model_vs_unreachable_propagation": dict(sorted(model_stats.items())),
    }


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", type=Path, default=Path("probe_results.json"))
    parser.add_argument(
        "--zerocopy-dir",
        type=Path,
        default=None,
        help="path to the `zerocopy/` crate directory of a google/zerocopy checkout "
        f"at {ZEROCOPY_COMMIT} (default: download the commit tarball)",
    )
    parser.add_argument("--skip-zerocopy", action="store_true")
    args = parser.parse_args()

    tc = resolve_toolchain()
    scrub = Scrubber()
    scrub.add(tc["sysroot"], "<SYSROOT>")
    scrub.add(tc["miri_sysroot"], "<MIRI_SYSROOT>")
    scrub.add(Path.home(), "<HOME>")

    with tempfile.TemporaryDirectory(prefix="probe_nondiverging_") as tmp:
        work = Path(tmp)
        scrub.add(work, "<WORK>")
        results: dict[str, Any] = {
            "schema": "probe_nondiverging_intrinsics/1",
            "toolchain": {
                "rustc_verbose_version": tc["rustc_vv"],
                "miri_version": tc["miri_version"],
            },
        }
        results["pass_specimens"] = run_pass_specimens(tc, work)
        results["pointer_checks"] = run_pointer_checks(tc, work, scrub)
        results["miri_matrix"] = run_miri_matrix(tc, work, scrub)
        results["miri_switch_pruning_differential"] = run_pruning_differential(tc, work, scrub)
        if not args.skip_zerocopy:
            results["zerocopy_census"] = run_zerocopy_census(
                tc, work, args.zerocopy_dir.resolve() if args.zerocopy_dir else None
            )

    encoded = scrub(json.dumps(results, indent=2, sort_keys=False))
    args.out.write_text(encoded + "\n", encoding="utf-8")
    print(f"wrote {args.out} ({len(encoded)} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
