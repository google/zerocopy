#!/usr/bin/env python3
"""Probe rustc's handling of `MaybeDangling<T>`, `ManuallyDrop<T>`, `Freeze` and `Unpin`.

Everything recorded in the output JSON is produced by running the given
toolchain on the Rust sources embedded below; nothing is replayed from a table.
The only constants are `REFERENCE_PARAMS_MODULO_NOFREE` and `MIRI_EXPECT`, which
are oracles used to compute the `discriminators` section and the exit status.

Parts:
  A. LLVM IR parameter attributes of nine one-argument functions at
     `-C opt-level=2 -C no-prepopulate-passes` and at `-C opt-level=0`, plus
     `size_of::<T>()` / `size_of::<Option<T>>()` for the nine argument types.
  B. Miri validity verdicts for dangling, misaligned and null references
     stored directly or inside the wrappers.
  C. MIR before/after `ScalarReplacementOfAggregates` for wrapper-typed locals.
  D. Miri runs of programs whose only reference to freed (or re-written)
     memory sits inside `MaybeDangling`/`ManuallyDrop`, with MIR optimisations
     off, on, on with the clean-up passes after SROA disabled, and with SROA
     itself disabled.

Usage:
  python3 probe_maybe_dangling_llvm_attrs_and_sroa.py \
      --rustc /path/to/toolchain/bin/rustc \
      [--miri /path/to/toolchain/bin/miri --miri-sysroot /path/to/miri/sysroot] \
      [--out result.json]

A Miri sysroot can be created with `MIRI_SYSROOT=/tmp/miri-sysroot cargo miri setup`.
Parts B and D are skipped (and reported as skipped) when `--miri` is absent.
Exit status: 0 when every toolchain-independent expectation holds, 1 otherwise.
Only the Python standard library is used.
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

# --------------------------------------------------------------------------
# Embedded Rust sources
# --------------------------------------------------------------------------

SIGS_RS = r"""
#![feature(maybe_dangling)]
#![crate_type = "lib"]
#![allow(dead_code)]
use std::cell::UnsafeCell;
use std::marker::PhantomPinned;
use std::mem::{ManuallyDrop, MaybeDangling, MaybeUninit};

/// `Freeze` (no `UnsafeCell`) but `!Unpin`.
pub struct PinnedU64 { pub v: u64, pub _pin: PhantomPinned }
/// A user-defined transparent wrapper that is not a lang item.
#[repr(transparent)]
pub struct PlainWrap<T>(pub T);

#[no_mangle] pub fn sig_1(x: &u64) { let _ = x; }
#[no_mangle] pub fn sig_2(x: &mut u64) { let _ = x; }
#[no_mangle] pub fn sig_3(x: &UnsafeCell<u64>) { let _ = x; }
#[no_mangle] pub fn sig_4(x: &mut UnsafeCell<u64>) { let _ = x; }
#[no_mangle] pub fn sig_5(x: &mut PinnedU64) { let _ = x; }
#[no_mangle] pub fn sig_6(x: PlainWrap<&u64>) { let _ = x; }
#[no_mangle] pub fn sig_7(x: ManuallyDrop<&u64>) { let _ = x; }
#[no_mangle] pub fn sig_8(x: MaybeDangling<&u64>) { let _ = x; }
#[no_mangle] pub fn sig_9(x: MaybeUninit<&u64>) { let _ = x; }
"""

SIG_TYPES = {
    "sig_1": "&u64",
    "sig_2": "&mut u64",
    "sig_3": "&UnsafeCell<u64>",
    "sig_4": "&mut UnsafeCell<u64>",
    "sig_5": "&mut PinnedU64",
    "sig_6": "PlainWrap<&u64>",
    "sig_7": "ManuallyDrop<&u64>",
    "sig_8": "MaybeDangling<&u64>",
    "sig_9": "MaybeUninit<&u64>",
}

SIZES_RS = r"""
#![feature(maybe_dangling)]
#![allow(dead_code)]
use std::cell::UnsafeCell;
use std::marker::PhantomPinned;
use std::mem::{size_of, ManuallyDrop, MaybeDangling, MaybeUninit};

pub struct PinnedU64 { pub v: u64, pub _pin: PhantomPinned }
#[repr(transparent)]
pub struct PlainWrap<T>(pub T);

fn main() {
    let sizes = [
        size_of::<&u64>(), size_of::<&mut u64>(), size_of::<&UnsafeCell<u64>>(),
        size_of::<&mut UnsafeCell<u64>>(), size_of::<&mut PinnedU64>(),
        size_of::<PlainWrap<&u64>>(), size_of::<ManuallyDrop<&u64>>(),
        size_of::<MaybeDangling<&u64>>(), size_of::<MaybeUninit<&u64>>(),
    ];
    let opt_sizes = [
        size_of::<Option<&u64>>(), size_of::<Option<&mut u64>>(),
        size_of::<Option<&UnsafeCell<u64>>>(), size_of::<Option<&mut UnsafeCell<u64>>>(),
        size_of::<Option<&mut PinnedU64>>(), size_of::<Option<PlainWrap<&u64>>>(),
        size_of::<Option<ManuallyDrop<&u64>>>(), size_of::<Option<MaybeDangling<&u64>>>(),
        size_of::<Option<MaybeUninit<&u64>>>(),
    ];
    println!("SIZES={:?}", sizes);
    println!("OPT_SIZES={:?}", opt_sizes);
}
"""

_FREED_BOX = """    let b = Box::new(7u64);
    let raw: *const u64 = &*b;
    drop(b);
"""

MIRI_PROGRAMS = {
    "bare_ref_freed_box": "fn main() {\n" + _FREED_BOX
    + "    let w: &u64 = unsafe { std::mem::transmute(raw) };\n    let _moved = w;\n}\n",
    "plain_wrap_freed_box_ref": "#[repr(transparent)]\nstruct PlainWrap<T>(T);\nfn main() {\n" + _FREED_BOX
    + "    let w: PlainWrap<&u64> = unsafe { std::mem::transmute(raw) };\n    let _moved = w;\n}\n",
    "manually_drop_freed_box_ref": "use std::mem::ManuallyDrop;\nfn main() {\n" + _FREED_BOX
    + "    let w: ManuallyDrop<&u64> = unsafe { std::mem::transmute(raw) };\n    let _moved = w;\n}\n",
    "maybe_dangling_freed_box_ref": "#![feature(maybe_dangling)]\nuse std::mem::MaybeDangling;\nfn main() {\n"
    + _FREED_BOX
    + "    let w: MaybeDangling<&u64> = unsafe { std::mem::transmute(raw) };\n    let _moved = w;\n}\n",
    "maybe_dangling_into_inner_freed_box_ref": "#![feature(maybe_dangling)]\nuse std::mem::MaybeDangling;\nfn main() {\n"
    + _FREED_BOX
    + "    let w: MaybeDangling<&u64> = unsafe { std::mem::transmute(raw) };\n"
    + "    let _bare: &u64 = w.into_inner();\n}\n",
    "maybe_dangling_misaligned_ref": "#![feature(maybe_dangling)]\nuse std::mem::MaybeDangling;\nfn main() {\n"
    + "    let raw_unaligned = std::ptr::without_provenance::<u64>(0x1);\n"
    + "    let w: MaybeDangling<&u64> = unsafe { std::mem::transmute(raw_unaligned) };\n    let _moved = w;\n}\n",
    "maybe_dangling_null_ref": "#![feature(maybe_dangling)]\nuse std::mem::MaybeDangling;\nfn main() {\n"
    + "    let raw_null = std::ptr::null::<u64>();\n"
    + "    let w: MaybeDangling<&u64> = unsafe { std::mem::transmute(raw_null) };\n    let _moved = w;\n}\n",
    "manually_drop_null_ref": "use std::mem::ManuallyDrop;\nfn main() {\n"
    + "    let raw_null = std::ptr::null::<u64>();\n"
    + "    let w: ManuallyDrop<&u64> = unsafe { std::mem::transmute(raw_null) };\n    let _moved = w;\n}\n",
    "maybe_uninit_null_and_uninit_ref": "use std::mem::MaybeUninit;\nfn main() {\n"
    + "    let raw_null = std::ptr::null::<u64>();\n"
    + "    let w: MaybeUninit<&u64> = unsafe { std::mem::transmute(raw_null) };\n    let _moved = w;\n"
    + "    let u: MaybeUninit<&u64> = MaybeUninit::uninit();\n    let _moved2 = u;\n}\n",
}

# Expected Miri exit status (0 = no UB reported, 1 = UB reported).
MIRI_EXPECT = {
    "bare_ref_freed_box": 1,
    "plain_wrap_freed_box_ref": 1,
    "manually_drop_freed_box_ref": 0,
    "maybe_dangling_freed_box_ref": 0,
    "maybe_dangling_into_inner_freed_box_ref": 1,
    "maybe_dangling_misaligned_ref": 1,
    "maybe_dangling_null_ref": 1,
    "manually_drop_null_ref": 1,
    "maybe_uninit_null_and_uninit_ref": 0,
}

SROA_RS = r"""
#![feature(maybe_dangling)]
#![crate_type = "lib"]
#![allow(unused_variables)]
use std::mem::{ManuallyDrop, MaybeDangling};

#[derive(Clone, Copy)]
pub struct RefPair<'a>(pub &'a u64, pub u64);
#[repr(transparent)]
pub struct PlainWrap<T>(pub T);
#[derive(Copy, Clone)]
pub struct S<T>(T);

pub fn use_plain_wrap(r: &u64, k: u64) -> u64 {
    let w = PlainWrap(RefPair(r, k + 1));
    let RefPair(_a, b) = w.0;
    b
}
pub fn use_manually_drop(r: &u64, k: u64) -> u64 {
    let w = ManuallyDrop::new(RefPair(r, k + 1));
    let RefPair(_a, b) = ManuallyDrop::into_inner(w);
    b
}
pub fn use_maybe_dangling(r: &u64, k: u64) -> u64 {
    let w = MaybeDangling::new(RefPair(r, k + 1));
    let RefPair(_a, b) = w.into_inner();
    b
}

// Whole-value copies: the shape of upstream `tests/mir-opt/sroa/dangling.rs`,
// instantiated at `&u64` so that optimized MIR is built for this crate.
pub fn copy_plain(a: S<&u64>) { let b = a; }
pub fn copy_maybe_dangling(a: MaybeDangling<&u64>) { let b = a; }
pub fn copy_manually_drop(a: ManuallyDrop<&u64>) { let b = a; }
"""

SROA_FUNCTIONS = [
    "use_plain_wrap", "use_manually_drop", "use_maybe_dangling",
    "copy_plain", "copy_maybe_dangling", "copy_manually_drop",
]

HAZARD_OUTER_RS = r"""
#![feature(maybe_dangling)]
#![allow(dead_code)]
use std::mem::MaybeDangling;

struct RefPair<'a>(&'a u64, u64);
struct Outer<'a> {
    md: MaybeDangling<RefPair<'a>>,
    tag: u64,
}

#[inline(never)]
fn victim() -> u64 {
    let b = Box::new(41u64);
    let r: &'static u64 = unsafe { &*(&raw const *b) };
    let o = Outer { md: MaybeDangling::new(RefPair(r, 7)), tag: 1 };
    drop(b); // the reference stored inside `o.md` dangles from here on
    let o2 = o; // whole-value move; the only reference sits under MaybeDangling
    o2.tag
}

fn main() {
    assert_eq!(victim(), 1);
}
"""

HAZARD_OUTER_PLAIN_RS = (
    HAZARD_OUTER_RS.replace("use std::mem::MaybeDangling;", "#[repr(transparent)]\nstruct PlainWrap<T>(T);")
    .replace("md: MaybeDangling<RefPair<'a>>", "md: PlainWrap<RefPair<'a>>")
    .replace("MaybeDangling::new(RefPair(r, 7))", "PlainWrap(RefPair(r, 7))")
    .replace("#![feature(maybe_dangling)]\n", "")
)

# Reproducer quoted from the upstream report rust-lang/rust#164176.
HAZARD_UPSTREAM_ISSUE_RS = r"""
use std::mem::ManuallyDrop;
fn main() {
    let mut v = 0u8;
    let p = &raw mut v;
    let mut md = ManuallyDrop::new(unsafe { &mut *p });
    unsafe {
        ManuallyDrop::drop(&mut md);
        *p = 1;
    }
    let _keep = md;
}
"""

POST_SROA_CLEANUP_PASSES = [
    "SimplifyLocals-before-const-prop",
    "DeadStoreElimination-initial",
    "SimplifyLocals-after-value-numbering",
    "DeadStoreElimination-final",
    "SimplifyLocals-final",
    "CopyProp",
    "DestinationPropagation",
    "SingleUseConsts",
]

# Parameter strings observed on LLVM 23 with `nofree` removed; used only to
# compute `discriminators.attr_matrix_matches_reference_modulo_nofree`.
REFERENCE_PARAMS_MODULO_NOFREE = {
    "sig_1": "ptr noalias noundef readonly align 8 captures(address, read_provenance) dereferenceable(8)",
    "sig_2": "ptr noalias noundef align 8 dereferenceable(8)",
    "sig_3": "ptr noundef nonnull align 8",
    "sig_4": "ptr noalias noundef align 8 dereferenceable(8)",
    "sig_5": "ptr noundef nonnull align 8",
    "sig_6": "ptr noalias noundef readonly align 8 captures(address, read_provenance) dereferenceable(8)",
    "sig_7": "ptr noundef nonnull align 8",
    "sig_8": "ptr noundef nonnull align 8",
    "sig_9": "ptr",
}
REFERENCE_PARAMS_OPT0 = {**{f"sig_{i}": "ptr align 8" for i in range(1, 9)}, "sig_9": "ptr"}
REFERENCE_OPTION_SIZES = [8, 8, 8, 8, 8, 8, 8, 8, 16]

# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------


class Scrubber:
    """Replace host-specific absolute paths in captured tool output."""

    def __init__(self) -> None:
        self.pairs: list[tuple[str, str]] = []

    def add(self, path: str | os.PathLike[str] | None, label: str) -> None:
        if path:
            text = str(path)
            if len(text) > 1:
                self.pairs.append((text, label))
                real = os.path.realpath(text)
                if real != text:
                    self.pairs.append((real, label))
        self.pairs.sort(key=lambda pair: -len(pair[0]))

    def __call__(self, text: str) -> str:
        for needle, label in self.pairs:
            text = text.replace(needle, label)
        return text


def run(cmd: list[str], cwd: Path, env: dict[str, str] | None = None, timeout: int = 600):
    merged = dict(os.environ)
    if env:
        merged.update(env)
    proc = subprocess.run(cmd, cwd=str(cwd), env=merged, capture_output=True, text=True, timeout=timeout)
    return proc.returncode, proc.stdout, proc.stderr


def attr_flags(param: str) -> dict[str, bool]:
    return {
        "noalias": bool(re.search(r"\bnoalias\b", param)),
        "nofree": bool(re.search(r"\bnofree\b", param)),
        "noundef": bool(re.search(r"\bnoundef\b", param)),
        "readonly": bool(re.search(r"\breadonly\b", param)),
        "nonnull": bool(re.search(r"\bnonnull\b", param)),
        "align": bool(re.search(r"\balign \d+", param)),
        "captures": bool(re.search(r"\bcaptures\(", param)),
        "dereferenceable": bool(re.search(r"\bdereferenceable\(\d+\)", param)),
        "dereferenceable_or_null": bool(re.search(r"\bdereferenceable_or_null\(\d+\)", param)),
    }


def parse_signatures(llvm_ir: str) -> dict[str, dict[str, object]]:
    out: dict[str, dict[str, object]] = {}
    for line in llvm_ir.splitlines():
        match = re.match(r"^define .*@(sig_\d)\((.*)\) unnamed_addr", line)
        if not match:
            continue
        name, params = match.group(1), match.group(2)
        param = re.sub(r"\s+%[\w.]+$", "", params.strip())
        out[name] = {"rust_type": SIG_TYPES[name], "llvm_param": param, **attr_flags(param)}
    return out


def first_error_lines(stderr: str, limit: int = 2) -> list[str]:
    """The first `error...` lines, each followed by its ` --> file:line:col` line if any."""
    out: list[str] = []
    lines = stderr.splitlines()
    errors = 0
    for index, line in enumerate(lines):
        if not line.startswith("error"):
            continue
        errors += 1
        if errors > limit:
            break
        out.append(line.rstrip())
        if index + 1 < len(lines) and lines[index + 1].lstrip().startswith("-->"):
            out.append(lines[index + 1].strip())
    return out


def mir_body(text: str) -> str:
    return text.strip() + "\n"


def classify_sroa(after: str) -> dict[str, object]:
    """Describe what SROA left behind for wrapper-typed locals."""
    wrapper_locals = re.findall(
        r"let (?:mut )?(_\d+): (?:std::mem::)?(MaybeDangling|ManuallyDrop|PlainWrap|S)<", after
    )
    fragment_debuginfo = re.findall(
        r"debug \(+\w+: (?:std::mem::)?(MaybeDangling|ManuallyDrop|PlainWrap|S)<[^=]*=> (_\d+);", after
    )
    whole_debuginfo = re.findall(r"debug (\w+) => (_\d+);", after)
    field_copy_from_arg = re.findall(r"(_\d+) = (?:copy|move) \(+_1\.0: ", after)
    whole_copy_from_arg = re.findall(r"(_\d+) = (?:copy|move) _1;", after)
    return {
        "wrapper_typed_locals": [f"{local}: {kind}" for local, kind in wrapper_locals],
        "debuginfo_fragments_through_wrapper": [f"{kind} => {local}" for kind, local in fragment_debuginfo],
        "debuginfo_whole_locals": [f"{name} => {local}" for name, local in whole_debuginfo],
        "field_copy_out_of_argument": bool(field_copy_from_arg),
        "whole_copy_of_argument": bool(whole_copy_from_arg),
        "wrapper_local_was_fragmented": bool(fragment_debuginfo),
    }


# --------------------------------------------------------------------------
# Probe parts
# --------------------------------------------------------------------------


def part_a(rustc: str, work: Path, scrub: Scrubber) -> dict[str, object]:
    src = work / "sigs.rs"
    src.write_text(SIGS_RS)
    result: dict[str, object] = {}
    configs = {
        "opt2_no_prepopulate": ["-C", "opt-level=2", "-C", "no-prepopulate-passes"],
        "opt0": ["-C", "opt-level=0"],
    }
    for label, flags in configs.items():
        out_ll = work / f"sigs_{label}.ll"
        cmd = [rustc, "--edition", "2021", str(src), "--emit=llvm-ir", "-A", "warnings", *flags, "-o", str(out_ll)]
        rc, _stdout, stderr = run(cmd, work)
        entry: dict[str, object] = {"rustc_flags": flags, "rustc_rc": rc}
        if rc != 0:
            entry["stderr_head"] = scrub(stderr).splitlines()[:20]
        else:
            entry["signatures"] = parse_signatures(out_ll.read_text())
        result[label] = entry

    sizes_src = work / "sizes.rs"
    sizes_src.write_text(SIZES_RS)
    sizes_bin = work / "sizes_bin"
    rc, _stdout, stderr = run([rustc, "--edition", "2021", str(sizes_src), "-A", "warnings", "-o", str(sizes_bin)], work)
    sizes: dict[str, object] = {"rustc_rc": rc}
    if rc == 0:
        rc_run, stdout, _stderr = run([str(sizes_bin)], work)
        sizes["run_rc"] = rc_run
        sizes["stdout"] = stdout.strip().splitlines()
        for line in stdout.splitlines():
            key, _, value = line.partition("=")
            if key in ("SIZES", "OPT_SIZES"):
                sizes[key.lower()] = json.loads(value)
        sizes["type_order"] = [SIG_TYPES[f"sig_{i}"] for i in range(1, 10)]
    else:
        sizes["stderr_head"] = scrub(stderr).splitlines()[:20]
    result["sizes"] = sizes
    return result


def run_miri(miri: str, sysroot: str, work: Path, name: str, source: str, flags: list[str], scrub: Scrubber):
    src = work / f"{name}.rs"
    src.write_text(source)
    cmd = [miri, "--edition", "2021", "--sysroot", sysroot, *flags, f"{name}.rs"]
    rc, _stdout, stderr = run(cmd, work)
    return {"miri_flags": flags, "miri_rc": rc, "errors": [scrub(line) for line in first_error_lines(stderr)]}


def part_b(miri: str, sysroot: str, work: Path, scrub: Scrubber) -> dict[str, object]:
    out: dict[str, object] = {}
    for name, source in MIRI_PROGRAMS.items():
        entry = run_miri(miri, sysroot, work, name, source, [], scrub)
        entry["expected_rc"] = MIRI_EXPECT[name]
        out[name] = entry
    return out


def part_c(rustc: str, work: Path, scrub: Scrubber) -> dict[str, object]:
    src = work / "sroa.rs"
    src.write_text(SROA_RS)
    dump_dir = work / "mir_dump"
    out_dir = work / "sroa_out"
    out_dir.mkdir(exist_ok=True)
    flags = ["-C", "opt-level=2", "-C", "overflow-checks=off", "-Zalways-encode-mir",
             "-Zdump-mir=ScalarReplacementOfAggregates", f"-Zdump-mir-dir={dump_dir}"]
    cmd = [rustc, "--edition", "2021", str(src), "-A", "warnings", *flags, "--emit=metadata", "--out-dir", str(out_dir)]
    rc, _stdout, stderr = run(cmd, work)
    result: dict[str, object] = {
        "rustc_flags": ["-C", "opt-level=2", "-C", "overflow-checks=off", "-Zalways-encode-mir",
                        "-Zdump-mir=ScalarReplacementOfAggregates", "-Zdump-mir-dir=<work>/mir_dump"],
        "rustc_rc": rc,
    }
    if rc != 0:
        result["stderr_head"] = scrub(stderr).splitlines()[:20]
        return result
    functions: dict[str, object] = {}
    for fn in SROA_FUNCTIONS:
        entry: dict[str, object] = {}
        for side in ("before", "after"):
            matches = sorted(dump_dir.glob(f"sroa.{fn}.*ScalarReplacementOfAggregates.{side}.mir"))
            entry[f"mir_{side}"] = mir_body(matches[0].read_text()) if matches else None
        if entry["mir_after"]:
            entry["classification"] = classify_sroa(str(entry["mir_after"]))
        functions[fn] = entry
    result["functions"] = functions
    return result


def part_d(miri: str, sysroot: str, work: Path, scrub: Scrubber) -> dict[str, object]:
    keep = "-Zmir-enable-passes=" + ",".join("-" + name for name in POST_SROA_CLEANUP_PASSES)
    outer_configs = {
        "miri_default_mir_opt_level_0": [],
        "mir_opt_level_2": ["-Zmir-opt-level=2"],
        "mir_opt_level_2_post_sroa_cleanup_disabled": ["-Zmir-opt-level=2", keep],
        "mir_opt_level_2_post_sroa_cleanup_disabled_sroa_disabled": [
            "-Zmir-opt-level=2", keep, "-Zmir-enable-passes=-ScalarReplacementOfAggregates"],
    }
    out: dict[str, object] = {"post_sroa_cleanup_passes_disabled": POST_SROA_CLEANUP_PASSES}
    outer: dict[str, object] = {}
    for label, flags in outer_configs.items():
        outer[label] = run_miri(miri, sysroot, work, "sroa_hazard_outer", HAZARD_OUTER_RS, flags, scrub)
    # Keep the MIR that Miri interpreted in the UB-reporting configuration.
    dump_dir = work / "hazard_dump"
    flags = outer_configs["mir_opt_level_2_post_sroa_cleanup_disabled"] + [
        "-Zdump-mir=victim", f"-Zdump-mir-dir={dump_dir}"]
    run([miri, "--edition", "2021", "--sysroot", sysroot, *flags, "sroa_hazard_outer.rs"], work)
    for side in ("before", "after"):
        matches = sorted(dump_dir.glob(f"sroa_hazard_outer.victim.*ScalarReplacementOfAggregates.{side}.mir"))
        outer[f"victim_mir_{side}_sroa"] = mir_body(matches[0].read_text()) if matches else None
    out["outer_struct_with_maybe_dangling_field"] = outer
    out["outer_struct_with_plain_wrap_field_control"] = {
        "miri_default_mir_opt_level_0": run_miri(
            miri, sysroot, work, "sroa_hazard_outer_plain", HAZARD_OUTER_PLAIN_RS, [], scrub)
    }
    issue_configs = {
        "miri_default_mir_opt_level_0": [],
        "enable_inline": ["-Zmir-enable-passes=+Inline"],
        "enable_inline_and_sroa": ["-Zmir-enable-passes=+Inline,+ScalarReplacementOfAggregates"],
    }
    issue: dict[str, object] = {}
    for label, flags in issue_configs.items():
        issue[label] = run_miri(miri, sysroot, work, "sroa_hazard_upstream_issue", HAZARD_UPSTREAM_ISSUE_RS, flags, scrub)
    out["upstream_issue_164176_reproducer"] = issue
    return out


def discriminators(result: dict[str, object]) -> tuple[dict[str, object], list[str]]:
    disc: dict[str, object] = {}
    failures: list[str] = []

    part_a_data = result["part_a"]
    opt2 = part_a_data["opt2_no_prepopulate"].get("signatures", {})  # type: ignore[index, union-attr]
    opt0 = part_a_data["opt0"].get("signatures", {})  # type: ignore[index, union-attr]
    observed_modulo = {
        name: re.sub(r"\s+", " ", re.sub(r"\bnofree ", "", str(sig["llvm_param"]))) for name, sig in opt2.items()
    }
    disc["attr_matrix_matches_reference_modulo_nofree"] = observed_modulo == REFERENCE_PARAMS_MODULO_NOFREE
    disc["nofree_emitted_on"] = sorted(name for name, sig in opt2.items() if sig["nofree"])
    disc["opt0_matrix_matches_reference"] = {n: s["llvm_param"] for n, s in opt0.items()} == REFERENCE_PARAMS_OPT0
    disc["option_sizes_match_reference"] = part_a_data["sizes"].get("opt_sizes") == REFERENCE_OPTION_SIZES  # type: ignore[index, union-attr]
    for key in ("attr_matrix_matches_reference_modulo_nofree", "opt0_matrix_matches_reference",
                "option_sizes_match_reference"):
        if not disc[key]:
            failures.append(key)

    part_b_data = result.get("part_b")
    if isinstance(part_b_data, dict) and not part_b_data.get("skipped"):
        mismatches = [name for name, entry in part_b_data.items() if entry["miri_rc"] != entry["expected_rc"]]
        disc["miri_validity_mismatches"] = mismatches
        if mismatches:
            failures.append("miri_validity_mismatches")

    functions = result["part_c"].get("functions", {})  # type: ignore[union-attr]
    if functions:
        def fragmented(fn: str):
            cls = functions[fn].get("classification")
            return None if cls is None else bool(cls["wrapper_local_was_fragmented"])

        def field_copy(fn: str):
            cls = functions[fn].get("classification")
            return None if cls is None else bool(cls["field_copy_out_of_argument"])

        disc["sroa_fragments_plain_wrapper_local"] = fragmented("use_plain_wrap")
        disc["sroa_fragments_maybe_dangling_local"] = fragmented("use_maybe_dangling")
        disc["sroa_fragments_manually_drop_local"] = fragmented("use_manually_drop")
        disc["sroa_rewrites_whole_copy_of_plain_argument"] = field_copy("copy_plain")
        disc["sroa_rewrites_whole_copy_of_maybe_dangling_argument"] = field_copy("copy_maybe_dangling")
        disc["sroa_rewrites_whole_copy_of_manually_drop_argument"] = field_copy("copy_manually_drop")
        for key in ("sroa_fragments_plain_wrapper_local", "sroa_rewrites_whole_copy_of_plain_argument"):
            if not disc[key]:
                failures.append(key)
    else:
        failures.append("part_c_did_not_run")

    part_d_data = result.get("part_d")
    if isinstance(part_d_data, dict) and not part_d_data.get("skipped"):
        outer = part_d_data["outer_struct_with_maybe_dangling_field"]
        disc["hazard_outer_rc"] = {label: entry["miri_rc"] for label, entry in outer.items()
                                   if isinstance(entry, dict) and "miri_rc" in entry}
        disc["hazard_outer_ub_only_with_sroa_and_no_cleanup"] = (
            disc["hazard_outer_rc"]["miri_default_mir_opt_level_0"] == 0
            and disc["hazard_outer_rc"]["mir_opt_level_2_post_sroa_cleanup_disabled"] == 1
            and disc["hazard_outer_rc"]["mir_opt_level_2_post_sroa_cleanup_disabled_sroa_disabled"] == 0)
        issue = part_d_data["upstream_issue_164176_reproducer"]
        disc["hazard_upstream_issue_rc"] = {label: entry["miri_rc"] for label, entry in issue.items()}
        if disc["hazard_outer_rc"]["miri_default_mir_opt_level_0"] != 0:
            failures.append("hazard_outer_source_program_not_clean_at_miri_defaults")
        if part_d_data["outer_struct_with_plain_wrap_field_control"]["miri_default_mir_opt_level_0"]["miri_rc"] != 1:
            failures.append("plain_wrap_control_not_ub")
    return disc, failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--rustc", default="rustc")
    parser.add_argument("--miri", default=None)
    parser.add_argument("--miri-sysroot", default=os.environ.get("MIRI_SYSROOT"))
    parser.add_argument("--out", default=None)
    args = parser.parse_args()

    scrub = Scrubber()
    scrub.add(os.path.expanduser("~"), "<home>")
    if args.miri_sysroot:
        scrub.add(args.miri_sysroot, "<miri-sysroot>")

    with tempfile.TemporaryDirectory(prefix="maybe_dangling_probe_") as tmp:
        work = Path(tmp)
        scrub.add(work, "<work>")
        rc, stdout, _stderr = run([args.rustc, "-vV"], work)
        if rc != 0:
            print("cannot run rustc -vV", file=sys.stderr)
            return 2
        rc_sysroot, sysroot_out, _ = run([args.rustc, "--print", "sysroot"], work)
        if rc_sysroot == 0:
            scrub.add(sysroot_out.strip(), "<toolchain-sysroot>")
        result: dict[str, object] = {
            "probe": "probe_maybe_dangling_llvm_attrs_and_sroa.py",
            "toolchain": {"rustc_vV": stdout.strip().splitlines()},
        }
        result["part_a"] = part_a(args.rustc, work, scrub)
        result["part_c"] = part_c(args.rustc, work, scrub)
        if args.miri and args.miri_sysroot:
            rc_miri, miri_out, _ = run([args.miri, "--version"], work)
            result["toolchain"]["miri_version"] = miri_out.strip() if rc_miri == 0 else None  # type: ignore[index]
            result["part_b"] = part_b(args.miri, args.miri_sysroot, work, scrub)
            result["part_d"] = part_d(args.miri, args.miri_sysroot, work, scrub)
        else:
            result["part_b"] = {"skipped": "no --miri/--miri-sysroot given"}
            result["part_d"] = {"skipped": "no --miri/--miri-sysroot given"}
        disc, failures = discriminators(result)
        result["discriminators"] = disc
        result["toolchain_independent_expectation_failures"] = failures

    text = scrub(json.dumps(result, indent=2, sort_keys=False)) + "\n"
    if args.out:
        Path(args.out).write_text(text)
    else:
        sys.stdout.write(text)
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
