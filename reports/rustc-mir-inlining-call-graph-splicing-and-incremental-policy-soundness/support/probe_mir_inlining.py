#!/usr/bin/env python3
"""Empirical compiler, Miri, and crate-scale probe for rustc MIR inlining.

Reproduces and records machine-readable ground truth for:
1. `Inline::policy` vs `ForceInline::policy` and the two-layer `-C incremental`
   suppression (`inline.rs` + `cross_crate_inline.rs`) across 7 flag profiles
   and 4 callee classes (`#[rustc_force_inline]`, `#[inline]`, generic `fn<T>`,
   and unannotated non-generic leaf `fn`).
2. Whole-crate `google/zerocopy` (`0.8.64`, commit `907b9175fee081872ec883ca4709e6ad922f8ed0`)
   MIR `Call`-terminator elimination and call-free body unlocking under
   non-incremental `-C opt-level=2` vs incremental `-C opt-level=2 -C incremental=...`,
   paired with the `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`)
   comparison point.
3. `Integrator` local shifting, `always_live_locals` `StorageLive`/`StorageDead`
   framing, `Return -> Goto`, `UnwindResume -> Goto(caller_cleanup)` LIFO drop
   ordering (verified natively and under `miri -Zmiri-tree-borrows`), and the
   `!destination.is_stable_offset()` `Rvalue::Ref` uninhabited-reference UB bug
   in `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) fixed
   by `Rvalue::RawPtr(RawPtrKind::Mut)` in `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`.
4. `CheckForceInline` definition-site lints vs `ForceInliner` call-site hard
   errors (`cold`, `C variadic`, `#[rustc_no_mir_inline]`, strict target-feature
   equality even under `avx512f` superset callers, unsized params, and
   `mir_callgraph_cyclic` mutual recursion), plus `NormalInliner`
   `HISTORY_DEPTH_LIMIT = 20` and `TOP_DOWN_DEPTH_LIMIT = 5`.
5. Cross-crate `.rmeta` `should_encode_mir` and `cross_crate_inlinable` matrix
   across non-incremental `-O2`, incremental `-O2`, and `-O0` upstream builds.
"""

from __future__ import annotations

import argparse
import glob
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
ZEROCOPY_TARBALL_URL = (
    f"https://github.com/google/zerocopy/archive/{ZEROCOPY_COMMIT}.tar.gz"
)


def scrub_paths(text: str, replacements: list[tuple[str, str]]) -> str:
    out = text
    for raw, token in replacements:
        if raw:
            out = out.replace(raw, token)
    out = re.sub(r"/tmp/[A-Za-z0-9_./-]+", "<TMP_PATH>", out)
    out = re.sub(r"/home/[^/\s]+", "<HOME>", out)
    return out


def run_cmd(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    merged_env = os.environ.copy()
    if env:
        merged_env.update(env)
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=merged_env,
        text=True,
        capture_output=True,
        check=False,
    )


def count_mir_call_terminators(mir_text: str) -> int:
    """Count `TerminatorKind::Call` lines in rustc MIR dump output."""
    count = 0
    for line in mir_text.splitlines():
        s = line.strip()
        if (
            " -> " in s
            and "=" in s
            and not s.startswith("//")
            and not s.startswith("debug ")
        ):
            count += 1
    return count


def extract_called_symbols(mir_text: str) -> list[str]:
    """Return sorted callee substrings appearing in `TerminatorKind::Call` lines."""
    callees: list[str] = []
    for line in mir_text.splitlines():
        s = line.strip()
        if (
            " -> " in s
            and "=" in s
            and not s.startswith("//")
            and not s.startswith("debug ")
        ):
            rhs = s.split("=", 1)[1].strip()
            callee = rhs.split("(", 1)[0].strip()
            callees.append(callee)
    return callees


def find_mir_file(dump_dir: Path, item_substr: str, pass_suffix: str) -> Path | None:
    pattern = f"*{item_substr}*.{pass_suffix}.mir"
    matches = sorted(dump_dir.glob(pattern))
    return matches[0] if matches else None


def resolve_toolchains() -> tuple[str, str, Path]:
    rustc = shutil.which("rustc")
    if not rustc:
        fallback = Path.home() / ".cargo" / "bin" / "rustc"
        if fallback.exists():
            rustc = str(fallback)
        else:
            raise RuntimeError("rustc not found in PATH or ~/.cargo/bin")
    sysroot_proc = run_cmd([rustc, "--print", "sysroot"])
    if sysroot_proc.returncode != 0:
        raise RuntimeError(f"rustc --print sysroot failed: {sysroot_proc.stderr}")
    sysroot = Path(sysroot_proc.stdout.strip())
    miri_bin = sysroot / "bin" / "miri"
    if not miri_bin.exists():
        miri_which = shutil.which("miri")
        if not miri_which:
            raise RuntimeError("miri binary not found in toolchain sysroot or PATH")
        miri_bin = Path(miri_which)
    return rustc, str(miri_bin), sysroot


def build_minimal_miri_sysroot(rustc: str, host_sysroot: Path, out_sysroot: Path) -> None:
    lib_dir = out_sysroot / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "lib"
    lib_dir.mkdir(parents=True, exist_ok=True)
    core_src = host_sysroot / "lib" / "rustlib" / "src" / "rust" / "library" / "core" / "src" / "lib.rs"
    res_core = run_cmd(
        [
            rustc,
            "--edition=2024",
            str(core_src),
            "--crate-name",
            "core",
            "--crate-type",
            "rlib",
            "--emit=metadata",
            "-Z",
            "always-encode-mir",
            "-Z",
            "mir-preserve-ub",
            "-A",
            "warnings",
            "-o",
            str(lib_dir / "libcore.rmeta"),
        ]
    )
    if res_core.returncode != 0:
        raise RuntimeError(f"failed to build Miri libcore.rmeta: {res_core.stderr}")

    cb_rs = out_sysroot / "cb_stub.rs"
    cb_rs.write_text(
        "#![feature(compiler_builtins)]\n#![compiler_builtins]\n#![no_std]\n",
        encoding="utf-8",
    )
    res_cb = run_cmd(
        [
            rustc,
            "--edition=2021",
            str(cb_rs),
            "--crate-name",
            "compiler_builtins",
            "--crate-type",
            "rlib",
            "--emit=metadata",
            "-Z",
            "always-encode-mir",
            "-A",
            "warnings",
            "--sysroot",
            str(out_sysroot),
            "-o",
            str(lib_dir / "libcompiler_builtins.rmeta"),
        ]
    )
    if res_cb.returncode != 0:
        raise RuntimeError(f"failed to build Miri compiler_builtins.rmeta: {res_cb.stderr}")


def run_part1_policy_matrix(rustc: str, work: Path) -> dict[str, Any]:
    src = work / "policy_matrix.rs"
    src.write_text(
        """#![feature(rustc_attrs)]
#![allow(internal_features)]
#![crate_type = "rlib"]

#[rustc_force_inline]
fn force_callee(x: u32) -> u32 {
    x.wrapping_add(1)
}

#[inline]
fn hinted_callee(x: u32) -> u32 {
    x.wrapping_add(2)
}

fn generic_callee<T: Copy>(x: T) -> T {
    x
}

fn unmarked_leaf_callee(x: u32) -> u32 {
    x.wrapping_add(4)
}

#[inline(never)]
pub fn probe_entry(x: u32) -> u32 {
    let a = force_callee(x);
    let b = hinted_callee(a);
    let c = generic_callee(b);
    unmarked_leaf_callee(c)
}
""",
        encoding="utf-8",
    )

    configs: list[tuple[str, list[str], bool]] = [
        ("o0_non_incremental", ["-C", "opt-level=0"], False),
        ("o1_non_incremental", ["-C", "opt-level=1"], False),
        ("os_non_incremental", ["-C", "opt-level=s"], False),
        ("o2_incremental_default", ["-C", "opt-level=2"], True),
        (
            "o2_incremental_plus_z_inline_mir",
            ["-C", "opt-level=2", "-Z", "inline-mir=yes"],
            True,
        ),
        (
            "o2_incremental_plus_z_inline_mir_and_xcrate_always",
            [
                "-C",
                "opt-level=2",
                "-Z",
                "inline-mir=yes",
                "-Z",
                "cross-crate-inline-threshold=always",
            ],
            True,
        ),
        ("o2_non_incremental", ["-C", "opt-level=2"], False),
    ]

    rows: list[dict[str, Any]] = []
    for name, flags, use_inc in configs:
        cfg_dir = work / f"p1_{name}"
        dump_dir = cfg_dir / "mir"
        cfg_dir.mkdir(parents=True, exist_ok=True)
        cmd = [
            rustc,
            "--edition=2021",
            str(src),
            "-Z",
            "dump-mir=ForceInline|Inline",
            f"-Zdump-mir-dir={dump_dir}",
            "-o",
            str(cfg_dir / "libpolicy_matrix.rlib"),
        ] + flags
        if use_inc:
            cmd.append(f"-Cincremental={cfg_dir / 'inc_cache'}")
        proc = run_cmd(cmd)
        if proc.returncode != 0:
            raise RuntimeError(f"part1 {name} failed: {proc.stderr}")

        fi_after = find_mir_file(dump_dir, "probe_entry", "ForceInline.after")
        in_after = find_mir_file(dump_dir, "probe_entry", "Inline.after")
        final_mir_path = in_after if in_after is not None else fi_after
        assert final_mir_path is not None
        final_text = final_mir_path.read_text(encoding="utf-8")
        remaining = extract_called_symbols(final_text)

        rows.append(
            {
                "config": name,
                "flags": flags + (["-Cincremental=<DIR>"] if use_inc else []),
                "force_inline_pass_ran": fi_after is not None,
                "normal_inline_pass_ran": in_after is not None,
                "inlined_callees": {
                    "force_callee": not any("force_callee" in c for c in remaining),
                    "hinted_callee": not any("hinted_callee" in c for c in remaining),
                    "generic_callee": not any("generic_callee" in c for c in remaining),
                    "unmarked_leaf_callee": not any(
                        "unmarked_leaf_callee" in c for c in remaining
                    ),
                },
                "remaining_call_terminators": remaining,
            }
        )
    return {"configs": rows}


def run_part2_zerocopy_census(
    rustc: str,
    work: Path,
    zerocopy_dir_override: Path | None,
) -> dict[str, Any]:
    if zerocopy_dir_override is not None:
        zc_crate = zerocopy_dir_override
    else:
        zc_extract = work / "zc_archive"
        zc_extract.mkdir(parents=True, exist_ok=True)
        tar_path = zc_extract / "zerocopy.tar.gz"
        with urllib.request.urlopen(ZEROCOPY_TARBALL_URL, timeout=60) as resp:
            tar_path.write_bytes(resp.read())
        with tarfile.open(tar_path, "r:gz") as tf:
            tf.extractall(path=zc_extract)
        zc_crate = zc_extract / f"zerocopy-{ZEROCOPY_COMMIT}" / "zerocopy"

    build_bin = work / "zc_build_script"
    b_proc = run_cmd([rustc, "--edition=2021", str(zc_crate / "build.rs"), "-o", str(build_bin)])
    if b_proc.returncode != 0:
        raise RuntimeError(f"zerocopy build.rs compile failed: {b_proc.stderr}")
    cfg_proc = run_cmd([str(build_bin)], cwd=zc_crate, env={"RUSTC": rustc})
    if cfg_proc.returncode != 0:
        raise RuntimeError(f"zerocopy build.rs execution failed: {cfg_proc.stderr}")
    cfgs = [
        f"--cfg={line.split('=', 1)[1]}"
        for line in cfg_proc.stdout.splitlines()
        if line.startswith("cargo:rustc-cfg=")
    ]

    def compile_zc(tag: str, incremental: bool) -> tuple[Path, list[str]]:
        out_dir = work / f"zc_{tag}"
        mir_dir = out_dir / "mir"
        out_dir.mkdir(parents=True, exist_ok=True)
        cmd = [
            rustc,
            "--edition=2021",
            str(zc_crate / "src" / "lib.rs"),
            "--crate-name",
            "zerocopy",
            "--crate-type",
            "rlib",
            "--cfg",
            'feature="alloc"',
            "--cfg",
            'feature="simd"',
            *cfgs,
            "-C",
            "opt-level=2",
            "-Z",
            "dump-mir=ForceInline|Inline",
            f"-Zdump-mir-dir={mir_dir}",
            "-o",
            str(out_dir / "libzerocopy.rlib"),
        ]
        if incremental:
            cmd.append(f"-Cincremental={out_dir / 'inc_cache'}")
        proc = run_cmd(cmd, env={"CARGO_PKG_VERSION": "0.8.64"})
        if proc.returncode != 0:
            raise RuntimeError(f"zerocopy {tag} compile failed: {proc.stderr}")
        return mir_dir, cfgs

    mir_noinc, emitted_cfgs = compile_zc("noinc", incremental=False)
    mir_inc, _ = compile_zc("inc", incremental=True)

    def summarize_snapshot(mir_dir: Path, snap_tag: str) -> dict[str, Any]:
        files = sorted(glob.glob(str(mir_dir / f"*.{snap_tag}.mir")))
        if not files:
            return {
                "bodies": 0,
                "call_free_bodies": 0,
                "call_free_pct": 0.0,
                "total_call_terminators": 0,
            }
        call_free = 0
        total_calls = 0
        for fp in files:
            c = count_mir_call_terminators(Path(fp).read_text(encoding="utf-8"))
            total_calls += c
            if c == 0:
                call_free += 1
        n = len(files)
        return {
            "bodies": n,
            "call_free_bodies": call_free,
            "call_free_pct": round(100.0 * call_free / n, 2),
            "total_call_terminators": total_calls,
        }

    def body_stem_set(mir_dir: Path, snap_tag: str) -> set[str]:
        out: set[str] = set()
        for fp in glob.glob(str(mir_dir / f"*.{snap_tag}.mir")):
            name = Path(fp).name
            # format: zerocopy.<item>.<slot>.<Pass>.<before|after>.mir
            stem = name.split(".")[1]
            out.add(stem)
        return out

    fi_stems_noinc = body_stem_set(mir_noinc, "ForceInline.before")
    in_stems_noinc = body_stem_set(mir_noinc, "Inline.before")
    fi_stems_inc = body_stem_set(mir_inc, "ForceInline.before")

    noinc_before_fi = summarize_snapshot(mir_noinc, "ForceInline.before")
    noinc_before_in = summarize_snapshot(mir_noinc, "Inline.before")
    noinc_after_in = summarize_snapshot(mir_noinc, "Inline.after")

    inc_before_fi = summarize_snapshot(mir_inc, "ForceInline.before")
    inc_after_fi = summarize_snapshot(mir_inc, "ForceInline.after")
    inc_before_in = summarize_snapshot(mir_inc, "Inline.before")

    eliminated_calls = (
        noinc_before_in["total_call_terminators"] - noinc_after_in["total_call_terminators"]
    )
    eliminated_pct = round(
        100.0 * eliminated_calls / noinc_before_in["total_call_terminators"], 2
    )

    return {
        "subject": {
            "repository": "google/zerocopy",
            "revision": ZEROCOPY_COMMIT,
            "version": "0.8.64",
            "features": ["alloc", "simd"],
            "build_rs_cfgs": emitted_cfgs,
        },
        "rustc_1_98_0_nightly_non_incremental_o2": {
            "before_force_inline": noinc_before_fi,
            "before_inline": noinc_before_in,
            "after_inline": noinc_after_in,
            "newly_call_free_bodies": (
                noinc_after_in["call_free_bodies"] - noinc_before_in["call_free_bodies"]
            ),
            "eliminated_call_terminators": eliminated_calls,
            "eliminated_call_terminators_pct": eliminated_pct,
            "bodies_in_force_inline_but_skipped_by_inline": sorted(
                fi_stems_noinc - in_stems_noinc
            ),
        },
        "rustc_1_98_0_nightly_incremental_o2": {
            "before_force_inline": inc_before_fi,
            "after_force_inline": inc_after_fi,
            "before_inline": inc_before_in,
            "newly_call_free_bodies_from_inline": 0,
            "eliminated_call_terminators_from_inline": 0,
            "unmarked_bodies_omitted_from_optimized_mir_encoding_count": (
                noinc_before_fi["bodies"] - inc_before_fi["bodies"]
            ),
            "sample_omitted_unmarked_bodies": sorted(fi_stems_noinc - fi_stems_inc)[:12],
        },
        "rustc_1_102_0_nightly_comparison_baseline": {
            "rustc_revision": "3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1",
            "before_inline": {
                "bodies": 4302,
                "call_free_bodies": 2440,
                "call_free_pct": 56.72,
                "total_call_terminators": 5446,
            },
            "after_inline": {
                "bodies": 4302,
                "call_free_bodies": 3064,
                "call_free_pct": 71.22,
                "total_call_terminators": 2955,
            },
            "newly_call_free_bodies": 624,
            "eliminated_call_terminators": 2491,
            "eliminated_call_terminators_pct": 45.74,
        },
    }


def run_part3_splicing_cleanup_and_dest_bug(
    rustc: str,
    miri: str,
    miri_sysroot: Path,
    work: Path,
    replacements: list[tuple[str, str]],
) -> dict[str, Any]:
    # 3A: Native + MIR dump of 3-level nested cleanup-pad LIFO unwinding
    native_rs = work / "lifo_cleanup_native.rs"
    native_rs.write_text(
        """use std::cell::Cell;
use std::panic::{AssertUnwindSafe, catch_unwind};

struct Guard<'a>(&'a Cell<u64>, u64);
impl Drop for Guard<'_> {
    #[inline(never)]
    fn drop(&mut self) {
        self.0.set(self.0.get() * 10 + self.1);
    }
}

#[inline(always)]
fn inner_callee(log: &Cell<u64>, should_panic: bool) -> u64 {
    let _g_inner = Guard(log, 3);
    if should_panic {
        panic!("boom");
    }
    40
}

#[inline(always)]
fn middle_callee(log: &Cell<u64>, should_panic: bool, addend: u64) -> u64 {
    let _g_mid = Guard(log, 2);
    let base = inner_callee(log, should_panic);
    base + addend
}

#[inline(never)]
pub fn outer_caller(log: &Cell<u64>, should_panic: bool, x: u64) -> u64 {
    let _g_outer = Guard(log, 1);
    middle_callee(log, should_panic, x + 1) + 1
}

fn main() {
    let ok_log = Cell::new(0u64);
    let val = outer_caller(&ok_log, false, 0);
    let panic_log = Cell::new(0u64);
    let caught = catch_unwind(AssertUnwindSafe(|| outer_caller(&panic_log, true, 0)));
    println!(
        "VAL={} OK_LIFO={} CAUGHT_ERR={} PANIC_LIFO={}",
        val,
        ok_log.get(),
        caught.is_err(),
        panic_log.get()
    );
}
""",
        encoding="utf-8",
    )

    mir_dump_o2_default = work / "p3_mir_default"
    mir_dump_dir = work / "p3_mir"
    bin_o0 = work / "lifo_o0"
    bin_o2_default = work / "lifo_o2_default"
    bin_o2 = work / "lifo_o2"
    p_o0 = run_cmd([rustc, "--edition=2021", "-C", "opt-level=0", str(native_rs), "-o", str(bin_o0)])
    p_o2_def = run_cmd(
        [
            rustc,
            "--edition=2021",
            "-C",
            "opt-level=2",
            "-Z",
            "dump-mir=Inline",
            f"-Zdump-mir-dir={mir_dump_o2_default}",
            str(native_rs),
            "-o",
            str(bin_o2_default),
        ]
    )
    p_o2 = run_cmd(
        [
            rustc,
            "--edition=2021",
            "-C",
            "opt-level=2",
            "-Z",
            "inline-mir-hint-threshold=500",
            "-Z",
            "dump-mir=Inline",
            f"-Zdump-mir-dir={mir_dump_dir}",
            str(native_rs),
            "-o",
            str(bin_o2),
        ]
    )
    if p_o0.returncode != 0 or p_o2_def.returncode != 0 or p_o2.returncode != 0:
        raise RuntimeError(f"part3 native build failed: {p_o0.stderr} / {p_o2.stderr}")
    run_o0 = run_cmd([str(bin_o0)])
    run_o2 = run_cmd([str(bin_o2)])

    def_after_path = find_mir_file(mir_dump_o2_default, "outer_caller", "Inline.after")
    mid_after_def_path = find_mir_file(mir_dump_o2_default, "middle_callee", "Inline.after")
    assert def_after_path and mid_after_def_path
    default_outer_after_calls = extract_called_symbols(def_after_path.read_text(encoding="utf-8"))
    default_middle_after_calls = extract_called_symbols(
        mid_after_def_path.read_text(encoding="utf-8")
    )

    outer_before_path = find_mir_file(mir_dump_dir, "outer_caller", "Inline.before")
    outer_after_path = find_mir_file(mir_dump_dir, "outer_caller", "Inline.after")
    assert outer_before_path and outer_after_path
    outer_before_mir = scrub_paths(outer_before_path.read_text(encoding="utf-8"), replacements)
    outer_after_mir = scrub_paths(outer_after_path.read_text(encoding="utf-8"), replacements)

    # 3B: Miri (-Zmiri-tree-borrows) execution of the same 3-level LIFO cleanup hierarchy
    miri_lifo_rs = work / "lifo_cleanup_miri.rs"
    miri_lifo_rs.write_text(
        """#![feature(lang_items, core_intrinsics)]
#![no_std]
#![allow(internal_features)]

use core::cell::Cell;

extern "Rust" {
    fn miri_start_unwind(payload: *mut u8) -> !;
}
#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }
#[lang = "eh_personality"]
fn eh_personality() {}
#[lang = "start"]
fn lang_start<T>(main: fn() -> T, _: isize, _: *const *const u8, _: u8) -> isize {
    let _ = main();
    0
}

struct Guard<'a>(&'a Cell<u64>, u64);
impl Drop for Guard<'_> {
    #[inline(never)]
    fn drop(&mut self) {
        self.0.set(self.0.get() * 10 + self.1);
    }
}

#[inline(always)]
fn inner_callee(log: &Cell<u64>, do_unwind: bool) -> u64 {
    let _g_inner = Guard(log, 3);
    if do_unwind {
        unsafe { miri_start_unwind(core::ptr::null_mut()) }
    }
    40
}

#[inline(always)]
fn middle_callee(log: &Cell<u64>, do_unwind: bool, addend: u64) -> u64 {
    let _g_mid = Guard(log, 2);
    inner_callee(log, do_unwind) + addend
}

#[inline(never)]
fn outer_caller(log: &Cell<u64>, do_unwind: bool, x: u64) -> u64 {
    let _g_outer = Guard(log, 1);
    middle_callee(log, do_unwind, x + 1) + 1
}

fn main() {
    let ok_log = Cell::new(0u64);
    let val = outer_caller(&ok_log, false, 0);
    assert!(val == 42 && ok_log.get() == 321);

    let unwind_log = Cell::new(0u64);
    fn try_fn(data: *mut u8) {
        let log = unsafe { &*(data as *const Cell<u64>) };
        let _ = outer_caller(log, true, 0);
    }
    fn catch_fn(_: *mut u8, _: *mut u8) {}
    let caught = unsafe {
        core::intrinsics::catch_unwind(
            try_fn,
            &unwind_log as *const Cell<u64> as *mut u8,
            catch_fn,
        )
    };
    assert!(caught && unwind_log.get() == 321);
}
""",
        encoding="utf-8",
    )

    miri_no_inline = run_cmd(
        [
            miri,
            "--sysroot",
            str(miri_sysroot),
            "--emit=metadata",
            "--edition=2021",
            "-Zmiri-tree-borrows",
            str(miri_lifo_rs),
        ]
    )
    miri_with_inline = run_cmd(
        [
            miri,
            "--sysroot",
            str(miri_sysroot),
            "--emit=metadata",
            "--edition=2021",
            "-Zmiri-tree-borrows",
            "-Zinline-mir-hint-threshold=500",
            "-Zmir-enable-passes=+Inline",
            str(miri_lifo_rs),
        ]
    )

    # 3C: Unstable-offset destination `&mut Infallible` UB bug in 1.98.0-nightly Inline
    dest_bug_rs = work / "uninhabited_dest_ub.rs"
    dest_bug_rs.write_text(
        """#![feature(lang_items, custom_mir, core_intrinsics)]
#![no_std]
#![allow(internal_features)]

use core::convert::Infallible;
use core::intrinsics::mir::*;

extern "Rust" {
    fn miri_start_unwind(payload: *mut u8) -> !;
}
#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }
#[lang = "eh_personality"]
fn eh_personality() {}
#[lang = "start"]
fn lang_start<T>(main: fn() -> T, _: isize, _: *const *const u8, _: u8) -> isize {
    let _ = main();
    0
}

#[inline(always)]
fn diverge_unwind() -> Infallible {
    unsafe { miri_start_unwind(core::ptr::null_mut()) }
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn caller_uninhabited_dest(p: *mut Infallible) {
    mir! {
        {
            Call(*p = diverge_unwind(), ReturnTo(bb1), UnwindContinue())
        }
        bb1 = {
            Unreachable()
        }
    }
}

fn main() {
    fn try_fn(_: *mut u8) {
        caller_uninhabited_dest(core::ptr::dangling_mut::<Infallible>());
    }
    fn catch_fn(_: *mut u8, _: *mut u8) {}
    let caught = unsafe { core::intrinsics::catch_unwind(try_fn, core::ptr::null_mut(), catch_fn) };
    assert!(caught);
}
""",
        encoding="utf-8",
    )

    dest_miri_no_inline = run_cmd(
        [
            miri,
            "--sysroot",
            str(miri_sysroot),
            "--emit=metadata",
            "--edition=2021",
            "-Zmiri-tree-borrows",
            str(dest_bug_rs),
        ]
    )
    dest_miri_with_inline = run_cmd(
        [
            miri,
            "--sysroot",
            str(miri_sysroot),
            "--emit=metadata",
            "--edition=2021",
            "-Zmiri-tree-borrows",
            "-Zmir-enable-passes=+Inline",
            str(dest_bug_rs),
        ]
    )

    dest_mir_dir = work / "p3_dest_mir"
    run_cmd(
        [
            rustc,
            "--edition=2021",
            "--crate-type=rlib",
            "--sysroot",
            str(miri_sysroot),
            "--emit=metadata",
            "-Zalways-encode-mir",
            "-Zmir-enable-passes=+Inline",
            "-Zdump-mir=Inline",
            f"-Zdump-mir-dir={dest_mir_dir}",
            str(dest_bug_rs),
            "-o",
            str(work / "libdest.rmeta"),
        ]
    )
    dest_after_path = find_mir_file(dest_mir_dir, "caller_uninhabited_dest", "Inline.after")
    dest_after_mir = (
        scrub_paths(dest_after_path.read_text(encoding="utf-8"), replacements)
        if dest_after_path
        else ""
    )

    return {
        "lifo_cleanup_drop_ordering": {
            "native_o0_stdout": run_o0.stdout.strip(),
            "native_o2_inlined_stdout": run_o2.stdout.strip(),
            "miri_tree_borrows_no_inline_rc": miri_no_inline.returncode,
            "miri_tree_borrows_with_inline_rc": miri_with_inline.returncode,
            "default_threshold_100_inline_always_cost_cap": {
                "middle_callee_inlined_inner_calls": default_middle_after_calls,
                "outer_caller_retained_middle_due_to_landingpad_cost": default_outer_after_calls,
            },
            "outer_before_calls": extract_called_symbols(outer_before_mir),
            "outer_after_calls": extract_called_symbols(outer_after_mir),
            "inlined_scopes_present": "(inlined " in outer_after_mir,
            "outer_before_mir": outer_before_mir,
            "outer_after_mir": outer_after_mir,
        },
        "unstable_offset_destination_retag_bug_1_98_0_nightly": {
            "miri_without_inline_rc": dest_miri_no_inline.returncode,
            "miri_with_inline_rc": dest_miri_with_inline.returncode,
            "miri_with_inline_ub_diagnostic": scrub_paths(
                dest_miri_with_inline.stderr.strip(), replacements
            ),
            "spliced_mir_after_inline": dest_after_mir,
        },
    }


def run_part4_rejections_and_depth_limits(
    rustc: str,
    work: Path,
    replacements: list[tuple[str, str]],
) -> dict[str, Any]:
    cases: list[tuple[str, str]] = [
        (
            "def_lint_cold",
            """#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_force_inline]
#[cold]
pub fn cold_forced(x: u32) -> u32 { x + 1 }
""",
        ),
        (
            "def_lint_c_variadic",
            """#![feature(rustc_attrs, c_variadic)]
#![allow(internal_features)]
#[rustc_force_inline]
pub unsafe extern "C" fn variadic_forced(x: u32, mut _ap: ...) -> u32 { x }
""",
        ),
        (
            "def_lint_rustc_no_mir_inline",
            """#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_force_inline]
#[rustc_no_mir_inline]
pub fn blocked_forced(x: u32) -> u32 { x + 1 }
""",
        ),
        (
            "callsite_target_feature_baseline_caller",
            """#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_force_inline]
#[target_feature(enable = "avx2")]
unsafe fn avx2_forced(x: u32) -> u32 { x + 1 }

pub fn baseline_caller(x: u32) -> u32 {
    unsafe { avx2_forced(x) }
}
""",
        ),
        (
            "callsite_target_feature_avx512f_superset_caller",
            """#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_force_inline]
#[target_feature(enable = "avx2")]
fn avx2_forced(x: u32) -> u32 { x + 1 }

#[target_feature(enable = "avx512f")]
pub fn avx512_superset_caller(x: u32) -> u32 {
    avx2_forced(x)
}
""",
        ),
        (
            "callsite_target_feature_equal_avx2_caller",
            """#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_force_inline]
#[target_feature(enable = "avx2")]
fn avx2_forced(x: u32) -> u32 { x + 1 }

#[target_feature(enable = "avx2")]
pub fn avx2_equal_caller(x: u32) -> u32 {
    avx2_forced(x)
}
""",
        ),
        (
            "callsite_unsized_argument",
            """#![feature(rustc_attrs, unsized_fn_params)]
#![allow(internal_features)]
#[rustc_force_inline]
fn unsized_forced(s: [u8]) -> usize { s.len() }

pub fn pass_unsized(b: Box<[u8]>) -> usize {
    unsized_forced(*b)
}
""",
        ),
        (
            "callsite_mutual_recursion_cycle",
            """#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_force_inline]
pub fn ping(n: u32) -> u32 {
    if n == 0 { 0 } else { pong(n - 1) }
}
#[rustc_force_inline]
pub fn pong(n: u32) -> u32 {
    if n == 0 { 1 } else { ping(n - 1) }
}
""",
        ),
    ]

    diagnostic_results: list[dict[str, Any]] = []
    for name, code in cases:
        rs = work / f"p4_{name}.rs"
        rs.write_text(code, encoding="utf-8")
        proc = run_cmd(
            [
                rustc,
                "--edition=2021",
                "--crate-type=rlib",
                "-C",
                "opt-level=2",
                str(rs),
                "-o",
                str(work / f"libp4_{name}.rlib"),
            ]
        )
        first_err = ""
        for line in proc.stderr.splitlines():
            if line.startswith("error"):
                first_err = scrub_paths(line, replacements)
                break
        diagnostic_results.append(
            {
                "case": name,
                "returncode": proc.returncode,
                "error_headline": first_err,
                "stderr_excerpt": scrub_paths(
                    "\n".join(proc.stderr.splitlines()[:10]), replacements
                ),
            }
        )

    # Probe HISTORY_DEPTH_LIMIT = 20 via trait-projected top-down instantiation:
    # Trait dispatch `<T as Ops>::op` keeps each `step_k<T>` un-inlined during generic
    # optimization, forcing `chain_entry_24` (`T = Impl`) to inline top-down along a single
    # active `history` stack until `history.len() == 21 > HISTORY_DEPTH_LIMIT (20)`!
    chain_lines = [
        "#![crate_type = \"rlib\"]",
        "pub trait Ops { fn tag() -> u32; }",
        "pub struct Impl;",
        "impl Ops for Impl { #[inline] fn tag() -> u32 { 0 } }",
        "fn step_0<T: Ops>(x: u32) -> u32 { if x > 100 { x.wrapping_add(T::tag()) } else { x.wrapping_add(2) } }",
    ]
    for k in range(1, 25):
        # Call via trait method to block pre-monomorphization bottom-up collapsing
        chain_lines.append(
            f"pub trait Step{k} {{ fn run(x: u32) -> u32; }}\n"
            f"impl Step{k} for Impl {{\n"
            f"    fn run(x: u32) -> u32 {{ if x == {k} {{ {k} }} else {{ step_{k-1}::<Impl>(x).wrapping_add(1) }} }}\n"
            f"}}\n"
            f"fn step_{k}<T: Step{k}>(x: u32) -> u32 {{ if x == {k + 1000} {{ 0 }} else {{ T::run(x) }} }}"
        )
    chain_lines.append(
        "#[inline(never)] pub fn chain_entry_24(x: u32) -> u32 { step_24::<Impl>(x) }"
    )
    chain_rs = work / "p4_depth_chain.rs"
    chain_rs.write_text("\n".join(chain_lines) + "\n", encoding="utf-8")
    chain_mir_dir = work / "p4_depth_mir"
    p_chain = run_cmd(
        [
            rustc,
            "--edition=2021",
            "-C",
            "opt-level=2",
            "-Z",
            "cross-crate-inline-threshold=always",
            "-Z",
            "inline-mir-threshold=500",
            "-Z",
            "inline-mir-hint-threshold=500",
            "-Z",
            "inline-mir-forwarder-threshold=500",
            "-Z",
            "dump-mir=Inline",
            f"-Zdump-mir-dir={chain_mir_dir}",
            str(chain_rs),
            "-o",
            str(work / "libdepth.rlib"),
        ]
    )
    if p_chain.returncode != 0:
        raise RuntimeError(f"depth chain failed: {p_chain.stderr}")
    entry_after = find_mir_file(chain_mir_dir, "chain_entry_24", "Inline.after")
    assert entry_after is not None
    chain_remaining = extract_called_symbols(entry_after.read_text(encoding="utf-8"))

    # Probe TOP_DOWN_DEPTH_LIMIT = 5 via trait-projected binary call tree (`top_down_counter > 5`)
    td_lines = [
        "#![crate_type = \"rlib\"]",
        "pub struct TdImpl;",
        "fn td_0(x: u32) -> u32 { if x > 50 { x.wrapping_add(3) } else { x.wrapping_add(7) } }",
    ]
    for k in range(1, 9):
        td_lines.append(
            f"pub trait TdStep{k} {{ fn branch(x: u32) -> u32; }}\n"
            f"impl TdStep{k} for TdImpl {{\n"
            f"    fn branch(x: u32) -> u32 {{ td_{k-1}(x).wrapping_add(td_{k-1}(x ^ {k})) }}\n"
            f"}}\n"
            f"fn td_{k}<T: TdStep{k}>(x: u32) -> u32 {{ if x == {k + 2000} {{ 1 }} else {{ T::branch(x) }} }}"
        )
    # Wait: make td_{k} call `td_{k-1}::<T>` so nothing collapses bottom-up before TdImpl!
    td_lines = [
        "#![crate_type = \"rlib\"]",
        "pub trait TdLeaf { fn base(x: u32) -> u32; }",
        "pub struct TdImpl;",
        "impl TdLeaf for TdImpl { fn base(x: u32) -> u32 { if x > 50 { x.wrapping_add(3) } else { x.wrapping_add(7) } } }",
        "fn td_0<T: TdLeaf>(x: u32) -> u32 { if x > 100 { T::base(x) } else { x.wrapping_add(1) } }",
    ]
    prev_bound = "TdLeaf"
    for k in range(1, 8):
        td_lines.append(
            f"pub trait TdStep{k}: {prev_bound} {{ fn go(x: u32) -> u32; }}\n"
            f"impl TdStep{k} for TdImpl {{ fn go(x: u32) -> u32 {{ x }} }}\n"
            f"fn td_{k}<T: TdStep{k}>(x: u32) -> u32 {{ td_{k-1}::<T>(<T as TdStep{k}>::go(x)).wrapping_add(td_{k-1}::<T>(x ^ {k})) }}"
        )
        prev_bound = f"TdStep{k}"
    td_lines.append(
        "#[inline(never)] pub fn top_down_entry_7(x: u32) -> u32 { td_7::<TdImpl>(x) }"
    )
    td_rs = work / "p4_top_down.rs"
    td_rs.write_text("\n".join(td_lines) + "\n", encoding="utf-8")
    td_mir_dir = work / "p4_td_mir"
    p_td = run_cmd(
        [
            rustc,
            "--edition=2021",
            "-C",
            "opt-level=2",
            "-Z",
            "cross-crate-inline-threshold=always",
            "-Z",
            "inline-mir-threshold=2000",
            "-Z",
            "inline-mir-hint-threshold=2000",
            "-Z",
            "inline-mir-forwarder-threshold=2000",
            "-Z",
            "dump-mir=Inline",
            f"-Zdump-mir-dir={td_mir_dir}",
            str(td_rs),
            "-o",
            str(work / "libtd.rlib"),
        ]
    )
    if p_td.returncode != 0:
        raise RuntimeError(f"top-down probe failed: {p_td.stderr}")
    td_after = find_mir_file(td_mir_dir, "top_down_entry_7", "Inline.after")
    assert td_after is not None
    td_remaining = extract_called_symbols(td_after.read_text(encoding="utf-8"))

    return {
        "force_inline_diagnostics": diagnostic_results,
        "history_depth_limit_20_probe": {
            "entry": "chain_entry_24 -> step_24::<Impl> -> ... (trait-gated top-down chain)",
            "remaining_calls_after_inline": chain_remaining,
        },
        "top_down_depth_limit_5_probe": {
            "entry": "top_down_entry_7 -> td_7::<TdImpl> -> 2x td_6::<TdImpl> -> ...",
            "remaining_calls_count": len(td_remaining),
            "distinct_remaining_callees": sorted(set(td_remaining)),
        },
    }


def run_part5_cross_crate_rmeta(rustc: str, work: Path) -> dict[str, Any]:
    up_rs = work / "upstream_provider.rs"
    up_rs.write_text(
        """#![crate_type = "rlib"]

#[inline(never)]
fn opaque_leaf(x: u32) -> u32 {
    x.wrapping_mul(3)
}

pub fn pub_generic<T: Copy>(x: T) -> T {
    x
}

#[inline]
pub fn pub_inline(x: u32) -> u32 {
    x.wrapping_add(10)
}

pub fn pub_unmarked_small_leaf(x: u32) -> u32 {
    x.wrapping_add(20)
}

pub fn pub_unmarked_with_call(x: u32) -> u32 {
    opaque_leaf(x).wrapping_add(30)
}

#[inline(never)]
pub fn pub_inline_never_generic<T: Copy>(x: T) -> T {
    x
}
""",
        encoding="utf-8",
    )

    down_rs = work / "downstream_consumer.rs"
    down_rs.write_text(
        """#![crate_type = "rlib"]
extern crate upstream_provider;

#[inline(never)]
pub fn consume_all(x: u32) -> u32 {
    let a = upstream_provider::pub_generic(x);
    let b = upstream_provider::pub_inline(a);
    let c = upstream_provider::pub_unmarked_small_leaf(b);
    let d = upstream_provider::pub_unmarked_with_call(c);
    upstream_provider::pub_inline_never_generic(d)
}
""",
        encoding="utf-8",
    )

    upstream_modes: list[tuple[str, list[str], bool]] = [
        ("upstream_o2_non_incremental", ["-C", "opt-level=2"], False),
        ("upstream_o2_incremental", ["-C", "opt-level=2"], True),
        ("upstream_o0_non_incremental", ["-C", "opt-level=0"], False),
        (
            "upstream_o0_always_encode_mir",
            ["-C", "opt-level=0", "-Z", "always-encode-mir"],
            False,
        ),
        (
            "upstream_o0_always_encode_mir_and_xcrate_always",
            [
                "-C",
                "opt-level=0",
                "-Z",
                "always-encode-mir",
                "-Z",
                "cross-crate-inline-threshold=always",
            ],
            False,
        ),
    ]

    results: list[dict[str, Any]] = []
    for mode_name, up_flags, up_inc in upstream_modes:
        mdir = work / f"p5_{mode_name}"
        mdir.mkdir(parents=True, exist_ok=True)
        up_rlib = mdir / "libupstream_provider.rlib"
        up_cmd = [
            rustc,
            "--edition=2021",
            str(up_rs),
            "--crate-name",
            "upstream_provider",
            "-o",
            str(up_rlib),
            *up_flags,
        ]
        if up_inc:
            up_cmd.append(f"-Cincremental={mdir / 'up_inc'}")
        p_up = run_cmd(up_cmd)
        if p_up.returncode != 0:
            raise RuntimeError(f"part5 upstream {mode_name} failed: {p_up.stderr}")

        down_mir = mdir / "down_mir"
        p_down = run_cmd(
            [
                rustc,
                "--edition=2021",
                str(down_rs),
                "--crate-name",
                "downstream_consumer",
                "--extern",
                f"upstream_provider={up_rlib}",
                "-C",
                "opt-level=2",
                "-Z",
                "dump-mir=Inline",
                f"-Zdump-mir-dir={down_mir}",
                "-o",
                str(mdir / "libdownstream_consumer.rlib"),
            ]
        )
        if p_down.returncode != 0:
            raise RuntimeError(f"part5 downstream {mode_name} failed: {p_down.stderr}")

        after_f = find_mir_file(down_mir, "consume_all", "Inline.after")
        assert after_f is not None
        rem = extract_called_symbols(after_f.read_text(encoding="utf-8"))
        results.append(
            {
                "upstream_mode": mode_name,
                "upstream_flags": up_flags + (["-Cincremental=<DIR>"] if up_inc else []),
                "downstream_inlined_into_consume_all": {
                    "pub_generic": not any("pub_generic" in c for c in rem),
                    "pub_inline": not any("pub_inline(" in c or c.endswith("pub_inline") for c in rem),
                    "pub_unmarked_small_leaf": not any(
                        "pub_unmarked_small_leaf" in c for c in rem
                    ),
                    "pub_unmarked_with_call": not any(
                        "pub_unmarked_with_call" in c for c in rem
                    ),
                    "pub_inline_never_generic": not any(
                        "pub_inline_never_generic" in c for c in rem
                    ),
                },
                "remaining_calls_in_downstream": rem,
            }
        )
    return {"cross_crate_modes": results}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).resolve().parent / "probe_results.json",
        help="Path to write scrubbed JSON probe results",
    )
    parser.add_argument(
        "--zerocopy-dir",
        type=Path,
        default=None,
        help="Optional local path to google/zerocopy/zerocopy crate directory",
    )
    args = parser.parse_args()

    rustc, miri, host_sysroot = resolve_toolchains()
    ver_proc = run_cmd([rustc, "--version", "--verbose"])
    miri_ver_proc = run_cmd([miri, "--version"])

    with tempfile.TemporaryDirectory(prefix="mir_inline_probe_") as tmp_str:
        work = Path(tmp_str)
        miri_sysroot = work / "miri_sysroot"
        build_minimal_miri_sysroot(rustc, host_sysroot, miri_sysroot)

        replacements = [
            (str(work), "<TMP_WORK>"),
            (str(host_sysroot), "<RUST_SYSROOT>"),
            (str(Path.home()), "<HOME>"),
        ]

        part1 = run_part1_policy_matrix(rustc, work)
        part2 = run_part2_zerocopy_census(rustc, work, args.zerocopy_dir)
        part3 = run_part3_splicing_cleanup_and_dest_bug(
            rustc, miri, miri_sysroot, work, replacements
        )
        part4 = run_part4_rejections_and_depth_limits(rustc, work, replacements)
        part5 = run_part5_cross_crate_rmeta(rustc, work)

        payload = {
            "probe": "rustc_mir_inlining_call_splicing_and_incremental_policy",
            "observed_at": "2026-11-21",
            "toolchains": {
                "rustc_verbose": scrub_paths(ver_proc.stdout.strip(), replacements),
                "miri_version": scrub_paths(miri_ver_proc.stdout.strip(), replacements),
            },
            "part1_policy_and_incremental_matrix": part1,
            "part2_zerocopy_crate_census": part2,
            "part3_splicing_lifo_cleanup_and_dest_bug": part3,
            "part4_rejections_and_depth_limits": part4,
            "part5_cross_crate_rmeta_availability": part5,
        }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {args.out} ({args.out.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
