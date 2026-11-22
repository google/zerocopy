#!/usr/bin/env python3
"""Live rustc & Miri differential probe for packed-struct alignment safety and drop elaboration.

Exercises five empirical domains directly against the installed `rustc` and `miri` toolchains
(zero hardcoded outcomes; every exit code, stdout, stderr, and MIR dump count is measured live):

1. `packed_ok`: End-to-end runtime execution + MIR dumps (`ElaborateDrops`, `AddMovesForPackedDrops`)
   + Miri Stacked Borrows + Miri Tree Borrows across:
   - `PackedNoImplDrop` whole-struct drop via `core::ptr::drop_glue`
   - `PackedWithImplDrop` custom `Drop::drop(&mut self)` (align=1) followed by aligned-temp
     extraction for inner `AlignedDrop` field
   - `partial_move_and_dynamic_drop_flag` testing dynamic stack drop flags under conditional
     field move-out on `PackedNoImplDrop` (no double-drop, no leak, exact `PACKED_DROP_LOG=1637`)
   - Legal align-1 borrows (`&p.pad`, `&p2.half`), raw address-of (`&raw const`/`&raw mut`),
     and borrow through `Deref` (`&*pp.r`) where `most_packed_projection` stops at `Deref`
2. `check_packed_ref_matrix`: Compile-time acceptance/rejection matrix for `CheckPackedRef` (`E0793`)
   covering packed(1)/packed(2), align<=pack vs align>pack, `&raw const`/`&raw mut`, `Deref`
   reset, and generic `#[repr(packed)] struct G<T>(T)` conservative rejection
3. `packed_drop_type_rules`: Compile-time `E0509` partial-move rejection on `PackedWithImplDrop`
   plus `wfcheck` unsized-tail drop rejection (`E0277`) vs `ManuallyDrop<[AlignedDrop]>` acceptance
4. `drop_in_place_ub_checks_gap`: Differential comparison between:
   (a) `core::ptr::drop_in_place(&raw mut p.b)` under `-Z ub-checks=yes` (silent survival, rc=0)
       vs Miri Stacked Borrows & Tree Borrows (immediate misaligned-reference UB, rc=1);
   (b) Direct `&mut *(&raw mut p.b)` in `main` under `-Z ub-checks=yes` (caught with panic, rc!=0),
       isolating the bypass to `core::ptr::drop_in_place`'s `?Sized` generic body + pre-inline
       `CheckAlignment` pass ordering;
   (c) Safe manual drop via `core::ptr::read_unaligned(&raw const p.b)` + `drop(val)` (rc=0 across
       native `-Z ub-checks=yes`, Miri SB, and Miri TB)
5. `remove_uninit_drops_const`: Const-checked `#![feature(const_precise_live_drops)]` MIR dump
   verifying `RemoveUninitDrops` runs in `Analysis(PostCleanup)` to erase uninitialized `Drop`
   terminators in `const fn` while remaining inactive on ordinary non-`const` functions.

Usage:
    python3 support/probe_packed_drops_and_elaborate_drops.py --out support/probe_results.json
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
from typing import Any


PACKED_OK_RS = r'''
use core::mem::align_of;
use core::sync::atomic::{AtomicU64, Ordering};

static LOG: AtomicU64 = AtomicU64::new(0);

struct AlignedDrop {
    val: u64,
    tag: u64,
}

impl Drop for AlignedDrop {
    fn drop(&mut self) {
        let addr = (self as *const Self) as usize;
        assert_eq!(
            addr % align_of::<Self>(),
            0,
            "AlignedDrop::drop received misaligned &mut self: addr={:#x}",
            addr
        );
        // Touch the payload to exercise aligned load/store semantics.
        let v = self.val;
        LOG.fetch_add(self.tag + (v & 0), Ordering::SeqCst);
    }
}

#[repr(C, packed)]
struct PackedNoImplDrop {
    pad: u8,
    first: AlignedDrop,
    second: AlignedDrop,
}

#[repr(C, packed)]
struct PackedWithImplDrop {
    pad: u8,
    inner: AlignedDrop,
}

impl Drop for PackedWithImplDrop {
    fn drop(&mut self) {
        // `self` has align = 1 so `&mut PackedWithImplDrop` is valid at any byte address.
        let self_addr = (self as *const Self) as usize;
        assert_eq!(self_addr % align_of::<Self>(), 0);
        // Legal align-1 field borrow (`align_of::<u8>() == 1 <= pack == 1`).
        let pad_ref: &u8 = &self.pad;
        // Legal raw address-of on misaligned field (`PlaceContext::NonMutatingUse(RawBorrow)`).
        let raw_inner: *const AlignedDrop = &raw const self.inner;
        let _ = (pad_ref, raw_inner);
        LOG.fetch_add(1000, Ordering::SeqCst);
    }
}

#[repr(C, packed(2))]
struct Packed2 {
    half: u16,
    wide: u32,
}

#[repr(C, packed)]
struct PackedRefHolder<'a> {
    tag: u8,
    r: &'a u64,
}

#[inline(never)]
fn drop_whole_packed() {
    let p = PackedNoImplDrop {
        pad: 1,
        first: AlignedDrop { val: 11, tag: 100 },
        second: AlignedDrop { val: 22, tag: 200 },
    };
    let pad_ref: &u8 = &p.pad;
    let raw_first: *const AlignedDrop = &raw const p.first;
    assert_eq!(*pad_ref, 1);
    assert!(!raw_first.is_null());

    let p2 = Packed2 { half: 0x1234, wide: 0x5678_9abc };
    let half_ref: &u16 = &p2.half;
    assert_eq!(*half_ref, 0x1234);

    let x: u64 = 99;
    let holder = PackedRefHolder { tag: 7, r: &x };
    // `most_packed_projection` stops at `Deref`, so `&*holder.r` is aligned (`&u64`).
    let through_deref: &u64 = &*holder.r;
    assert_eq!(*through_deref, 99);
}

#[inline(never)]
fn packed_with_own_drop() {
    let p = PackedWithImplDrop {
        pad: 2,
        inner: AlignedDrop { val: 33, tag: 300 },
    };
    let _raw_mut: *const AlignedDrop = &raw const p.inner;
}

#[inline(never)]
fn partial_move_and_dynamic_drop_flag(take_first: bool, first_tag: u64, second_tag: u64) {
    let p = PackedNoImplDrop {
        pad: 3,
        first: AlignedDrop { val: 44, tag: first_tag },
        second: AlignedDrop { val: 55, tag: second_tag },
    };
    if take_first {
        let moved = p.first;
        // `moved` is dropped here at the end of the `if` block; `p.first` must NOT be
        // double-dropped when `p` goes out of scope, while `p.second` MUST still be dropped.
        drop(moved);
    }
}

fn main() {
    drop_whole_packed();                              // +100 +200 = 300
    packed_with_own_drop();                           // +1000 +300 = 1300 (cum 1600)
    partial_move_and_dynamic_drop_flag(true, 20, 10); // +20 +10 = 30 (cum 1630)
    partial_move_and_dynamic_drop_flag(false, 2, 5);  // +2 +5 = 7 (cum 1637)
    println!("PACKED_DROP_LOG={}", LOG.load(Ordering::SeqCst));
}
'''

CHECK_PACKED_REF_CASES: dict[str, tuple[str, int, str]] = {
    "e0793_packed1_u32": (
        """#[repr(C, packed)]
struct P { a: u8, b: u32 }
pub fn bad(p: &P) -> &u32 { &p.b }
fn main() {}
""",
        1,
        "E0793",
    ),
    "e0793_packed1_mut_u64": (
        """#[repr(C, packed)]
struct P { a: u8, b: u64 }
pub fn bad(p: &mut P) -> &mut u64 { &mut p.b }
fn main() {}
""",
        1,
        "E0793",
    ),
    "e0793_packed2_u32": (
        """#[repr(C, packed(2))]
struct P2 { a: u16, b: u32 }
pub fn bad(p: &P2) -> &u32 { &p.b }
fn main() {}
""",
        1,
        "E0793",
    ),
    "e0793_generic_unbounded": (
        """#[repr(packed)]
struct G<T>(T);
pub fn bad<T>(g: &G<T>) -> &T { &g.0 }
fn main() {}
""",
        1,
        "E0793",
    ),
    "ok_packed1_u8": (
        """#[repr(C, packed)]
struct P { a: u8, b: u32 }
pub fn ok(p: &P) -> &u8 { &p.a }
fn main() {}
""",
        0,
        "",
    ),
    "ok_packed2_u16": (
        """#[repr(C, packed(2))]
struct P2 { a: u16, b: u32 }
pub fn ok(p: &P2) -> &u16 { &p.a }
fn main() {}
""",
        0,
        "",
    ),
    "ok_packed1_raw_borrows": (
        """#[repr(C, packed)]
struct P { a: u8, b: u32 }
pub fn ok_const(p: &P) -> *const u32 { &raw const p.b }
pub fn ok_mut(p: &mut P) -> *mut u32 { &raw mut p.b }
fn main() {}
""",
        0,
        "",
    ),
    "ok_packed1_deref_reset": (
        """#[repr(C, packed)]
struct Q<'a> { a: u8, r: &'a u32 }
pub fn ok<'a>(q: &Q<'a>) -> &'a u32 { &*q.r }
fn main() {}
""",
        0,
        "",
    ),
    "ok_nested_packed_min": (
        """#[repr(C, packed(4))]
struct Inner { x: u16, y: u32 }
#[repr(C, packed(2))]
struct Outer { a: u8, i: Inner }
pub fn ok_u16(o: &Outer) -> &u16 { &o.i.x }
fn main() {}
""",
        0,
        "",
    ),
    "e0793_nested_packed_min": (
        """#[repr(C, packed(4))]
struct Inner { x: u16, y: u32 }
#[repr(C, packed(2))]
struct Outer { a: u8, i: Inner }
pub fn bad_u32(o: &Outer) -> &u32 { &o.i.y }
fn main() {}
""",
        1,
        "E0793",
    ),
}

PACKED_DROP_TYPE_CASES: dict[str, tuple[str, int, str]] = {
    "e0509_partial_move_packed_with_impl_drop": (
        """struct AlignedDrop(u64);
impl Drop for AlignedDrop { fn drop(&mut self) {} }

#[repr(C, packed)]
struct PackedWithImplDrop { pad: u8, inner: AlignedDrop }
impl Drop for PackedWithImplDrop { fn drop(&mut self) {} }

pub fn bad(p: PackedWithImplDrop) -> AlignedDrop {
    p.inner
}
fn main() {}
""",
        1,
        "E0509",
    ),
    "e0277_unsized_tail_needs_drop_packed": (
        """struct AlignedDrop(u64);
impl Drop for AlignedDrop { fn drop(&mut self) {} }

#[repr(C, packed)]
struct BadUnsized { pad: u8, tail: [AlignedDrop] }
fn main() {}
""",
        1,
        "E0277",
    ),
    "ok_unsized_tail_manually_drop_packed": (
        """use core::mem::ManuallyDrop;
struct AlignedDrop(u64);
impl Drop for AlignedDrop { fn drop(&mut self) {} }

#[repr(C, packed)]
struct OkUnsized { pad: u8, tail: ManuallyDrop<[AlignedDrop]> }
fn main() {}
""",
        0,
        "",
    ),
    "e0588_packed_contains_repr_align": (
        """#[repr(align(8))]
struct OverAligned(u64);
#[repr(C, packed)]
struct BadPacked { pad: u8, inner: OverAligned }
fn main() {}
""",
        1,
        "E0588",
    ),
}

RAW_DROP_IN_PLACE_RS = r'''
use core::mem::ManuallyDrop;

struct AlignedDrop(u64);

impl Drop for AlignedDrop {
    fn drop(&mut self) {
        let _ = self.0;
    }
}

#[repr(C, packed)]
struct P {
    a: u8,
    b: AlignedDrop,
}

fn main() {
    // Allocate in a 16-byte aligned wrapper so `&raw mut p.b` is guaranteed odd (addr % 8 == 1).
    #[repr(align(16))]
    struct Anchor(ManuallyDrop<P>);

    let mut anchor = Anchor(ManuallyDrop::new(P { a: 1, b: AlignedDrop(42) }));
    let ptr: *mut AlignedDrop = &raw mut (*anchor.0).b;
    assert_eq!((ptr as usize) % 8, 1);
    // UB: `core::ptr::drop_in_place` calls `drop_glue(&mut *to_drop)` on a 1-aligned `*mut AlignedDrop`.
    unsafe { core::ptr::drop_in_place(ptr) };
    println!("RAW_DROP_UB_CHECKS_SURVIVED=true");
}
'''

DIRECT_MUT_DEREF_CONTROL_RS = r'''
use core::mem::ManuallyDrop;

struct AlignedDrop(u64);

#[repr(C, packed)]
struct P {
    a: u8,
    b: AlignedDrop,
}

fn main() {
    #[repr(align(16))]
    struct Anchor(ManuallyDrop<P>);

    let mut anchor = Anchor(ManuallyDrop::new(P { a: 1, b: AlignedDrop(42) }));
    let ptr: *mut AlignedDrop = &raw mut (*anchor.0).b;
    assert_eq!((ptr as usize) % 8, 1);
    // Direct `&mut *ptr` in `main` IS seen by `CheckAlignment` before `Inline`.
    unsafe {
        let r: &mut AlignedDrop = &mut *ptr;
        core::hint::black_box(r);
    }
    println!("DIRECT_MUT_DEREF_SURVIVED=true");
}
'''

READ_UNALIGNED_SAFE_DROP_RS = r'''
use core::mem::{ManuallyDrop, align_of};
use core::sync::atomic::{AtomicU64, Ordering};

static DROPPED: AtomicU64 = AtomicU64::new(0);

struct AlignedDrop(u64);

impl Drop for AlignedDrop {
    fn drop(&mut self) {
        assert_eq!(((self as *const Self) as usize) % align_of::<Self>(), 0);
        DROPPED.fetch_add(self.0, Ordering::SeqCst);
    }
}

#[repr(C, packed)]
struct P {
    a: u8,
    b: AlignedDrop,
}

fn main() {
    #[repr(align(16))]
    struct Anchor(ManuallyDrop<P>);

    let anchor = Anchor(ManuallyDrop::new(P { a: 1, b: AlignedDrop(42) }));
    let ptr: *const AlignedDrop = &raw const (*anchor.0).b;
    assert_eq!((ptr as usize) % 8, 1);
    // Sound manual packed drop: move to aligned stack local via `read_unaligned`, then drop.
    let val = unsafe { core::ptr::read_unaligned(ptr) };
    drop(val);
    println!("SAFE_READ_UNALIGNED_DROP={}", DROPPED.load(Ordering::SeqCst));
}
'''

REMOVE_UNINIT_DROPS_CONST_RS = r'''
#![feature(const_precise_live_drops)]

pub struct NonCopy(pub u32);
impl Drop for NonCopy {
    fn drop(&mut self) {}
}

#[repr(C, packed)]
pub struct PackedPair {
    pub tag: u8,
    pub a: NonCopy,
    pub b: NonCopy,
}

pub const fn const_extract_both(p: PackedPair) -> (NonCopy, NonCopy) {
    // Both fields moved out before `p` goes out of scope:
    // `RemoveUninitDrops` sees every drop-needing child move path uninitialized and
    // erases `drop(p)` -> `goto` BEFORE `CheckLiveDrops` runs!
    (p.a, p.b)
}

pub fn runtime_extract_both(p: PackedPair) -> (NonCopy, NonCopy) {
    (p.a, p.b)
}

pub const RES: u32 = {
    let p = PackedPair { tag: 1, a: NonCopy(10), b: NonCopy(20) };
    let (a, b) = const_extract_both(p);
    let out = a.0 + b.0;
    core::mem::forget(a);
    core::mem::forget(b);
    out
};

fn main() {
    let (a, b) = runtime_extract_both(PackedPair { tag: 1, a: NonCopy(3), b: NonCopy(4) });
    println!("CONST_RES={} RT_RES={}", RES, a.0 + b.0);
}
'''


def sanitize(text: str, replacements: list[tuple[str, str]]) -> str:
    out = text
    for old, new in replacements:
        if old:
            out = out.replace(old, new)
    home_dir = str(Path.home())
    if home_dir:
        out = out.replace(home_dir, "<HOME>")
    out = re.sub(r"/(?:home|Users)/[A-Za-z0-9._-]+", "<HOME>", out)
    out = re.sub(r"/rustc(?:-[a-z]+)?/[0-9a-f]{40}/", "<RUSTC_SRC>/", out)
    return out


def run_cmd(cmd: list[str], cwd: Path | None = None, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)


def run_miri_file(
    miri_bin: str,
    sysroot: str,
    rs_file: Path,
    extra_flags: list[str],
    reps: list[tuple[str, str]],
) -> dict[str, Any]:
    cmd = [miri_bin, "--edition=2021", "--sysroot", sysroot, *extra_flags, str(rs_file)]
    proc = run_cmd(cmd)
    return {
        "rc": proc.returncode,
        "stdout": sanitize(proc.stdout.strip(), reps),
        "stderr": sanitize(proc.stderr.strip(), reps),
    }


def parse_mir_counts(mir_dir: Path) -> dict[str, dict[str, Any]]:
    counts: dict[str, dict[str, Any]] = {}
    for p in sorted(mir_dir.glob("*.mir")):
        txt = p.read_text(errors="replace")
        # Count MIR terminators and statements accurately
        drop_terms = len(re.findall(r"^\s+drop\(", txt, flags=re.M))
        storage_live = len(re.findall(r"^\s+StorageLive\(", txt, flags=re.M))
        storage_dead = len(re.findall(r"^\s+StorageDead\(", txt, flags=re.M))
        switch_int = len(re.findall(r"^\s+switchInt\(", txt, flags=re.M))
        bool_flags = len(re.findall(r"let mut _\d+: bool;", txt))
        goto_terms = len(re.findall(r"^\s+goto ->", txt, flags=re.M))
        counts[p.name] = {
            "drop_terminators": drop_terms,
            "storage_live": storage_live,
            "storage_dead": storage_dead,
            "switch_int": switch_int,
            "bool_locals": bool_flags,
            "goto_terminators": goto_terms,
        }
    return counts


def ensure_miri_sysroot(cargo_bin: str, work_dir: Path, provided_sysroot: str | None) -> tuple[str, str]:
    rustc_sysroot = run_cmd(["rustc", "--print", "sysroot"]).stdout.strip()
    miri_bin = str(Path(rustc_sysroot) / "bin" / "miri")
    if not Path(miri_bin).exists():
        found = shutil.which("miri")
        if not found:
            raise RuntimeError("miri binary not found in rustc sysroot or PATH")
        miri_bin = found
    if provided_sysroot and Path(provided_sysroot).exists():
        return miri_bin, provided_sysroot
    setup_dir = work_dir / "miri_setup_pkg"
    (setup_dir / "src").mkdir(parents=True, exist_ok=True)
    (setup_dir / "Cargo.toml").write_text('[package]\nname = "miri_setup_pkg"\nversion = "0.1.0"\nedition = "2021"\n')
    (setup_dir / "src" / "main.rs").write_text("fn main() {}\n")
    sysroot_dir = work_dir / "miri_sysroot"
    env = dict(os.environ, MIRI_SYSROOT=str(sysroot_dir))
    proc = run_cmd([cargo_bin, "miri", "setup", "--print-sysroot"], cwd=setup_dir, env=env)
    if proc.returncode != 0:
        raise RuntimeError(f"cargo miri setup failed: {proc.stderr}")
    return miri_bin, proc.stdout.strip().splitlines()[-1].strip()


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", default=str(Path(__file__).resolve().parent / "probe_results.json"))
    ap.add_argument("--miri-sysroot", default="", help="Optional pre-built Miri sysroot path")
    ap.add_argument("--save-mir-excerpts", default="", help="Optional directory to save key sanitized MIR dumps")
    args = ap.parse_args(argv)

    rustc_ver = run_cmd(["rustc", "-vV"]).stdout.strip()
    cargo_bin = shutil.which("cargo") or "cargo"
    miri_ver = run_cmd([cargo_bin, "miri", "--version"]).stdout.strip()

    with tempfile.TemporaryDirectory(prefix="packed_drops_probe_") as tmp_str:
        tmp = Path(tmp_str)
        miri_bin, miri_sysroot = ensure_miri_sysroot(cargo_bin, tmp, args.miri_sysroot or None)
        reps = [
            (str(tmp), "<TMP>"),
            (miri_sysroot, "<MIRI_SYSROOT>"),
            (run_cmd(["rustc", "--print", "sysroot"]).stdout.strip(), "<RUSTC_SYSROOT>"),
        ]

        results: dict[str, Any] = {
            "schema": "packed-drops-probe/1",
            "observed_at": datetime.date.today().isoformat(),
            "rustc_version": rustc_ver,
            "miri_version": miri_ver,
        }

        # ------------------------------------------------------------------
        # 1. packed_ok: native + ub-checks + MIR dumps + Miri SB/TB
        # ------------------------------------------------------------------
        packed_ok_rs = tmp / "packed_ok.rs"
        packed_ok_rs.write_text(PACKED_OK_RS)
        mir_dir = tmp / "mir_packed_ok"
        mir_dir.mkdir()
        bin_native = tmp / "packed_ok_native"
        c_native = run_cmd([
            "rustc", "--edition=2021", "-C", "opt-level=0", "-C", "debuginfo=0",
            "-Z", "dump-mir=ElaborateDrops|AddMovesForPackedDrops",
            "-Z", f"dump-mir-dir={mir_dir}",
            "-o", str(bin_native), str(packed_ok_rs),
        ])
        r_native = run_cmd([str(bin_native)]) if c_native.returncode == 0 else None

        bin_ub = tmp / "packed_ok_ub"
        c_ub = run_cmd([
            "rustc", "--edition=2021", "-C", "opt-level=0", "-Z", "ub-checks=yes",
            "-o", str(bin_ub), str(packed_ok_rs),
        ])
        r_ub = run_cmd([str(bin_ub)]) if c_ub.returncode == 0 else None

        miri_sb = run_miri_file(miri_bin, miri_sysroot, packed_ok_rs, [], reps)
        miri_tb = run_miri_file(miri_bin, miri_sysroot, packed_ok_rs, ["-Zmiri-tree-borrows"], reps)

        mir_counts = parse_mir_counts(mir_dir)
        key_mir_excerpts: dict[str, str] = {}
        wanted_patterns = [
            "core.ptr-drop_glue.PackedNoImplDrop",
            "core.ptr-drop_glue.PackedWithImplDrop",
            "packed_ok.partial_move_and_dynamic_drop_flag",
            "packed_ok.drop_whole_packed",
            "packed_ok.packed_with_own_drop",
        ]
        for p in sorted(mir_dir.glob("*.mir")):
            if any(w in p.name for w in wanted_patterns) and "promoted" not in p.name:
                key_mir_excerpts[p.name] = sanitize(p.read_text(errors="replace"), reps)

        results["packed_ok"] = {
            "compile_native_rc": c_native.returncode,
            "native_rc": r_native.returncode if r_native else None,
            "native_stdout": sanitize(r_native.stdout.strip(), reps) if r_native else "",
            "ub_checks_rc": r_ub.returncode if r_ub else None,
            "ub_checks_stdout": sanitize(r_ub.stdout.strip(), reps) if r_ub else "",
            "miri_sb": miri_sb,
            "miri_tb": miri_tb,
            "mir_dump_counts": mir_counts,
        }

        # ------------------------------------------------------------------
        # 2. CheckPackedRef matrix (E0793 vs legal borrows & raw pointers)
        # ------------------------------------------------------------------
        cpr_results: dict[str, Any] = {}
        for name, (src, exp_rc, exp_code) in CHECK_PACKED_REF_CASES.items():
            f = tmp / f"{name}.rs"
            f.write_text(src)
            out_bin = tmp / f"{name}.bin"
            c = run_cmd(["rustc", "--edition=2021", "--crate-type=bin", "-o", str(out_bin), str(f)])
            err_s = sanitize(c.stderr.strip(), reps)
            cpr_results[name] = {
                "rc": c.returncode,
                "expected_rc": exp_rc,
                "expected_error_code": exp_code,
                "matched_expected": (c.returncode == exp_rc) and (not exp_code or exp_code in err_s),
                "stderr": err_s,
            }
        results["check_packed_ref_matrix"] = cpr_results

        # ------------------------------------------------------------------
        # 3. Packed Drop type-system rules (E0509 + wfcheck unsized tail)
        # ------------------------------------------------------------------
        pdt_results: dict[str, Any] = {}
        for name, (src, exp_rc, exp_code) in PACKED_DROP_TYPE_CASES.items():
            f = tmp / f"{name}.rs"
            f.write_text(src)
            out_bin = tmp / f"{name}.bin"
            c = run_cmd(["rustc", "--edition=2021", "--crate-type=bin", "-o", str(out_bin), str(f)])
            err_s = sanitize(c.stderr.strip(), reps)
            pdt_results[name] = {
                "rc": c.returncode,
                "expected_rc": exp_rc,
                "expected_error_code": exp_code,
                "matched_expected": (c.returncode == exp_rc) and (not exp_code or exp_code in err_s),
                "stderr": err_s,
            }
        results["packed_drop_type_rules"] = pdt_results

        # ------------------------------------------------------------------
        # 4. drop_in_place -Z ub-checks=yes gap vs direct &mut *ptr vs Miri
        # ------------------------------------------------------------------
        raw_drop_rs = tmp / "raw_drop_in_place.rs"
        raw_drop_rs.write_text(RAW_DROP_IN_PLACE_RS)
        mir_raw_drop = tmp / "mir_raw_drop"
        mir_raw_drop.mkdir()
        raw_drop_bin = tmp / "raw_drop_ub"
        c_raw_ub = run_cmd([
            "rustc", "--edition=2021", "-C", "opt-level=0", "-Z", "ub-checks=yes",
            "-Z", "dump-mir=CheckAlignment|Inline",
            "-Z", f"dump-mir-dir={mir_raw_drop}",
            "-o", str(raw_drop_bin), str(raw_drop_rs),
        ])
        r_raw_ub = run_cmd([str(raw_drop_bin)]) if c_raw_ub.returncode == 0 else None
        raw_drop_bin_o2 = tmp / "raw_drop_ub_o2"
        c_raw_ub_o2 = run_cmd([
            "rustc", "--edition=2021", "-C", "opt-level=2", "-Z", "ub-checks=yes",
            "-o", str(raw_drop_bin_o2), str(raw_drop_rs),
        ])
        r_raw_ub_o2 = run_cmd([str(raw_drop_bin_o2)]) if c_raw_ub_o2.returncode == 0 else None
        raw_miri_sb = run_miri_file(miri_bin, miri_sysroot, raw_drop_rs, [], reps)
        raw_miri_tb = run_miri_file(miri_bin, miri_sysroot, raw_drop_rs, ["-Zmiri-tree-borrows"], reps)

        # Control: direct `&mut *ptr` in `main` under `-Z ub-checks=yes`
        ctrl_rs = tmp / "direct_mut_deref_control.rs"
        ctrl_rs.write_text(DIRECT_MUT_DEREF_CONTROL_RS)
        ctrl_bin = tmp / "direct_mut_deref_ub"
        c_ctrl = run_cmd([
            "rustc", "--edition=2021", "-C", "opt-level=0", "-Z", "ub-checks=yes",
            "-o", str(ctrl_bin), str(ctrl_rs),
        ])
        r_ctrl = run_cmd([str(ctrl_bin)]) if c_ctrl.returncode == 0 else None
        ctrl_miri_sb = run_miri_file(miri_bin, miri_sysroot, ctrl_rs, [], reps)

        # Safe manual pattern: `read_unaligned` + `drop`
        safe_rs = tmp / "read_unaligned_safe_drop.rs"
        safe_rs.write_text(READ_UNALIGNED_SAFE_DROP_RS)
        safe_bin = tmp / "read_unaligned_safe_drop_ub"
        c_safe = run_cmd([
            "rustc", "--edition=2021", "-C", "opt-level=0", "-Z", "ub-checks=yes",
            "-o", str(safe_bin), str(safe_rs),
        ])
        r_safe = run_cmd([str(safe_bin)]) if c_safe.returncode == 0 else None
        safe_miri_sb = run_miri_file(miri_bin, miri_sysroot, safe_rs, [], reps)
        safe_miri_tb = run_miri_file(miri_bin, miri_sysroot, safe_rs, ["-Zmiri-tree-borrows"], reps)

        # Count `MisalignedPointerDereference` asserts in main's CheckAlignment MIR dump
        raw_main_check_align_asserts = 0
        for p in sorted(mir_raw_drop.glob("*.main.*.CheckAlignment.after.mir")):
            txt = p.read_text(errors="replace")
            raw_main_check_align_asserts += txt.count("MisalignedPointerDereference")
            key_mir_excerpts[p.name] = sanitize(txt, reps)
        for p in sorted(mir_raw_drop.glob("*.main.*.Inline.after.mir")):
            key_mir_excerpts[p.name] = sanitize(p.read_text(errors="replace"), reps)

        results["drop_in_place_ub_checks_gap"] = {
            "raw_drop_in_place": {
                "compile_ub_checks_rc": c_raw_ub.returncode,
                "ub_checks_rc": r_raw_ub.returncode if r_raw_ub else None,
                "ub_checks_stdout": sanitize(r_raw_ub.stdout.strip(), reps) if r_raw_ub else "",
                "ub_checks_stderr": sanitize(r_raw_ub.stderr.strip(), reps) if r_raw_ub else "",
                "ub_checks_o2_rc": r_raw_ub_o2.returncode if r_raw_ub_o2 else None,
                "ub_checks_o2_stdout": sanitize(r_raw_ub_o2.stdout.strip(), reps) if r_raw_ub_o2 else "",
                "main_check_alignment_asserts": raw_main_check_align_asserts,
                "miri_sb": raw_miri_sb,
                "miri_tb": raw_miri_tb,
            },
            "direct_mut_deref_control": {
                "compile_ub_checks_rc": c_ctrl.returncode,
                "ub_checks_rc": r_ctrl.returncode if r_ctrl else None,
                "ub_checks_stdout": sanitize(r_ctrl.stdout.strip(), reps) if r_ctrl else "",
                "ub_checks_stderr": sanitize(r_ctrl.stderr.strip(), reps) if r_ctrl else "",
                "miri_sb": ctrl_miri_sb,
            },
            "read_unaligned_safe_drop": {
                "compile_ub_checks_rc": c_safe.returncode,
                "ub_checks_rc": r_safe.returncode if r_safe else None,
                "ub_checks_stdout": sanitize(r_safe.stdout.strip(), reps) if r_safe else "",
                "miri_sb": safe_miri_sb,
                "miri_tb": safe_miri_tb,
            },
        }

        # ------------------------------------------------------------------
        # 5. RemoveUninitDrops (const_precise_live_drops vs non-const)
        # ------------------------------------------------------------------
        rud_rs = tmp / "remove_uninit_drops_const.rs"
        rud_rs.write_text(REMOVE_UNINIT_DROPS_CONST_RS)
        mir_rud = tmp / "mir_rud"
        mir_rud.mkdir()
        rud_bin = tmp / "remove_uninit_drops_const"
        c_rud = run_cmd([
            "rustc", "--edition=2021", "-C", "opt-level=0",
            "-Z", "dump-mir=RemoveUninitDrops|ElaborateDrops",
            "-Z", f"dump-mir-dir={mir_rud}",
            "-o", str(rud_bin), str(rud_rs),
        ])
        r_rud = run_cmd([str(rud_bin)]) if c_rud.returncode == 0 else None
        rud_counts = parse_mir_counts(mir_rud)
        for p in sorted(mir_rud.glob("*.mir")):
            if "const_extract_both" in p.name or "runtime_extract_both" in p.name:
                key_mir_excerpts[p.name] = sanitize(p.read_text(errors="replace"), reps)

        # Also compile without `#![feature(const_precise_live_drops)]` to prove `RemoveUninitDrops`
        # does not run on normal non-const crates.
        rud_plain_rs = tmp / "no_feature_plain.rs"
        rud_plain_rs.write_text(
            "pub struct NonCopy(pub u32); impl Drop for NonCopy { fn drop(&mut self) {} }\n"
            "pub fn f(x: NonCopy) -> NonCopy { x }\nfn main() { let _ = f(NonCopy(1)); }\n"
        )
        mir_plain = tmp / "mir_plain"
        mir_plain.mkdir()
        c_plain = run_cmd([
            "rustc", "--edition=2021", "-C", "opt-level=0",
            "-Z", "dump-mir=RemoveUninitDrops",
            "-Z", f"dump-mir-dir={mir_plain}",
            "-o", str(tmp / "plain_bin"), str(rud_plain_rs),
        ])
        plain_rud_files = sorted(p.name for p in mir_plain.glob("*RemoveUninitDrops*.mir"))

        results["remove_uninit_drops_const"] = {
            "compile_rc": c_rud.returncode,
            "run_rc": r_rud.returncode if r_rud else None,
            "run_stdout": sanitize(r_rud.stdout.strip(), reps) if r_rud else "",
            "mir_dump_counts": rud_counts,
            "plain_non_const_crate_compile_rc": c_plain.returncode,
            "plain_non_const_remove_uninit_drops_dumps": plain_rud_files,
        }

        if args.save_mir_excerpts:
            ex_dir = Path(args.save_mir_excerpts)
            ex_dir.mkdir(parents=True, exist_ok=True)
            for fn, content in key_mir_excerpts.items():
                (ex_dir / fn).write_text(content)

        # Check overall acceptance assertions
        checks = {
            "packed_ok_native_1637": results["packed_ok"]["native_rc"] == 0 and results["packed_ok"]["native_stdout"] == "PACKED_DROP_LOG=1637",
            "packed_ok_ub_checks_1637": results["packed_ok"]["ub_checks_rc"] == 0 and results["packed_ok"]["ub_checks_stdout"] == "PACKED_DROP_LOG=1637",
            "packed_ok_miri_sb_1637": miri_sb["rc"] == 0 and miri_sb["stdout"] == "PACKED_DROP_LOG=1637",
            "packed_ok_miri_tb_1637": miri_tb["rc"] == 0 and miri_tb["stdout"] == "PACKED_DROP_LOG=1637",
            "all_check_packed_ref_matched": all(v["matched_expected"] for v in cpr_results.values()),
            "all_packed_drop_type_rules_matched": all(v["matched_expected"] for v in pdt_results.values()),
            "raw_drop_ub_checks_bypassed": (
                results["drop_in_place_ub_checks_gap"]["raw_drop_in_place"]["ub_checks_rc"] == 0
                and results["drop_in_place_ub_checks_gap"]["raw_drop_in_place"]["ub_checks_stdout"] == "RAW_DROP_UB_CHECKS_SURVIVED=true"
                and raw_main_check_align_asserts == 0
            ),
            "raw_drop_miri_sb_caught": raw_miri_sb["rc"] == 1 and "unaligned reference" in raw_miri_sb["stderr"],
            "raw_drop_miri_tb_caught": raw_miri_tb["rc"] == 1 and "unaligned reference" in raw_miri_tb["stderr"],
            "direct_mut_deref_ub_checks_caught": (
                results["drop_in_place_ub_checks_gap"]["direct_mut_deref_control"]["ub_checks_rc"] != 0
                and "misaligned pointer dereference" in results["drop_in_place_ub_checks_gap"]["direct_mut_deref_control"]["ub_checks_stderr"]
            ),
            "safe_read_unaligned_drop_passes_all": (
                results["drop_in_place_ub_checks_gap"]["read_unaligned_safe_drop"]["ub_checks_rc"] == 0
                and results["drop_in_place_ub_checks_gap"]["read_unaligned_safe_drop"]["ub_checks_stdout"] == "SAFE_READ_UNALIGNED_DROP=42"
                and safe_miri_sb["rc"] == 0
                and safe_miri_tb["rc"] == 0
            ),
            "remove_uninit_drops_const_runs_only_with_feature": (
                c_rud.returncode == 0
                and results["remove_uninit_drops_const"]["run_stdout"] == "CONST_RES=30 RT_RES=7"
                and len(plain_rud_files) == 0
            ),
        }
        results["checks"] = checks
        results["all_checks_passed"] = all(checks.values())

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"all_checks_passed": results["all_checks_passed"], "checks": results["checks"]}, indent=2))
    return 0 if results["all_checks_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
