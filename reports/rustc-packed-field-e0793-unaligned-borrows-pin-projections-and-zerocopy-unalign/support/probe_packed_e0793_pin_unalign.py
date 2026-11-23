#!/usr/bin/env python3
"""Reproducible empirical probes for rustc CheckPackedRef (E0793),
AddMovesForPackedDrops, Miri alignment UB, Pin/Unpin structural projections,
and zerocopy::Unalign<T>.

Runs every compilation, MIR dump, binary, and cargo +nightly miri test strictly
inside `with tempfile.TemporaryDirectory():` and writes structured JSON output
with local host/user paths redacted.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
from typing import Any


def make_env() -> dict[str, str]:
    env = os.environ.copy()
    cargo_bin = os.path.expanduser("~/.cargo/bin")
    if os.path.isdir(cargo_bin):
        env["PATH"] = f"{cargo_bin}:{env.get('PATH', '')}"
    return env


def redact_text(text: str, extra_roots: list[str] | None = None) -> str:
    if not text:
        return text
    out = text
    if extra_roots:
        for idx, root in enumerate(extra_roots):
            if root:
                label = "<zerocopy_src>" if idx == 0 else "<tmp>"
                out = out.replace(root, label)
    home = os.path.expanduser("~")
    if home:
        out = out.replace(home, "<home>")
    out = re.sub(r"/tmp/tmp[A-Za-z0-9_]+", "<tmp>", out)
    out = re.sub(r"/var/tmp/[A-Za-z0-9_./-]+", "<var_tmp>", out)
    out = re.sub(
        r"<home>/\.rustup/toolchains/[^/]+/lib/rustlib/src/rust/",
        "<rustlib_src>/",
        out,
    )
    out = re.sub(
        r"/rustc/[0-9a-f]{40}/",
        "<rustc_sysroot>/",
        out,
    )
    return out


def run_cmd(
    cmd: list[str],
    cwd: pathlib.Path,
    env: dict[str, str],
    extra_roots: list[str] | None = None,
) -> dict[str, Any]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
        timeout=180,
    )
    return {
        "returncode": proc.returncode,
        "stdout": redact_text(proc.stdout.strip(), extra_roots),
        "stderr": redact_text(proc.stderr.strip(), extra_roots),
    }


def run_rustc_case(
    code: str,
    env: dict[str, str],
    edition: str = "2024",
    extra_args: list[str] | None = None,
    execute: bool = False,
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        tdir = pathlib.Path(td)
        src = tdir / "probe.rs"
        exe = tdir / "probe_bin"
        src.write_text(code, encoding="utf-8")
        cmd = ["rustc", f"--edition={edition}", str(src), "-o", str(exe)]
        if extra_args:
            cmd.extend(extra_args)
        comp = run_cmd(cmd, tdir, env, extra_roots=[None, str(tdir)])
        result: dict[str, Any] = {
            "edition": edition,
            "extra_args": extra_args or [],
            "compile_returncode": comp["returncode"],
            "compile_stdout": comp["stdout"],
            "compile_stderr": comp["stderr"],
        }
        if execute and comp["returncode"] == 0:
            run = run_cmd([str(exe)], tdir, env, extra_roots=[None, str(tdir)])
            result["run_returncode"] = run["returncode"]
            result["run_stdout"] = run["stdout"]
            result["run_stderr"] = run["stderr"]
        return result


def run_miri_case(
    main_rs: str,
    env: dict[str, str],
    edition: str = "2024",
    miriflags: str | None = None,
    zerocopy_src: pathlib.Path | None = None,
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        tdir = pathlib.Path(td)
        src_dir = tdir / "src"
        src_dir.mkdir()
        deps = ""
        if zerocopy_src is not None:
            deps = f'zerocopy = {{ path = "{zerocopy_src}" }}\n'
        (tdir / "Cargo.toml").write_text(
            f'[package]\nname = "miri_probe"\nversion = "0.1.0"\nedition = "{edition}"\n'
            f'[dependencies]\n{deps}',
            encoding="utf-8",
        )
        (src_dir / "main.rs").write_text(main_rs, encoding="utf-8")
        run_env = env.copy()
        if miriflags:
            run_env["MIRIFLAGS"] = miriflags
        cmd = ["cargo", "+nightly", "miri", "run", "--offline"]
        roots = [str(zerocopy_src) if zerocopy_src else "", str(tdir)]
        res = run_cmd(cmd, tdir, run_env, extra_roots=roots)
        res["edition"] = edition
        res["miriflags"] = miriflags or ""
        res["command"] = (
            f"MIRIFLAGS={miriflags} " if miriflags else ""
        ) + "cargo +nightly miri run --offline"
        return res


def probe_e0793_and_acceptance_boundary(env: dict[str, str]) -> dict[str, Any]:
    rejected_src = r'''#![allow(dead_code)]
#[repr(C, packed(1))]
struct Pack1 {
    a_u8: u8,
    b_u32: u32,
}

#[repr(C, packed(2))]
struct Pack2 {
    a_u8: u8,
    b_u16: u16,
    c_u32: u32,
}

#[repr(C, packed(4))]
struct Pack4 {
    a_u8: u8,
    b_u32: u32,
    c_u64: u64,
}

#[repr(C, packed(4))]
struct InnerP4 {
    x: u32,
}

#[repr(C, packed(2))]
struct NestedP2P4 {
    tag: u8,
    inner: InnerP4,
}

#[repr(C, packed(1))]
struct SliceTailU32 {
    tag: u8,
    tail: [u32],
}

#[repr(C, packed(1))]
union UnionPack1 {
    a: u8,
    b: u32,
}

fn borrow_u32(x: &u32) -> u32 {
    *x
}

fn check_slice_tail(s: &SliceTailU32) -> usize {
    (&s.tail).len()
}

fn main() {
    let p1 = Pack1 { a_u8: 1, b_u32: 0x11223344 };
    let p2 = Pack2 { a_u8: 1, b_u16: 0x2233, c_u32: 0x44556677 };
    let p4 = Pack4 { a_u8: 1, b_u32: 0x12345678, c_u64: 0x0102030405060708 };
    let nested = NestedP2P4 { tag: 1, inner: InnerP4 { x: 42 } };
    let u = UnionPack1 { b: 99 };

    let _e1 = &p1.b_u32;
    let _e2 = &p2.c_u32;
    let _e3 = &p4.c_u64;
    let _e4 = format!("{}", p1.b_u32);
    let _e5 = borrow_u32(&p1.b_u32);
    let _e6 = &p1.b_u32 as *const u32;
    let _e7 = &nested.inner.x;
    let _e8 = unsafe { &u.b };
    let _ = check_slice_tail;
}
'''
    rejected = run_rustc_case(rejected_src, env, execute=False)

    accepted_src = r'''#![allow(dead_code)]
use core::ptr;

#[repr(C)]
struct AlignedTarget {
    x: u32,
}

#[repr(C, packed(1))]
struct Pack1<'a> {
    a_u8: u8,
    b_u32: u32,
    arr_u8: [u8; 4],
    r: &'a AlignedTarget,
}

#[repr(C, packed(2))]
struct Pack2 {
    a_u8: u8,
    b_u16: u16,
    c_u32: u32,
}

#[repr(C, packed(4))]
struct Pack4 {
    a_u8: u8,
    b_u32: u32,
}

#[repr(C, packed(1))]
struct SliceTailU8 {
    tag: u8,
    tail: [u8],
}

fn take_u8(x: &u8) -> u8 { *x }
fn take_u16(x: &u16) -> u16 { *x }
fn take_u32(x: &u32) -> u32 { *x }
fn take_u8_slice(s: &[u8]) -> usize { s.len() }

fn make_dst_u8() -> usize {
    let raw: [u8; 4] = [7, 10, 20, 30];
    // SAFETY: SliceTailU8 has repr(C, packed(1)) -> align 1, size = 1 + 3 = 4.
    let dst: &SliceTailU8 = unsafe { &*(ptr::slice_from_raw_parts(raw.as_ptr(), 3) as *const SliceTailU8) };
    take_u8_slice(&dst.tail)
}

fn main() {
    static TARGET: AlignedTarget = AlignedTarget { x: 0x778899aa };
    let mut p1 = Pack1 { a_u8: 7, b_u32: 0x12345678, arr_u8: [1, 2, 3, 4], r: &TARGET };
    let p2 = Pack2 { a_u8: 10, b_u16: 0x4242, c_u32: 0xdeadbeef };
    let p4 = Pack4 { a_u8: 1, b_u32: 0xcafebabe };

    let ra = take_u8(&p1.a_u8);
    let rarr = take_u8_slice(&p1.arr_u8);
    let rb2 = take_u16(&p2.b_u16);
    let rb4 = take_u32(&p4.b_u32);
    let r_deref = take_u32(&(*p1.r).x);
    let tail_len = make_dst_u8();

    let copy_b = p1.b_u32;
    let brace_b = { p1.b_u32 };
    let copy_c2 = p2.c_u32;

    let raw_const = &raw const p1.b_u32;
    let raw_before = unsafe { ptr::read_unaligned(raw_const) };
    let raw_mut = &raw mut p1.b_u32;
    unsafe { ptr::write_unaligned(raw_mut, 0x87654321) };
    let raw_after = p1.b_u32;

    println!(
        "RA={} RARR={} RB2={:#x} RB4={:#x} DEREF={:#x} TAIL_LEN={} COPY={:#x} BRACE={:#x} C2={:#x} RAW_BEFORE={:#x} RAW_AFTER={:#x}",
        ra, rarr, rb2, rb4, r_deref, tail_len, copy_b, brace_b, copy_c2, raw_before, raw_after
    );
}
'''
    accepted = run_rustc_case(accepted_src, env, execute=True)

    # Also test packed union E0793 rejection vs raw ptr / copy
    # and test &(*p1.r) vs &p1.r separately
    deref_vs_direct_src = r'''#[repr(C)]
struct AlignedTarget { x: u32 }
#[repr(C, packed(1))]
struct Pack1<'a> { tag: u8, r: &'a AlignedTarget }
fn main() {
    static T: AlignedTarget = AlignedTarget { x: 5 };
    let p = Pack1 { tag: 1, r: &T };
    let _ok: &u32 = &(*p.r).x;
    let _bad = &p.r;
}
'''
    deref_vs_direct = run_rustc_case(deref_vs_direct_src, env, execute=False)

    return {
        "rejected_e0793": rejected,
        "accepted_boundary": accepted,
        "deref_reset_vs_direct_ref_borrow": deref_vs_direct,
    }


def probe_add_moves_for_packed_drops(env: dict[str, str]) -> dict[str, Any]:
    mir_src = r'''use core::sync::atomic::{AtomicUsize, Ordering};

static DROPS: AtomicUsize = AtomicUsize::new(0);
static LAST_DROP_ADDR: AtomicUsize = AtomicUsize::new(0);
static LAST_DROP_MOD4: AtomicUsize = AtomicUsize::new(99);

struct DropCounted(u32);

impl Drop for DropCounted {
    #[inline(never)]
    fn drop(&mut self) {
        let addr = (self as *const Self) as usize;
        LAST_DROP_ADDR.store(addr, Ordering::Relaxed);
        LAST_DROP_MOD4.store(addr % 4, Ordering::Relaxed);
        DROPS.fetch_add(self.0 as usize, Ordering::Relaxed);
    }
}

#[repr(C, packed(1))]
struct Packed1Drop {
    tag: u8,
    d: DropCounted,
}

#[repr(C, packed(4))]
struct Packed4Drop {
    tag: u8,
    d: DropCounted,
}

#[inline(never)]
fn reassign_packed1_drop(mut p: Packed1Drop) -> u32 {
    p.d = DropCounted(7);
    (p.tag as u32) + p.d.0
}

#[inline(never)]
fn reassign_packed4_drop(mut p: Packed4Drop) -> u32 {
    p.d = DropCounted(9);
    (p.tag as u32) + p.d.0
}

#[repr(C, align(4))]
struct AlignedHolder1 {
    _align: [u32; 0],
    p: Packed1Drop,
}

fn main() {
    let h1 = AlignedHolder1 { _align: [], p: Packed1Drop { tag: 1, d: DropCounted(41) } };
    let field_addr_p1 = (&raw const h1.p.d) as usize;
    let sum1 = reassign_packed1_drop(h1.p);
    let drop_addr_p1 = LAST_DROP_ADDR.load(Ordering::Relaxed);
    let drop_mod4_p1 = LAST_DROP_MOD4.load(Ordering::Relaxed);

    let p4 = Packed4Drop { tag: 2, d: DropCounted(10) };
    let sum4 = reassign_packed4_drop(p4);
    println!(
        "SUM1={} SUM4={} DROPS={} FIELD_MOD4={} DROP_MOD4={} RELOCATED={}",
        sum1,
        sum4,
        DROPS.load(Ordering::Relaxed),
        field_addr_p1 % 4,
        drop_mod4_p1,
        field_addr_p1 != drop_addr_p1
    );
}
'''
    with tempfile.TemporaryDirectory() as td:
        tdir = pathlib.Path(td)
        src = tdir / "mir_probe.rs"
        exe = tdir / "mir_probe_bin"
        dump_dir = tdir / "mir_dump"
        dump_dir.mkdir()
        src.write_text(mir_src, encoding="utf-8")
        cmd = [
            "rustc",
            "--edition=2024",
            "-Zdump-mir=AddMovesForPackedDrops",
            f"-Zdump-mir-dir={dump_dir}",
            str(src),
            "-o",
            str(exe),
        ]
        comp = run_cmd(cmd, tdir, env, extra_roots=[None, str(tdir)])
        run = run_cmd([str(exe)], tdir, env, extra_roots=[None, str(tdir)]) if comp["returncode"] == 0 else {}
        dumps: dict[str, list[str]] = {}
        for f in sorted(dump_dir.iterdir()):
            if "reassign_packed1_drop" in f.name or "reassign_packed4_drop" in f.name:
                dumps[f.name] = f.read_text(encoding="utf-8").splitlines()
        return {
            "compile_returncode": comp["returncode"],
            "compile_stderr": comp["stderr"],
            "run": run,
            "mir_dumps": dumps,
        }


def probe_miri_alignment(env: dict[str, str]) -> dict[str, Any]:
    safe_src = r'''use core::ptr;
use core::sync::atomic::{AtomicUsize, Ordering};

static DROPS: AtomicUsize = AtomicUsize::new(0);

struct DropVal(u32);
impl Drop for DropVal {
    fn drop(&mut self) {
        assert_eq!((self as *const Self as usize) % 4, 0);
        DROPS.fetch_add(self.0 as usize, Ordering::Relaxed);
    }
}

#[repr(C, packed(1))]
struct Packed {
    tag: u8,
    val: u32,
    drop_val: DropVal,
}

#[repr(C, align(4))]
struct AlignedWrap {
    _align: [u32; 0],
    p: Packed,
}

fn main() {
    let mut wrap = AlignedWrap { _align: [], p: Packed { tag: 1, val: 0x12345678, drop_val: DropVal(14) } };
    let raw = &raw mut wrap.p.val;
    let mod4 = (raw as usize) % 4;
    let v1 = unsafe { ptr::read_unaligned(raw) };
    unsafe { ptr::write_unaligned(raw, 0xcafebabe) };
    let v2 = wrap.p.val;
    drop(wrap);
    assert_eq!(mod4, 1);
    assert_eq!(v1, 0x12345678);
    assert_eq!(v2, 0xcafebabe);
    assert_eq!(DROPS.load(Ordering::Relaxed), 14);
    println!("MIRI_PACKED_SAFE_OK mod4={} v1={:#x} v2={:#x} drops={}", mod4, v1, v2, DROPS.load(Ordering::Relaxed));
}
'''
    ub_ref_src = r'''use core::ptr;

#[repr(C, packed(1))]
struct Packed {
    tag: u8,
    val: u32,
}

#[repr(C, align(4))]
struct AlignedWrap {
    _align: [u32; 0],
    p: Packed,
}

fn main() {
    let wrap = AlignedWrap { _align: [], p: Packed { tag: 1, val: 0x12345678 } };
    let raw: *const u32 = ptr::addr_of!(wrap.p.val);
    assert_eq!((raw as usize) % 4, 1);
    let bad_ref: &u32 = unsafe { &*raw };
    let _ = bad_ref;
}
'''
    ub_raw_deref_src = r'''use core::ptr;

#[repr(C, packed(1))]
struct Packed {
    tag: u8,
    val: u32,
}

#[repr(C, align(4))]
struct AlignedWrap {
    _align: [u32; 0],
    p: Packed,
}

fn main() {
    let wrap = AlignedWrap { _align: [], p: Packed { tag: 1, val: 0x12345678 } };
    let raw: *const u32 = ptr::addr_of!(wrap.p.val);
    assert_eq!((raw as usize) % 4, 1);
    let _bad_load: u32 = unsafe { *raw };
}
'''
    ub_zst_ref_src = r'''#[repr(align(4))]
struct Align4Zst;

#[repr(C, align(4))]
struct AlignedBuf([u8; 8]);

fn main() {
    let buf = AlignedBuf([0u8; 8]);
    let raw_zst = unsafe { buf.0.as_ptr().add(1) } as *const Align4Zst;
    assert_eq!((raw_zst as usize) % 4, 1);
    let _bad_zst_ref: &Align4Zst = unsafe { &*raw_zst };
}
'''
    return {
        "miri_safe_packed_raw_rw_and_drop_sb": run_miri_case(safe_src, env),
        "miri_safe_packed_raw_rw_and_drop_tb": run_miri_case(
            safe_src, env, miriflags="-Zmiri-tree-borrows"
        ),
        "miri_unaligned_reference_ub_caught": run_miri_case(ub_ref_src, env),
        "miri_unaligned_raw_deref_load_ub_caught": run_miri_case(ub_raw_deref_src, env),
        "miri_unaligned_zst_reference_ub_caught": run_miri_case(ub_zst_ref_src, env),
    }


def probe_pin_and_projections(env: dict[str, str]) -> dict[str, Any]:
    rejected_src = r'''use core::marker::PhantomPinned;
use core::pin::Pin;

struct PinnedState {
    val: u32,
    _pin: PhantomPinned,
}

fn try_new(s1: &mut PinnedState) -> Pin<&mut PinnedState> {
    Pin::new(s1)
}

fn try_get_mut(p: Pin<&mut PinnedState>) -> &mut PinnedState {
    p.get_mut()
}

fn try_into_inner(p: Pin<&mut PinnedState>) -> &mut PinnedState {
    Pin::into_inner(p)
}

fn try_swap(mut p1: Pin<&mut PinnedState>, mut p2: Pin<&mut PinnedState>) {
    core::mem::swap(&mut *p1, &mut *p2);
}

fn main() {
    let _ = (try_new, try_get_mut, try_into_inner, try_swap);
}
'''
    pin_exec_src = r'''use core::marker::PhantomPinned;
use core::pin::{Pin, pin};
use core::ptr::NonNull;

struct SelfRef {
    hdr: u32,
    buf: [u8; 4],
    ptr_to_buf: Option<NonNull<u8>>,
    _pin: PhantomPinned,
}

impl SelfRef {
    fn new(hdr: u32) -> Self {
        Self { hdr, buf: [10, 20, 30, 40], ptr_to_buf: None, _pin: PhantomPinned }
    }

    fn init(self: Pin<&mut Self>) {
        // SAFETY: Does not move `self`, writes self-pointer into pinned `self`.
        unsafe {
            let this = self.get_unchecked_mut();
            this.ptr_to_buf = NonNull::new(this.buf.as_mut_ptr());
        }
    }

    // Non-structural projection: `hdr` is `Unpin` and not address-pinned.
    fn project_hdr_unpinned(self: Pin<&mut Self>) -> &mut u32 {
        // SAFETY: `hdr` is never structurally pinned.
        unsafe { &mut self.get_unchecked_mut().hdr }
    }

    // Structural projection: `buf` is structurally pinned.
    fn project_buf_pinned(self: Pin<&mut Self>) -> Pin<&mut [u8; 4]> {
        // SAFETY: `buf` stays at its address while `self` is pinned.
        unsafe { self.map_unchecked_mut(|s| &mut s.buf) }
    }

    fn read_via_self_ptr(&self) -> u8 {
        unsafe { *self.ptr_to_buf.unwrap().as_ptr() }
    }
}

fn main() {
    let mut a = 11u32;
    let mut b = 22u32;
    let mut pa = Pin::new(&mut a);
    let mut pb = Pin::new(&mut b);
    core::mem::swap(&mut *pa, &mut *pb);
    let get_mut_val = *pa.as_mut().get_mut();
    let into_inner_val = *Pin::into_inner(pb);

    let mut pinned = pin!(SelfRef::new(7));
    pinned.as_mut().init();
    *pinned.as_mut().project_hdr_unpinned() = 42;
    let addr_before = pinned.as_ref().get_ref().buf.as_ptr() as usize;
    let mut pinned_buf = pinned.as_mut().project_buf_pinned();
    let addr_proj = pinned_buf.as_mut().as_ref().get_ref().as_ptr() as usize;
    let first_byte = pinned.as_ref().read_via_self_ptr();
    assert_eq!(addr_before, addr_proj);
    println!(
        "UNPIN_SWAPPED={} GET_MUT={} INTO_INNER={} STRUCTURAL_HDR={} SELF_BYTE={} ADDR_STABLE={}",
        a == 22 && b == 11,
        get_mut_val,
        into_inner_val,
        pinned.hdr,
        first_byte,
        addr_before == addr_proj
    );
}
'''
    # Also test packed struct Drop moving a non-aligned field and changing its address
    packed_drop_addr_src = r'''use core::sync::atomic::{AtomicUsize, Ordering};

static DROPPED_AT: AtomicUsize = AtomicUsize::new(0);
struct WatchDrop(u32);
impl Drop for WatchDrop {
    #[inline(never)]
    fn drop(&mut self) {
        DROPPED_AT.store(self as *const Self as usize, Ordering::Relaxed);
    }
}

#[repr(C, packed)]
struct PackedWrapper {
    pad: u8,
    inner: WatchDrop,
}

#[repr(C, align(4))]
struct AlignedWrap {
    _align: [u32; 0],
    w: PackedWrapper,
}

fn main() {
    let wrap = AlignedWrap { _align: [], w: PackedWrapper { pad: 1, inner: WatchDrop(5) } };
    let field_addr = (&raw const wrap.w.inner) as usize;
    drop(wrap);
    let drop_addr = DROPPED_AT.load(Ordering::Relaxed);
    println!(
        "FIELD_MOD4={} DROP_MOD4={} ADDR_CHANGED={}",
        field_addr % 4,
        drop_addr % 4,
        field_addr != drop_addr
    );
}
'''
    return {
        "not_unpin_phantom_pinned_rejected": run_rustc_case(rejected_src, env, execute=False),
        "unpin_and_structural_pin_projection_exec": run_rustc_case(pin_exec_src, env, execute=True),
        "unpin_and_structural_pin_projection_miri_tb": run_miri_case(
            pin_exec_src, env, miriflags="-Zmiri-tree-borrows"
        ),
        "packed_drop_relocation_breaks_address_stability_miri": run_miri_case(
            packed_drop_addr_src, env, miriflags="-Zmiri-tree-borrows"
        ),
    }


def probe_zerocopy_unalign(
    env: dict[str, str], zerocopy_src: pathlib.Path | None
) -> dict[str, Any]:
    if zerocopy_src is None or not zerocopy_src.is_dir():
        return {
            "status": "skipped",
            "reason": "no --zerocopy-src directory provided or found",
        }

    probe_rs = r'''use core::cell::Cell;
use core::mem::{align_of, size_of};
use std::panic::{AssertUnwindSafe, catch_unwind};
use zerocopy::{FromBytes, Unalign};

#[repr(C, align(4))]
struct AlignedBuf([u8; 16]);

fn main() {
    assert_eq!(size_of::<Unalign<u32>>(), 4);
    assert_eq!(align_of::<Unalign<u32>>(), 1);

    let mut u = Unalign::new(0xdeadbeefu32);
    let got = u.get();
    u.set(0x11223344);
    let after_set = u.get();

    // Unaligned address inside an aligned byte buffer (offset 1 -> mod 4 == 1)
    let mut buf = AlignedBuf([0u8; 16]);
    let mis_bytes: &mut [u8; 4] = (&mut buf.0[1..5]).try_into().unwrap();
    let mis_ref: &mut Unalign<u32> = FromBytes::mut_from_bytes(mis_bytes).unwrap();
    mis_ref.set(0x01020304);
    let mis_mod4 = (mis_ref as *const Unalign<u32> as usize) % 4;
    let mis_deref_ok = mis_ref.try_deref().is_ok();
    let mis_deref_mut_ok = mis_ref.try_deref_mut().is_ok();
    let mis_get = mis_ref.get();
    mis_ref.update(|x| *x = x.wrapping_add(1));
    let after_update = mis_ref.get();

    // Verify WriteBackOnDrop writes back even if callback panics
    let _ = catch_unwind(AssertUnwindSafe(|| {
        mis_ref.update(|x| {
            *x = 0x55667788;
            panic!("unwind inside Unalign::update");
        });
    }));
    let after_unwind = mis_ref.get();

    // Aligned address (offset 0 -> mod 4 == 0)
    let al_bytes: &[u8; 4] = (&buf.0[0..4]).try_into().unwrap();
    let al_ref: &Unalign<u32> = FromBytes::ref_from_bytes(al_bytes).unwrap();
    let al_mod4 = (al_ref as *const Unalign<u32> as usize) % 4;
    let al_buf_deref = *al_ref.try_deref().unwrap();
    let al_mut = Unalign::new(0xcafebabeu32);
    let al_mut_mod4 = (&al_mut as *const Unalign<u32> as usize) % 4;
    let al_deref = *al_mut.try_deref().unwrap();

    // Non-Copy inner type inside Unalign<Cell<u32>>: update works via stack copy
    let mut uc = Unalign::new(Cell::new(7u32));
    uc.update(|c| c.set(c.get() + 70));
    let cell_inner = uc.into_inner().into_inner();

    // T: Unaligned enables Deref
    let ua = Unalign::new([1u8, 2, 3, 4]);
    let deref_unaligned_first = (*ua)[0];

    println!(
        "ZC_SIZE={} ZC_ALIGN={} GET={:#x} SET={:#x} MIS_MOD4={} MIS_DEREF={} MIS_DEREF_MUT={} MIS_GET={:#x} AFTER_UPDATE={:#x} AFTER_UNWIND={:#x} AL_MOD4={} AL_BUF_DEREF={} AL_DEREF={:#x} CELL_INNER={} UNALIGNED_DEREF={}",
        size_of::<Unalign<u32>>(),
        align_of::<Unalign<u32>>(),
        got,
        after_set,
        mis_mod4,
        mis_deref_ok,
        mis_deref_mut_ok,
        mis_get,
        after_update,
        after_unwind,
        al_mod4 | al_mut_mod4,
        al_buf_deref,
        al_deref,
        cell_inner,
        deref_unaligned_first
    );
}
'''

    neg_deref_rs = r'''use core::ops::Deref;
use zerocopy::Unalign;

fn bad_deref(u: &Unalign<u32>) -> &u32 {
    Deref::deref(u)
}

fn main() {
    let u = Unalign::new(1u32);
    let _ = bad_deref(&u);
}
'''

    with tempfile.TemporaryDirectory() as td:
        tdir = pathlib.Path(td)
        zc_rlib = tdir / "libzerocopy.rlib"
        zc_env = env.copy()
        cargo_toml = zerocopy_src / "Cargo.toml"
        pkg_ver = "0.8.64"
        if cargo_toml.is_file():
            m = re.search(r'^version\s*=\s*"([^"]+)"', cargo_toml.read_text(encoding="utf-8"), re.M)
            if m:
                pkg_ver = m.group(1)
        zc_env["CARGO_PKG_VERSION"] = pkg_ver
        lib_cmd = [
            "rustc",
            "--edition=2021",
            "--crate-name",
            "zerocopy",
            "--crate-type",
            "lib",
            str(zerocopy_src / "src" / "lib.rs"),
            "-o",
            str(zc_rlib),
        ]
        lib_res = run_cmd(lib_cmd, tdir, zc_env, extra_roots=[str(zerocopy_src), str(tdir)])

        probe_path = tdir / "zc_probe.rs"
        probe_exe = tdir / "zc_probe_bin"
        probe_path.write_text(probe_rs, encoding="utf-8")
        pos_comp = run_cmd(
            [
                "rustc",
                "--edition=2024",
                str(probe_path),
                "--extern",
                f"zerocopy={zc_rlib}",
                "-o",
                str(probe_exe),
            ],
            tdir,
            env,
            extra_roots=[str(zerocopy_src), str(tdir)],
        )
        pos_run = (
            run_cmd([str(probe_exe)], tdir, env, extra_roots=[str(zerocopy_src), str(tdir)])
            if pos_comp["returncode"] == 0
            else {}
        )

        neg_path = tdir / "zc_neg.rs"
        neg_exe = tdir / "zc_neg_bin"
        neg_path.write_text(neg_deref_rs, encoding="utf-8")
        neg_comp = run_cmd(
            [
                "rustc",
                "--edition=2024",
                str(neg_path),
                "--extern",
                f"zerocopy={zc_rlib}",
                "-o",
                str(neg_exe),
            ],
            tdir,
            env,
            extra_roots=[str(zerocopy_src), str(tdir)],
        )

    # Also run real zerocopy::Unalign under Miri (Tree Borrows)
    miri_zc_rs = r'''use core::cell::Cell;
use zerocopy::{FromBytes, Unalign};

#[repr(C, align(4))]
struct AlignedBuf([u8; 16]);

fn main() {
    let mut buf = AlignedBuf([0u8; 16]);
    let mis_bytes: &mut [u8; 4] = (&mut buf.0[1..5]).try_into().unwrap();
    let mis_ref: &mut Unalign<u32> = FromBytes::mut_from_bytes(mis_bytes).unwrap();
    mis_ref.set(0xdeadbeef);
    assert!((mis_ref as *const Unalign<u32> as usize) % 4 != 0);
    assert!(mis_ref.try_deref().is_err());
    assert!(mis_ref.try_deref_mut().is_err());
    mis_ref.update(|x| *x = x.wrapping_add(1));
    assert_eq!(mis_ref.get(), 0xdeadbef0);

    let al_bytes: &mut [u8; 4] = (&mut buf.0[4..8]).try_into().unwrap();
    let al_ref: &mut Unalign<u32> = FromBytes::mut_from_bytes(al_bytes).unwrap();
    al_ref.set(0x12345678);
    assert_eq!(*al_ref.try_deref().unwrap(), 0x12345678);

    let mut uc = Unalign::new(Cell::new(7u32));
    uc.update(|c| c.set(c.get() + 70));
    assert_eq!(uc.into_inner().into_inner(), 77);
    println!("MIRI_ZEROCOPY_UNALIGN_OK");
}
'''
    miri_res = run_miri_case(
        miri_zc_rs,
        env,
        edition="2024",
        miriflags="-Zmiri-tree-borrows",
        zerocopy_src=zerocopy_src,
    )

    return {
        "status": "executed",
        "edition_zerocopy": "2021",
        "edition_probe": "2024",
        "lib_compile": lib_res,
        "probe_compile": pos_comp,
        "probe_run": pos_run,
        "negative_deref_requires_unaligned": neg_comp,
        "miri_zerocopy_unalign_tb": miri_res,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--zerocopy-src",
        default=os.environ.get("ZEROCOPY_SRC", ""),
        help="Path to google/zerocopy/zerocopy crate root (optional)",
    )
    parser.add_argument(
        "--out",
        default="",
        help="Output JSON file path (default: probe_results.json next to this script)",
    )
    args = parser.parse_args()

    env = make_env()
    zc_path = pathlib.Path(args.zerocopy_src).resolve() if args.zerocopy_src else None
    out_path = (
        pathlib.Path(args.out)
        if args.out
        else pathlib.Path(__file__).resolve().parent / "probe_results.json"
    )

    with tempfile.TemporaryDirectory() as td:
        tdir = pathlib.Path(td)
        rustc_ver = run_cmd(["rustc", "-vV"], tdir, env)
        miri_ver = run_cmd(["cargo", "+nightly", "miri", "--version"], tdir, env)

    results = {
        "rustc_version": rustc_ver["stdout"],
        "miri_version": miri_ver["stdout"],
        "experiments": {
            "a_packed_e0793_and_acceptance_boundary": probe_e0793_and_acceptance_boundary(env),
            "b_add_moves_for_packed_drops_mir": probe_add_moves_for_packed_drops(env),
            "c_miri_unaligned_load_vs_ub_reference": probe_miri_alignment(env),
            "d_pin_unpin_structural_projections": probe_pin_and_projections(env),
            "e_real_zerocopy_unalign_crate": probe_zerocopy_unalign(env, zc_path),
        },
    }

    out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {out_path} ({out_path.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
