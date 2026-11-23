#!/usr/bin/env python3
"""Live rustc, LLVM IR, Miri, and zerocopy::KnownLayout empirical probe.

Reproduces:
  A. Wide-pointer `ptr::eq` vs. `ptr::addr_eq` on slices and `dyn Trait` objects,
     including native LLVM execution vs. `cargo +nightly miri` vtable-salt
     divergence, cross-type vtable deduplication, and `-Copt-level=2` LLVM IR.
  B. Dynamic `mem::size_of_val` / `mem::align_of_val` on custom DSTs
     (`Packet<T: ?Sized>`, `Header6<T: ?Sized>`, `Packed2Slice`), `-Copt-level=2`
     LLVM IR lowering (`(align + size) & -align`), and real `zerocopy`
     `KnownLayout` / `DstLayout` overflow-checked and `isize::MAX` validation.

All compilations and executions run inside `tempfile.TemporaryDirectory()`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any


WIDE_PTR_PROBE_RS = r"""
use std::mem::ManuallyDrop;
use std::ptr;

trait Tr {
    fn tag(&self) -> u8;
}

trait SubTr: Tr {
    fn extra(&self) -> u8;
}

trait Marker {}

struct Inner(u8);

#[repr(C)]
struct Outer {
    inner: Inner,
    bias: u8,
}

impl Tr for Inner {
    fn tag(&self) -> u8 {
        self.0
    }
}

impl Tr for Outer {
    fn tag(&self) -> u8 {
        self.inner.0.wrapping_add(self.bias)
    }
}

impl SubTr for Outer {
    fn extra(&self) -> u8 {
        self.bias
    }
}

#[repr(C)]
struct TyA(u8);
#[repr(C)]
struct TyB(u8);

impl Marker for TyA {}
impl Marker for TyB {}

#[repr(C)]
union SameAddrPair {
    a: ManuallyDrop<TyA>,
    b: ManuallyDrop<TyB>,
}

#[inline(never)]
fn to_dyn_a(x: &Outer) -> &dyn Tr {
    x
}

#[inline(never)]
fn to_dyn_b(x: &Outer) -> &dyn Tr {
    x
}

#[inline(never)]
fn upcast_to_dyn(x: &Outer) -> &dyn Tr {
    let sub: &dyn SubTr = x;
    sub
}

fn main() {
    let arr = [10u8, 20, 30, 40];
    let s2: *const [u8] = &arr[..2];
    let s3: *const [u8] = &arr[..3];
    let s3b: *const [u8] = &arr[..3];
    let s_off: *const [u8] = &arr[1..3];

    let slice_addr_eq = ptr::addr_eq(s2, s3);
    let slice_eq_diff = ptr::eq(s2, s3);
    let slice_eq_same = ptr::eq(s3, s3b);
    let slice_off_addr_eq = ptr::addr_eq(s2, s_off);
    let slice_off_eq = ptr::eq(s2, s_off);
    let slice_thin_cast_eq = (s2 as *const ()) == (s3 as *const ());

    let obj = Outer {
        inner: Inner(7),
        bias: 5,
    };
    let dp_a: *const dyn Tr = to_dyn_a(&obj);
    let dp_b: *const dyn Tr = to_dyn_b(&obj);
    let dp_copy: *const dyn Tr = dp_a;
    let dp_upcast: *const dyn Tr = upcast_to_dyn(&obj);
    let dp_inner: *const dyn Tr = &obj.inner;

    let dyn_addr_eq = ptr::addr_eq(dp_a, dp_inner);
    let dyn_eq_diff_vtable = ptr::eq(dp_a, dp_inner);
    let dyn_eq_same_vtable = ptr::eq(dp_a, dp_b);
    let dyn_eq_copied = ptr::eq(dp_a, dp_copy);
    let dyn_eq_upcast = ptr::eq(dp_a, dp_upcast);

    // Distinct concrete types with identical layout/drop/methods for marker trait.
    let u = SameAddrPair {
        a: ManuallyDrop::new(TyA(1)),
    };
    let pa: *const dyn Marker = unsafe { &*u.a };
    let pb: *const dyn Marker = unsafe { &*u.b };
    let diff_types_addr_eq = ptr::addr_eq(pa, pb);
    let diff_types_ptr_eq = ptr::eq(pa, pb);

    println!(
        "SLICE_ADDR_EQ={} SLICE_EQ_DIFF={} SLICE_EQ_SAME={} SLICE_OFF_ADDR_EQ={} SLICE_OFF_EQ={} SLICE_THIN_CAST_EQ={} DYN_ADDR_EQ={} DYN_EQ_DIFF_VTABLE={} DYN_EQ_SAME_VTABLE={} DYN_EQ_COPIED={} DYN_EQ_UPCAST={} DIFF_TYPES_ADDR_EQ={} DIFF_TYPES_PTR_EQ={}",
        slice_addr_eq,
        slice_eq_diff,
        slice_eq_same,
        slice_off_addr_eq,
        slice_off_eq,
        slice_thin_cast_eq,
        dyn_addr_eq,
        dyn_eq_diff_vtable,
        dyn_eq_same_vtable,
        dyn_eq_copied,
        dyn_eq_upcast,
        diff_types_addr_eq,
        diff_types_ptr_eq,
    );
}
"""


LLVM_WIDE_PTR_IR_RS = r"""
#![crate_type = "lib"]

use std::ptr;

pub trait Tr {
    fn tag(&self) -> u8;
}

#[unsafe(no_mangle)]
pub extern "Rust" fn cmp_dyn_ptr_eq(a: *const dyn Tr, b: *const dyn Tr) -> bool {
    ptr::eq(a, b)
}

#[unsafe(no_mangle)]
pub extern "Rust" fn cmp_dyn_ptr_ne(a: *const dyn Tr, b: *const dyn Tr) -> bool {
    a != b
}

#[unsafe(no_mangle)]
pub extern "Rust" fn cmp_dyn_addr_eq(a: *const dyn Tr, b: *const dyn Tr) -> bool {
    ptr::addr_eq(a, b)
}

#[unsafe(no_mangle)]
pub extern "Rust" fn cmp_slice_ptr_eq(a: *const [u8], b: *const [u8]) -> bool {
    ptr::eq(a, b)
}

#[unsafe(no_mangle)]
pub extern "Rust" fn cmp_slice_addr_eq(a: *const [u8], b: *const [u8]) -> bool {
    ptr::addr_eq(a, b)
}
"""


CUSTOM_DST_PROBE_RS = r"""
use std::mem;

trait Tr {
    fn id(&self) -> u8;
}

impl Tr for u8 {
    fn id(&self) -> u8 {
        *self
    }
}

#[repr(C, align(16))]
struct Big16([u8; 16]);

impl Tr for Big16 {
    fn id(&self) -> u8 {
        self.0[0]
    }
}

#[repr(C)]
struct Packet<T: ?Sized> {
    header: u8,
    payload: T,
}

#[repr(C)]
struct Header6<T: ?Sized> {
    a: u32,
    b: u16,
    payload: T,
}

#[repr(C, packed(2))]
struct Packed2Slice {
    header: u8,
    payload: [u32],
}

fn measure_pkt<T: ?Sized>(p: &Packet<T>) -> (usize, usize) {
    (mem::size_of_val(p), mem::align_of_val(p))
}

fn measure_h6<T: ?Sized>(p: &Header6<T>) -> (usize, usize) {
    (mem::size_of_val(p), mem::align_of_val(p))
}

fn main() {
    let p_u32_3 = Packet {
        header: 1,
        payload: [10u32, 20, 30],
    };
    let p_u32_0 = Packet {
        header: 1,
        payload: [0u32; 0],
    };
    let p_u8_3 = Packet {
        header: 1,
        payload: [1u8, 2, 3],
    };
    let p_small = Packet {
        header: 1,
        payload: 9u8,
    };
    let p_big = Packet {
        header: 1,
        payload: Big16([7u8; 16]),
    };

    let u32_3 = measure_pkt::<[u32]>(&p_u32_3);
    let u32_0 = measure_pkt::<[u32]>(&p_u32_0);
    let u8_3 = measure_pkt::<[u8]>(&p_u8_3);
    let dyn_small = measure_pkt::<dyn Tr>(&p_small);
    let dyn_big = measure_pkt::<dyn Tr>(&p_big);

    let h6_u8_3 = Header6 {
        a: 1,
        b: 2,
        payload: [1u8, 2, 3],
    };
    let h6_big = Header6 {
        a: 1,
        b: 2,
        payload: Big16([3u8; 16]),
    };
    let h6_u8 = measure_h6::<[u8]>(&h6_u8_3);
    let h6_dyn_big = measure_h6::<dyn Tr>(&h6_big);

    // Build Packed2Slice by unsizing coercion via a concrete sized generic wrapper?
    // Non-generic packed DSTs cannot unsize from an array directly without raw ptr cast
    // unless coerced via unsized coercion from a same-field-type array-backed struct?
    // Wait: Rust does NOT allow unsizing Packed2Slice from an array struct directly, so test raw slice ptr:
    let raw_buf = [0u64; 4];
    let thin = raw_buf.as_ptr() as *const u32;
    let slice_ptr: *const [u32] = std::ptr::slice_from_raw_parts(thin, 3);
    let packed_ref: &Packed2Slice = unsafe { &*(slice_ptr as *const Packed2Slice) };
    let packed2_u32_3 = (mem::size_of_val(packed_ref), mem::align_of_val(packed_ref));

    println!(
        "U32_3=({},{}) U32_0=({},{}) U8_3=({},{}) DYN_SMALL=({},{}) DYN_BIG=({},{}) H6_U8_3=({},{}) H6_DYN_BIG=({},{}) PACKED2_U32_3=({},{})",
        u32_3.0, u32_3.1,
        u32_0.0, u32_0.1,
        u8_3.0, u8_3.1,
        dyn_small.0, dyn_small.1,
        dyn_big.0, dyn_big.1,
        h6_u8.0, h6_u8.1,
        h6_dyn_big.0, h6_dyn_big.1,
        packed2_u32_3.0, packed2_u32_3.1,
    );
}
"""


LLVM_CUSTOM_DST_IR_RS = r"""
#![crate_type = "lib"]

use std::mem;

pub trait Tr {
    fn id(&self) -> u8;
}

#[repr(C)]
pub struct Packet<T: ?Sized> {
    pub header: u8,
    pub payload: T,
}

#[repr(C)]
pub struct Header6<T: ?Sized> {
    pub a: u32,
    pub b: u16,
    pub payload: T,
}

#[repr(C, packed(2))]
pub struct Packed2Slice {
    pub header: u8,
    pub payload: [u32],
}

#[unsafe(no_mangle)]
pub extern "Rust" fn packet_dyn_size_align(p: &Packet<dyn Tr>) -> (usize, usize) {
    (mem::size_of_val(p), mem::align_of_val(p))
}

#[unsafe(no_mangle)]
pub extern "Rust" fn packet_slice_u32_size_align(p: &Packet<[u32]>) -> (usize, usize) {
    (mem::size_of_val(p), mem::align_of_val(p))
}

#[unsafe(no_mangle)]
pub extern "Rust" fn header6_dyn_size_align(p: &Header6<dyn Tr>) -> (usize, usize) {
    (mem::size_of_val(p), mem::align_of_val(p))
}

#[unsafe(no_mangle)]
pub extern "Rust" fn packed2_slice_u32_size_align(p: &Packed2Slice) -> (usize, usize) {
    (mem::size_of_val(p), mem::align_of_val(p))
}
"""


ZEROCOPY_PROBE_RS = r"""
use std::mem;
use std::num::NonZeroUsize;
use std::ptr::NonNull;
use zerocopy::{DstLayout, KnownLayout, PointerMetadata};

fn main() {
    let arr = [1u32, 2, 3];
    let zc_u32_3 = <[u32] as KnownLayout>::size_for_metadata(3);
    let mem_u32_3 = mem::size_of_val(&arr[..]);
    let zc_u8_3 = <[u8] as KnownLayout>::size_for_metadata(3);
    let zc_overflow = <[u32] as KnownLayout>::size_for_metadata(usize::MAX);
    let zc_u8_usize_max = <[u8] as KnownLayout>::size_for_metadata(usize::MAX);

    let valid_3 = <[u32] as KnownLayout>::is_valid_metadata(3);
    let valid_max = <[u32] as KnownLayout>::is_valid_metadata(usize::MAX);
    let valid_u8_isize_max = <[u8] as KnownLayout>::is_valid_metadata(isize::MAX as usize);
    let valid_u8_over_isize_max =
        <[u8] as KnownLayout>::is_valid_metadata((isize::MAX as usize) + 1);
    let valid_zst_usize_max = <[()] as KnownLayout>::is_valid_metadata(usize::MAX);
    let raw_sz = <[u32] as KnownLayout>::size_of_val_raw(NonNull::from(&arr[..]));

    // Custom DST layouts built directly via DstLayout::for_repr_c_struct:
    // 1. Packet<[u32]> = { header: u8, payload: [u32] }
    let pkt_u32_layout = DstLayout::for_repr_c_struct(
        None,
        None,
        &[DstLayout::for_type::<u8>(), <[u32] as KnownLayout>::LAYOUT],
    );
    let pkt_u32_3 = 3usize.size_for_metadata(pkt_u32_layout);
    let pkt_u32_0 = 0usize.size_for_metadata(pkt_u32_layout);
    let pkt_u32_max = usize::MAX.size_for_metadata(pkt_u32_layout);

    // 2. Packet<[u8]> = { header: u8, payload: [u8] }
    let pkt_u8_layout = DstLayout::for_repr_c_struct(
        None,
        None,
        &[DstLayout::for_type::<u8>(), <[u8] as KnownLayout>::LAYOUT],
    );
    let pkt_u8_3 = 3usize.size_for_metadata(pkt_u8_layout);

    // 3. Header6<[u8]> = { a: u32, b: u16, payload: [u8] }
    let h6_u8_layout = DstLayout::for_repr_c_struct(
        None,
        None,
        &[
            DstLayout::for_type::<u32>(),
            DstLayout::for_type::<u16>(),
            <[u8] as KnownLayout>::LAYOUT,
        ],
    );
    let h6_u8_3 = 3usize.size_for_metadata(h6_u8_layout);
    let h6_u8_0 = 0usize.size_for_metadata(h6_u8_layout);

    // 4. Packed2Slice = #[repr(C, packed(2))] { header: u8, payload: [u32] }
    let packed2_layout = DstLayout::for_repr_c_struct(
        None,
        NonZeroUsize::new(2),
        &[DstLayout::for_type::<u8>(), <[u32] as KnownLayout>::LAYOUT],
    );
    let packed2_u32_3 = 3usize.size_for_metadata(packed2_layout);

    println!(
        "ZC_U32_3={:?} MEM_U32_3={} ZC_U8_3={:?} ZC_OVERFLOW={:?} ZC_U8_USIZE_MAX={:?} VALID_3={} VALID_MAX={} VALID_U8_IMAX={} VALID_U8_OVER={} VALID_ZST_MAX={} RAW_SZ={:?} PKT_U32_3={:?} PKT_U32_0={:?} PKT_U32_MAX={:?} PKT_U8_3={:?} H6_U8_3={:?} H6_U8_0={:?} PACKED2_U32_3={:?}",
        zc_u32_3,
        mem_u32_3,
        zc_u8_3,
        zc_overflow,
        zc_u8_usize_max,
        valid_3,
        valid_max,
        valid_u8_isize_max,
        valid_u8_over_isize_max,
        valid_zst_usize_max,
        raw_sz,
        pkt_u32_3,
        pkt_u32_0,
        pkt_u32_max,
        pkt_u8_3,
        h6_u8_3,
        h6_u8_0,
        packed2_u32_3,
    );
}
"""


def sanitize_text(text: str, extra_paths: list[str] | None = None) -> str:
    home = os.path.expanduser("~")
    if home:
        text = text.replace(home, "<home>")
    for p in extra_paths or []:
        if p:
            text = text.replace(p, "<tmp>")
    text = re.sub(r"/tmp/tmp[A-Za-z0-9_]+", "<tmp>", text)
    return text


def run_cmd(cmd: list[str], cwd: Path | None = None, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    merged_env = os.environ.copy()
    cargo_bin = os.path.expanduser("~/.cargo/bin")
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
        check=False,
    )


def extract_llvm_functions(ll_text: str, names: list[str]) -> dict[str, list[str]]:
    found: dict[str, list[str]] = {}
    lines = ll_text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("define ") and any(f"@{name}(" in line for name in names):
            block = [line]
            i += 1
            while i < len(lines):
                block.append(lines[i])
                if lines[i].strip() == "}":
                    break
                i += 1
            found[line] = block
        i += 1
    return found


def resolve_zerocopy_dir(explicit: str | None) -> Path | None:
    candidates: list[Path] = []
    if explicit:
        candidates.append(Path(explicit))
    env_dir = os.environ.get("ZEROCOPY_DIR")
    if env_dir:
        candidates.append(Path(env_dir))
    cwd = Path.cwd()
    candidates.extend([cwd, cwd.parent, cwd.parent.parent])
    for cand in candidates:
        if (cand / "zerocopy" / "Cargo.toml").is_file() and (cand / "zerocopy" / "src" / "lib.rs").is_file():
            return cand
        if (cand / "Cargo.toml").is_file() and (cand / "src" / "layout.rs").is_file() and (cand / "src" / "lib.rs").is_file():
            return cand.parent
    return None


def parse_kv_tokens(stdout: str) -> dict[str, str]:
    parsed: dict[str, str] = {}
    for tok in stdout.strip().split():
        if "=" in tok:
            k, v = tok.split("=", 1)
            parsed[k] = v
    return parsed


def run_probe(zerocopy_dir: Path | None) -> dict[str, Any]:
    rustc_v = run_cmd(["rustc", "-vV"])
    miri_v = run_cmd(["cargo", "+nightly", "miri", "--version"])
    uname_m = run_cmd(["uname", "-m"])

    results: dict[str, Any] = {
        "probe_id": "wide-ptr-dst-size-of-val-and-known-layout",
        "rustc_version": rustc_v.stdout.strip(),
        "miri_version": miri_v.stdout.strip(),
        "host_arch": uname_m.stdout.strip(),
        "experiments": {},
    }

    with tempfile.TemporaryDirectory() as tmpdir_str:
        tmp = Path(tmpdir_str)
        redact = [tmpdir_str]

        # ------------------------------------------------------------------
        # A.1 Native execution: wide pointer ptr::eq vs ptr::addr_eq
        # ------------------------------------------------------------------
        wide_rs = tmp / "wide_ptr_probe.rs"
        wide_bin = tmp / "wide_ptr_probe"
        wide_rs.write_text(WIDE_PTR_PROBE_RS, encoding="utf-8")
        c_wide = run_cmd(["rustc", "--edition", "2024", str(wide_rs), "-o", str(wide_bin)])
        r_wide = run_cmd([str(wide_bin)]) if c_wide.returncode == 0 else None

        # ------------------------------------------------------------------
        # A.2 Miri execution + seed sweep (default + 16 explicit seeds)
        # ------------------------------------------------------------------
        miri_a_dir = tmp / "miri_wide_ptr"
        (miri_a_dir / "src").mkdir(parents=True)
        (miri_a_dir / "Cargo.toml").write_text(
            '[package]\nname = "miri_wide_ptr"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        (miri_a_dir / "src" / "main.rs").write_text(WIDE_PTR_PROBE_RS, encoding="utf-8")
        miri_a_default = run_cmd(["cargo", "+nightly", "miri", "run", "--offline"], cwd=miri_a_dir)

        seed_same_vtable_true = 0
        seed_same_vtable_false = 0
        seed_samples: list[dict[str, Any]] = []
        for seed in range(16):
            r_seed = run_cmd(
                ["cargo", "+nightly", "miri", "run", "--offline"],
                cwd=miri_a_dir,
                env={"MIRIFLAGS": f"-Zmiri-seed={seed}"},
            )
            kv = parse_kv_tokens(r_seed.stdout)
            same_vt = kv.get("DYN_EQ_SAME_VTABLE")
            if same_vt == "true":
                seed_same_vtable_true += 1
            elif same_vt == "false":
                seed_same_vtable_false += 1
            seed_samples.append(
                {
                    "seed": seed,
                    "dyn_eq_same_vtable": same_vt,
                    "dyn_addr_eq": kv.get("DYN_ADDR_EQ"),
                    "dyn_eq_copied": kv.get("DYN_EQ_COPIED"),
                }
            )

        # ------------------------------------------------------------------
        # A.3 LLVM IR: wide pointer eq / ne / addr_eq
        # ------------------------------------------------------------------
        wide_ir_rs = tmp / "wide_ptr_ir.rs"
        wide_ir_ll = tmp / "wide_ptr_ir.ll"
        wide_ir_rs.write_text(LLVM_WIDE_PTR_IR_RS, encoding="utf-8")
        c_wide_ir = run_cmd(
            ["rustc", "--edition", "2024", "-Copt-level=2", "--emit=llvm-ir", str(wide_ir_rs), "-o", str(wide_ir_ll)]
        )
        wide_ir_funcs = (
            extract_llvm_functions(
                wide_ir_ll.read_text(encoding="utf-8"),
                [
                    "cmp_dyn_ptr_eq",
                    "cmp_dyn_ptr_ne",
                    "cmp_dyn_addr_eq",
                    "cmp_slice_ptr_eq",
                    "cmp_slice_addr_eq",
                ],
            )
            if c_wide_ir.returncode == 0
            else {}
        )

        results["experiments"]["a_wide_ptr_eq_vs_addr_eq"] = {
            "slice_and_dyn_eq_vs_addr_eq_exec": {
                "edition": "2024",
                "compile_returncode": c_wide.returncode,
                "compile_stderr": sanitize_text(c_wide.stderr, redact),
                "run_returncode": r_wide.returncode if r_wide else None,
                "run_stdout": r_wide.stdout.strip() if r_wide else "",
                "parsed": parse_kv_tokens(r_wide.stdout) if r_wide else {},
            },
            "slice_and_dyn_eq_vs_addr_eq_miri": {
                "edition": "2024",
                "command": "cargo +nightly miri run --offline",
                "returncode": miri_a_default.returncode,
                "stdout": miri_a_default.stdout.strip(),
                "stderr": sanitize_text(miri_a_default.stderr, redact),
                "parsed": parse_kv_tokens(miri_a_default.stdout),
                "miri_seed_sweep_0_to_15": {
                    "seed_count": 16,
                    "dyn_eq_same_vtable_true_count": seed_same_vtable_true,
                    "dyn_eq_same_vtable_false_count": seed_same_vtable_false,
                    "samples": seed_samples,
                },
            },
            "wide_ptr_eq_vs_addr_eq_llvm_ir": {
                "edition": "2024",
                "extra_args": ["-Copt-level=2", "--emit=llvm-ir"],
                "compile_returncode": c_wide_ir.returncode,
                "compile_stderr": sanitize_text(c_wide_ir.stderr, redact),
                "llvm_ir_functions": wide_ir_funcs,
            },
        }

        # ------------------------------------------------------------------
        # B.1 Custom DST dynamic size_of_val / align_of_val (native + Miri)
        # ------------------------------------------------------------------
        dst_rs = tmp / "custom_dst_probe.rs"
        dst_bin = tmp / "custom_dst_probe"
        dst_rs.write_text(CUSTOM_DST_PROBE_RS, encoding="utf-8")
        c_dst = run_cmd(["rustc", "--edition", "2024", str(dst_rs), "-o", str(dst_bin)])
        r_dst = run_cmd([str(dst_bin)]) if c_dst.returncode == 0 else None

        miri_b_dir = tmp / "miri_custom_dst"
        (miri_b_dir / "src").mkdir(parents=True)
        (miri_b_dir / "Cargo.toml").write_text(
            '[package]\nname = "miri_custom_dst"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        (miri_b_dir / "src" / "main.rs").write_text(CUSTOM_DST_PROBE_RS, encoding="utf-8")
        miri_b = run_cmd(["cargo", "+nightly", "miri", "run", "--offline"], cwd=miri_b_dir)

        # ------------------------------------------------------------------
        # B.2 Custom DST LLVM IR
        # ------------------------------------------------------------------
        dst_ir_rs = tmp / "custom_dst_ir.rs"
        dst_ir_ll = tmp / "custom_dst_ir.ll"
        dst_ir_rs.write_text(LLVM_CUSTOM_DST_IR_RS, encoding="utf-8")
        c_dst_ir = run_cmd(
            ["rustc", "--edition", "2024", "-Copt-level=2", "--emit=llvm-ir", str(dst_ir_rs), "-o", str(dst_ir_ll)]
        )
        dst_ir_funcs = (
            extract_llvm_functions(
                dst_ir_ll.read_text(encoding="utf-8"),
                [
                    "packet_dyn_size_align",
                    "packet_slice_u32_size_align",
                    "header6_dyn_size_align",
                    "packed2_slice_u32_size_align",
                ],
            )
            if c_dst_ir.returncode == 0
            else {}
        )

        # ------------------------------------------------------------------
        # B.3 Real zerocopy::KnownLayout & DstLayout compiled probe
        # ------------------------------------------------------------------
        zc_section: dict[str, Any]
        if zerocopy_dir is None:
            zc_section = {
                "status": "skipped_no_zerocopy_checkout",
                "note": "Pass --zerocopy-dir <path> or set ZEROCOPY_DIR to compile and run the real zerocopy crate probe.",
            }
        else:
            zc_cargo = (zerocopy_dir / "zerocopy" / "Cargo.toml").read_text(encoding="utf-8")
            m_ver = re.search(r'^version\s*=\s*"([^"]+)"', zc_cargo, re.MULTILINE)
            zc_ver = m_ver.group(1) if m_ver else "0.8.64"
            git_head = run_cmd(["git", "-C", str(zerocopy_dir), "rev-parse", "HEAD"])
            zc_rlib = tmp / "libzerocopy.rlib"
            zc_lib_rs = zerocopy_dir / "zerocopy" / "src" / "lib.rs"
            c_zc_lib = run_cmd(
                [
                    "rustc",
                    "--edition",
                    "2021",
                    "--crate-type",
                    "rlib",
                    "--crate-name",
                    "zerocopy",
                    str(zc_lib_rs),
                    "-o",
                    str(zc_rlib),
                ],
                env={"CARGO_PKG_VERSION": zc_ver},
            )
            zc_probe_rs = tmp / "zc_probe.rs"
            zc_probe_bin = tmp / "zc_probe"
            zc_probe_rs.write_text(ZEROCOPY_PROBE_RS, encoding="utf-8")
            c_zc_probe = (
                run_cmd(
                    [
                        "rustc",
                        "--edition",
                        "2024",
                        "--extern",
                        f"zerocopy={zc_rlib}",
                        str(zc_probe_rs),
                        "-o",
                        str(zc_probe_bin),
                    ]
                )
                if c_zc_lib.returncode == 0
                else None
            )
            r_zc_probe = run_cmd([str(zc_probe_bin)]) if (c_zc_probe and c_zc_probe.returncode == 0) else None
            zc_section = {
                "zerocopy_version": zc_ver,
                "zerocopy_checkout_revision": git_head.stdout.strip() if git_head.returncode == 0 else None,
                "edition_zerocopy": "2021",
                "edition_probe": "2024",
                "lib_compile_returncode": c_zc_lib.returncode,
                "lib_compile_stderr": sanitize_text(c_zc_lib.stderr, redact + [str(zerocopy_dir)]),
                "probe_compile_returncode": c_zc_probe.returncode if c_zc_probe else None,
                "probe_compile_stderr": sanitize_text(c_zc_probe.stderr, redact) if c_zc_probe else "",
                "run_returncode": r_zc_probe.returncode if r_zc_probe else None,
                "run_stdout": r_zc_probe.stdout.strip() if r_zc_probe else "",
                "parsed": parse_kv_tokens(r_zc_probe.stdout) if r_zc_probe else {},
            }

        results["experiments"]["b_custom_dst_size_of_val_and_zerocopy"] = {
            "custom_dst_dynamic_sizing_exec": {
                "edition": "2024",
                "compile_returncode": c_dst.returncode,
                "compile_stderr": sanitize_text(c_dst.stderr, redact),
                "run_returncode": r_dst.returncode if r_dst else None,
                "run_stdout": r_dst.stdout.strip() if r_dst else "",
                "parsed": parse_kv_tokens(r_dst.stdout) if r_dst else {},
            },
            "custom_dst_dynamic_sizing_miri": {
                "edition": "2024",
                "command": "cargo +nightly miri run --offline",
                "returncode": miri_b.returncode,
                "stdout": miri_b.stdout.strip(),
                "stderr": sanitize_text(miri_b.stderr, redact),
                "parsed": parse_kv_tokens(miri_b.stdout),
            },
            "custom_dst_dynamic_sizing_llvm_ir": {
                "edition": "2024",
                "extra_args": ["-Copt-level=2", "--emit=llvm-ir"],
                "compile_returncode": c_dst_ir.returncode,
                "compile_stderr": sanitize_text(c_dst_ir.stderr, redact),
                "llvm_ir_functions": dst_ir_funcs,
            },
            "real_zerocopy_known_layout_probe": zc_section,
        }

    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--zerocopy-dir",
        help="Path to a google/zerocopy checkout for compiling the real zerocopy crate.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).resolve().with_name("probe_results.json"),
        help="Output JSON path (default: support/probe_results.json).",
    )
    args = parser.parse_args()

    zc_dir = resolve_zerocopy_dir(args.zerocopy_dir)
    results = run_probe(zc_dir)
    args.out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")

    # Sanity assertions on empirical results.
    exp_a = results["experiments"]["a_wide_ptr_eq_vs_addr_eq"]
    p_exec_a = exp_a["slice_and_dyn_eq_vs_addr_eq_exec"]["parsed"]
    p_miri_a = exp_a["slice_and_dyn_eq_vs_addr_eq_miri"]["parsed"]
    assert p_exec_a["SLICE_ADDR_EQ"] == "true"
    assert p_exec_a["SLICE_EQ_DIFF"] == "false"
    assert p_exec_a["SLICE_EQ_SAME"] == "true"
    assert p_exec_a["DYN_ADDR_EQ"] == "true"
    assert p_exec_a["DYN_EQ_DIFF_VTABLE"] == "false"
    assert p_exec_a["DYN_EQ_SAME_VTABLE"] == "true"
    assert p_miri_a["DYN_ADDR_EQ"] == "true"
    assert p_miri_a["DYN_EQ_COPIED"] == "true"

    exp_b = results["experiments"]["b_custom_dst_size_of_val_and_zerocopy"]
    p_exec_b = exp_b["custom_dst_dynamic_sizing_exec"]["parsed"]
    p_miri_b = exp_b["custom_dst_dynamic_sizing_miri"]["parsed"]
    assert p_exec_b == p_miri_b
    assert p_exec_b["U32_3"] == "(16,4)"
    assert p_exec_b["U32_0"] == "(4,4)"
    assert p_exec_b["U8_3"] == "(4,1)"
    assert p_exec_b["DYN_SMALL"] == "(2,1)"
    assert p_exec_b["DYN_BIG"] == "(32,16)"
    assert p_exec_b["H6_U8_3"] == "(12,4)"
    assert p_exec_b["H6_DYN_BIG"] == "(32,16)"
    assert p_exec_b["PACKED2_U32_3"] == "(14,2)"

    zc = exp_b["real_zerocopy_known_layout_probe"]
    if "parsed" in zc:
        p_zc = zc["parsed"]
        assert p_zc["ZC_U32_3"] == "Some(12)"
        assert p_zc["MEM_U32_3"] == "12"
        assert p_zc["ZC_U8_3"] == "Some(3)"
        assert p_zc["ZC_OVERFLOW"] == "None"
        assert p_zc["VALID_3"] == "true"
        assert p_zc["VALID_MAX"] == "false"
        assert p_zc["RAW_SZ"] == "Some(12)"
        assert p_zc["PKT_U32_3"] == "Some(16)"
        assert p_zc["PKT_U32_0"] == "Some(4)"
        assert p_zc["PKT_U32_MAX"] == "None"

    print(f"Wrote verified empirical results to {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
