#!/usr/bin/env python3
"""Self-contained rustc, LLVM IR/asm, and Miri empirical probe for core::intrinsics::simd
and the MCP#838 MIR validator ICE.

Executes four empirical parts against the installed nightly rustc + miri toolchain:
  Part A: Valid simd_masked_load (partial allocation, null Vector, 1usize Unaligned),
          simd_as saturation, simd_bitmask (LE x86_64 vs BE s390x), simd_select_bitmask
          roundtrip, and s390x vs x86_64 SimdAlign::Vector alignment split.
  Part B: Miri UB sharpness matrix (Stacked Borrows & Tree Borrows) vs native x86_64
          execution (misaligned all-zero mask, +1 non-{0,-1} mask MSB vs LSB divergence,
          simd_cast OOB/NaN float->u8 UB, active OOB lane UB).
  Part C: Cross-target #![no_core] LLVM IR (-C opt-level=0 and -O) and asm for
          x86_64-unknown-linux-gnu (LE) vs s390x-unknown-linux-gnu (BE).
  Part D: Live #![forbid(unsafe_code)] MCP#838 MIR Validator ICE (rc = 101) across
          --crate-type=lib, --emit=metadata, and -Zmir-opt-level=0.

Writes deterministic JSON results to --out (default: support/probe_results.json next to
this script, or stdout if --out -).
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


def _find_tool(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    candidate = Path.home() / ".cargo" / "bin" / name
    if candidate.is_file():
        return str(candidate)
    raise RuntimeError(f"required tool not found on PATH or ~/.cargo/bin: {name}")


def _run(
    cmd: list[str],
    *,
    env: dict[str, str] | None = None,
    cwd: Path | None = None,
    timeout: int = 60,
) -> dict[str, Any]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    return {
        "rc": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def _scrub(text: str, tmpdir: Path) -> str:
    return text.replace(str(tmpdir), "<TMP>")


NOCORE_PRELUDE = """\
#![allow(internal_features, dead_code, unused, integer_to_ptr_transmutes)]
#![feature(no_core, lang_items, repr_simd, intrinsics, adt_const_params, auto_traits, rustc_attrs)]
#![no_core]
#![no_main]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
#[lang = "freeze"]
pub unsafe auto trait Freeze {}
#[lang = "legacy_receiver"]
pub trait LegacyReceiver {}
impl<T: ?Sized> LegacyReceiver for &T {}
#[lang = "structural_peq"]
pub trait StructuralPartialEq {}
#[lang = "eq"]
pub trait PartialEq<Rhs: ?Sized = Self> {
    fn eq(&self, other: &Rhs) -> bool;
}
#[lang = "const_param_ty"]
pub trait ConstParamTy_ {}

impl Copy for i8 {}
impl Copy for i32 {}
impl Copy for u8 {}
impl Copy for u32 {}
impl Copy for f32 {}
impl Copy for usize {}
impl Copy for isize {}
impl<T: ?Sized> Copy for *const T {}
impl<T: ?Sized> Copy for *mut T {}
impl Copy for [i32; 4] {}
impl Copy for [u32; 4] {}
impl Copy for [u32; 2] {}
impl Copy for [i32; 8] {}
impl Copy for [u32; 8] {}
impl Copy for [f32; 4] {}
impl Copy for [u8; 4] {}

#[repr(simd)]
pub struct I32x4([i32; 4]);
impl Copy for I32x4 {}
#[repr(simd)]
pub struct U32x4([u32; 4]);
impl Copy for U32x4 {}
#[repr(simd)]
pub struct U32x8([u32; 8]);
impl Copy for U32x8 {}
#[repr(simd)]
pub struct I32x8([i32; 8]);
impl Copy for I32x8 {}
#[repr(simd)]
pub struct F32x4([f32; 4]);
impl Copy for F32x4 {}
#[repr(simd)]
pub struct U8x4([u8; 4]);
impl Copy for U8x4 {}

#[repr(u8)]
pub enum SimdAlign {
    Unaligned = 0,
    Element = 1,
    Vector = 2,
}
impl Copy for SimdAlign {}
impl StructuralPartialEq for SimdAlign {}
impl PartialEq for SimdAlign {
    fn eq(&self, _other: &Self) -> bool { true }
}
impl ConstParamTy_ for SimdAlign {}

#[rustc_intrinsic]
unsafe fn simd_masked_load<V, U, T, const ALIGN: SimdAlign>(mask: V, ptr: U, val: T) -> T;
#[rustc_intrinsic]
unsafe fn simd_as<T, U>(x: T) -> U;
#[rustc_intrinsic]
unsafe fn simd_cast<T, U>(x: T) -> U;
#[rustc_intrinsic]
unsafe fn simd_bitmask<T, U>(x: T) -> U;
#[rustc_intrinsic]
unsafe fn simd_select_bitmask<M, T>(m: M, yes: T, no: T) -> T;
#[rustc_intrinsic]
unsafe fn transmute<Src, Dst>(src: Src) -> Dst;

#[inline(always)]
fn without_provenance_u32(addr: usize) -> *const u32 {
    unsafe { transmute(addr) }
}
"""


PART_A_STD_SRC = """\
#![feature(repr_simd, core_intrinsics)]
use core::intrinsics::simd::{SimdAlign, simd_as, simd_bitmask, simd_masked_load, simd_select_bitmask};

#[repr(simd)]
#[derive(Copy, Clone)]
struct I32x4([i32; 4]);
#[repr(simd)]
#[derive(Copy, Clone)]
struct U32x4([u32; 4]);
#[repr(simd)]
#[derive(Copy, Clone)]
struct I32x8([i32; 8]);
#[repr(simd)]
#[derive(Copy, Clone)]
struct U32x8([u32; 8]);
#[repr(simd)]
#[derive(Copy, Clone)]
struct F32x4([f32; 4]);
#[repr(simd)]
#[derive(Copy, Clone)]
struct U8x4([u8; 4]);

fn main() {
    let short: [u32; 2] = [10, 20];
    let partial = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Element }>(
            I32x4([-1, -1, 0, 0]),
            short.as_ptr(),
            U32x4([99; 4]),
        )
    };
    let null_masked = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Vector }>(
            I32x4([0; 4]),
            core::ptr::null(),
            U32x4([77; 4]),
        )
    };
    let unalign1_masked = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Unaligned }>(
            I32x4([0; 4]),
            core::ptr::without_provenance(1),
            U32x4([55; 4]),
        )
    };
    let sat: U8x4 = unsafe { simd_as(F32x4([-5.0, 300.0, f32::NAN, 42.9])) };
    let bm: u8 = unsafe { simd_bitmask(I32x8([-1, 0, -1, 0, 0, 0, 0, 0])) };
    let roundtrip: U32x8 = unsafe {
        simd_select_bitmask(
            bm,
            U32x8([100, 101, 102, 103, 104, 105, 106, 107]),
            U32x8([200, 201, 202, 203, 204, 205, 206, 207]),
        )
    };
    let p_arr: [u32; 4] = unsafe { core::mem::transmute(partial) };
    let n_arr: [u32; 4] = unsafe { core::mem::transmute(null_masked) };
    let u_arr: [u32; 4] = unsafe { core::mem::transmute(unalign1_masked) };
    let s_arr: [u8; 4] = unsafe { core::mem::transmute(sat) };
    let r_arr: [u32; 8] = unsafe { core::mem::transmute(roundtrip) };
    println!(
        "PARTIAL={p_arr:?} NULL_MASKED={n_arr:?} UNALIGN1_MASKED={u_arr:?} SAT={s_arr:?} BITMASK=0x{bm:02x} ROUNDTRIP={r_arr:?}"
    );
}
"""


PART_A_NOCORE_MIRI_BODY = """\
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let all_ones_i32: i32 = 0xffff_ffff_u32 as i32;
    let all_ones_u32: u32 = 0xffff_ffff_u32;

    // 1. Partial-allocation [u32; 2] masked load with SimdAlign::Element
    let short: [u32; 2] = [10, 20];
    let p_short: *const u32 = &short as *const [u32; 2] as *const u32;
    let partial: U32x4 = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Element }>(
            I32x4([all_ones_i32, all_ones_i32, 0, 0]),
            p_short,
            U32x4([99, 99, 99, 99]),
        )
    };
    let [p0, p1, p2, p3]: [u32; 4] = unsafe { transmute(partial) };
    match (p0, p1, p2, p3) {
        (10, 20, 99, 99) => {}
        _ => return 11,
    }

    // 2. Null pointer with all-zero mask and SimdAlign::Vector
    let null_masked: U32x4 = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Vector }>(
            I32x4([0, 0, 0, 0]),
            without_provenance_u32(0),
            U32x4([77, 77, 77, 77]),
        )
    };
    let [n0, n1, n2, n3]: [u32; 4] = unsafe { transmute(null_masked) };
    match (n0, n1, n2, n3) {
        (77, 77, 77, 77) => {}
        _ => return 12,
    }

    // 3. 1usize pointer with all-zero mask and SimdAlign::Unaligned
    let unalign1: U32x4 = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Unaligned }>(
            I32x4([0, 0, 0, 0]),
            without_provenance_u32(1),
            U32x4([55, 55, 55, 55]),
        )
    };
    let [u0, u1, u2, u3]: [u32; 4] = unsafe { transmute(unalign1) };
    match (u0, u1, u2, u3) {
        (55, 55, 55, 55) => {}
        _ => return 13,
    }

    // 4. simd_as saturating f32 -> u8 (including -5.0, 300.0, qNaN, 42.9)
    let neg5_f32: f32 = unsafe { transmute(0xc0a0_0000_u32) };
    let nan_f32: f32 = unsafe { transmute(0x7fc0_0000_u32) };
    let sat: U8x4 = unsafe { simd_as(F32x4([neg5_f32, 300.0_f32, nan_f32, 42.9_f32])) };
    let [s0, s1, s2, s3]: [u8; 4] = unsafe { transmute(sat) };
    match (s0, s1, s2, s3) {
        (0, 255, 0, 42) => {}
        _ => return 14,
    }

    // 5. simd_bitmask + simd_select_bitmask roundtrip (works identically across LE and BE!)
    let m8 = U32x8([all_ones_u32, 0, all_ones_u32, 0, 0, 0, 0, 0]);
    let bm: u8 = unsafe { simd_bitmask(m8) };
    let rt: U32x8 = unsafe {
        simd_select_bitmask(
            bm,
            U32x8([100, 101, 102, 103, 104, 105, 106, 107]),
            U32x8([200, 201, 202, 203, 204, 205, 206, 207]),
        )
    };
    let [r0, r1, r2, r3, r4, r5, r6, r7]: [u32; 8] = unsafe { transmute(rt) };
    match (r0, r1, r2, r3, r4, r5, r6, r7) {
        (100, 201, 102, 203, 204, 205, 206, 207) => {}
        _ => return 15,
    }

    // Return the observed bitmask byte directly (0x05=5 on LE x86_64, 0xA0=160 on BE s390x).
    bm as isize
}
"""


PART_B_CASES: dict[str, dict[str, str]] = {
    "all_masked_misaligned_element_align4_ub": {
        "nocore_body": """\
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let v: U32x4 = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Element }>(
            I32x4([0, 0, 0, 0]),
            without_provenance_u32(1),
            U32x4([0, 0, 0, 0]),
        )
    };
    let [a0, _, _, _]: [u32; 4] = unsafe { transmute(v) };
    a0 as isize
}
""",
        "std_src": """\
#![feature(repr_simd, core_intrinsics)]
use core::intrinsics::simd::{SimdAlign, simd_masked_load};
#[repr(simd)] #[derive(Copy, Clone)] struct I32x4([i32; 4]);
#[repr(simd)] #[derive(Copy, Clone)] struct U32x4([u32; 4]);
fn main() {
    let v = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Element }>(
            I32x4([0; 4]),
            core::ptr::without_provenance(1),
            U32x4([0; 4]),
        )
    };
    let arr: [u32; 4] = unsafe { core::mem::transmute(v) };
    println!("{arr:?}");
}
""",
    },
    "all_masked_align8_vector_align_target_split": {
        "nocore_body": """\
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let v: U32x4 = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Vector }>(
            I32x4([0, 0, 0, 0]),
            without_provenance_u32(8),
            U32x4([33, 33, 33, 33]),
        )
    };
    let [a0, _, _, _]: [u32; 4] = unsafe { transmute(v) };
    match a0 {
        33 => 0,
        _ => 9,
    }
}
""",
        "std_src": """\
#![feature(repr_simd, core_intrinsics)]
use core::intrinsics::simd::{SimdAlign, simd_masked_load};
#[repr(simd)] #[derive(Copy, Clone)] struct I32x4([i32; 4]);
#[repr(simd)] #[derive(Copy, Clone)] struct U32x4([u32; 4]);
fn main() {
    let v = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Vector }>(
            I32x4([0; 4]),
            core::ptr::without_provenance(8),
            U32x4([33; 4]),
        )
    };
    let arr: [u32; 4] = unsafe { core::mem::transmute(v) };
    println!("ALIGN_OF_U32X4={} VAL={arr:?}", core::mem::align_of::<U32x4>());
}
""",
    },
    "non_all_ones_plus1_mask_masked_load_ub": {
        "nocore_body": """\
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let buf: [u32; 4] = [10, 20, 30, 40];
    let p: *const u32 = &buf as *const [u32; 4] as *const u32;
    let v: U32x4 = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Element }>(
            I32x4([1, 0, 0, 0]),
            p,
            U32x4([99, 99, 99, 99]),
        )
    };
    let [a0, _, _, _]: [u32; 4] = unsafe { transmute(v) };
    a0 as isize
}
""",
        "std_src": """\
#![feature(repr_simd, core_intrinsics)]
use core::intrinsics::simd::{SimdAlign, simd_masked_load};
#[repr(simd)] #[derive(Copy, Clone)] struct I32x4([i32; 4]);
#[repr(simd)] #[derive(Copy, Clone)] struct U32x4([u32; 4]);
fn main() {
    let buf: [u32; 4] = [10, 20, 30, 40];
    let v = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Element }>(
            core::hint::black_box(I32x4([1, 0, 0, 0])),
            buf.as_ptr(),
            U32x4([99; 4]),
        )
    };
    let arr: [u32; 4] = unsafe { core::mem::transmute(v) };
    println!("NATIVE_PLUS1_MASK={arr:?}");
}
""",
    },
    "non_all_ones_plus1_mask_bitmask_ub_and_lsb_contrast": {
        "nocore_body": """\
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let all_ones: i32 = 0xffff_ffff_u32 as i32;
    let bm: u8 = unsafe { simd_bitmask(I32x8([1, 0, all_ones, 0, 0, 0, 0, 0])) };
    bm as isize
}
""",
        "std_src": """\
#![feature(repr_simd, core_intrinsics)]
use core::intrinsics::simd::{simd_and, simd_bitmask, simd_cast};
#[repr(simd)] #[derive(Copy, Clone)] struct I32x8([i32; 8]);
#[repr(simd)] #[derive(Copy, Clone)] struct I8x8([i8; 8]);
fn main() {
    let raw = core::hint::black_box(I32x8([1, 0, -1, 0, 0, 0, 0, 0]));
    // LLVM vector_mask_to_bitmask extracts MSB (lshr 31 + trunc -> icmp slt 0): +1 -> 0, -1 -> 1 => 0x04
    let llvm_bitmask: u8 = unsafe { simd_bitmask(raw) };
    // core::simd::Mask::to_array extracts LSB (simd_cast::<_, i8> & 1): +1 -> 1, -1 -> 1 => [1,0,1,0,0,0,0,0]
    let lsb_bytes: I8x8 = unsafe {
        let casted: I8x8 = simd_cast(raw);
        simd_and(casted, I8x8([1; 8]))
    };
    let lsb_arr: [u8; 8] = unsafe { core::mem::transmute(lsb_bytes) };
    println!("LLVM_BITMASK_MSB=0x{llvm_bitmask:02x} MASK_TO_ARRAY_LSB={lsb_arr:?}");
}
""",
    },
    "simd_cast_oob_float_to_u8_ub": {
        "nocore_body": """\
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let v: U8x4 = unsafe { simd_cast(F32x4([300.0_f32, 1.0_f32, 2.0_f32, 3.0_f32])) };
    let [a0, _, _, _]: [u8; 4] = unsafe { transmute(v) };
    a0 as isize
}
""",
        "std_src": """\
#![feature(repr_simd, core_intrinsics)]
use core::intrinsics::simd::simd_cast;
#[repr(simd)] #[derive(Copy, Clone)] struct F32x4([f32; 4]);
#[repr(simd)] #[derive(Copy, Clone)] struct U8x4([u8; 4]);
fn main() {
    let v: U8x4 = unsafe { simd_cast(core::hint::black_box(F32x4([300.0, 1.0, 2.0, 3.0]))) };
    let arr: [u8; 4] = unsafe { core::mem::transmute(v) };
    println!("{arr:?}");
}
""",
    },
    "simd_cast_nan_float_to_u8_ub": {
        "nocore_body": """\
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let nan_f32: f32 = unsafe { transmute(0x7fc0_0000_u32) };
    let v: U8x4 = unsafe { simd_cast(F32x4([nan_f32, 1.0_f32, 2.0_f32, 3.0_f32])) };
    let [a0, _, _, _]: [u8; 4] = unsafe { transmute(v) };
    a0 as isize
}
""",
        "std_src": """\
#![feature(repr_simd, core_intrinsics)]
use core::intrinsics::simd::simd_cast;
#[repr(simd)] #[derive(Copy, Clone)] struct F32x4([f32; 4]);
#[repr(simd)] #[derive(Copy, Clone)] struct U8x4([u8; 4]);
fn main() {
    let v: U8x4 = unsafe { simd_cast(core::hint::black_box(F32x4([f32::NAN, 1.0, 2.0, 3.0]))) };
    let arr: [u8; 4] = unsafe { core::mem::transmute(v) };
    println!("{arr:?}");
}
""",
    },
    "unmasked_oob_lane2_on_len2_slice_ub": {
        "nocore_body": """\
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let all_ones: i32 = 0xffff_ffff_u32 as i32;
    let short: [u32; 2] = [10, 20];
    let p: *const u32 = &short as *const [u32; 2] as *const u32;
    let v: U32x4 = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Element }>(
            I32x4([all_ones, all_ones, all_ones, 0]),
            p,
            U32x4([0, 0, 0, 0]),
        )
    };
    let [a0, _, _, _]: [u32; 4] = unsafe { transmute(v) };
    a0 as isize
}
""",
        "std_src": """\
#![feature(repr_simd, core_intrinsics)]
use core::intrinsics::simd::{SimdAlign, simd_masked_load};
#[repr(simd)] #[derive(Copy, Clone)] struct I32x4([i32; 4]);
#[repr(simd)] #[derive(Copy, Clone)] struct U32x4([u32; 4]);
fn main() {
    let short: [u32; 2] = [10, 20];
    let v = unsafe {
        simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Element }>(
            core::hint::black_box(I32x4([-1, -1, -1, 0])),
            short.as_ptr(),
            U32x4([0; 4]),
        )
    };
    let arr: [u32; 4] = unsafe { core::mem::transmute(v) };
    println!("OOB_LANE0_1=[{}, {}]", arr[0], arr[1]);
}
""",
    },
}


PART_C_IR_SRC = """\
#![feature(no_core, lang_items, repr_simd, intrinsics, adt_const_params, auto_traits)]
#![no_core]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
#[lang = "freeze"]
pub unsafe auto trait Freeze {}
#[lang = "legacy_receiver"]
pub trait LegacyReceiver {}
impl<T: ?Sized> LegacyReceiver for &T {}
#[lang = "structural_peq"]
pub trait StructuralPartialEq {}
#[lang = "eq"]
pub trait PartialEq<Rhs: ?Sized = Self> {
    fn eq(&self, other: &Rhs) -> bool;
}
#[lang = "const_param_ty"]
pub trait ConstParamTy_ {}

impl Copy for i32 {}
impl Copy for f32 {}
impl Copy for u8 {}
impl Copy for u32 {}
impl<T: ?Sized> Copy for *const T {}

#[repr(simd)]
pub struct I32x8([i32; 8]);
#[repr(simd)]
pub struct F32x4([f32; 4]);
#[repr(simd)]
pub struct U8x4([u8; 4]);
#[repr(simd)]
pub struct I32x4([i32; 4]);
#[repr(simd)]
pub struct U32x4([u32; 4]);

#[repr(u8)]
pub enum SimdAlign {
    Unaligned = 0,
    Element = 1,
    Vector = 2,
}
impl Copy for SimdAlign {}
impl StructuralPartialEq for SimdAlign {}
impl PartialEq for SimdAlign {
    fn eq(&self, _other: &Self) -> bool { true }
}
impl ConstParamTy_ for SimdAlign {}

#[rustc_intrinsic]
unsafe fn simd_bitmask<T, U>(x: T) -> U;
#[rustc_intrinsic]
unsafe fn simd_as<T, U>(x: T) -> U;
#[rustc_intrinsic]
unsafe fn simd_cast<T, U>(x: T) -> U;
#[rustc_intrinsic]
unsafe fn simd_masked_load<V, U, T, const ALIGN: SimdAlign>(mask: V, ptr: U, val: T) -> T;

#[unsafe(no_mangle)]
pub unsafe fn ir_bitmask(m: I32x8) -> u8 {
    simd_bitmask(m)
}

#[unsafe(no_mangle)]
pub unsafe fn ir_simd_as(x: F32x4) -> U8x4 {
    simd_as(x)
}

#[unsafe(no_mangle)]
pub unsafe fn ir_simd_cast(x: F32x4) -> U8x4 {
    simd_cast(x)
}

#[unsafe(no_mangle)]
pub unsafe fn ir_masked_load_unaligned(m: I32x4, p: *const u32, d: U32x4) -> U32x4 {
    simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Unaligned }>(m, p, d)
}

#[unsafe(no_mangle)]
pub unsafe fn ir_masked_load_elem(m: I32x4, p: *const u32, d: U32x4) -> U32x4 {
    simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Element }>(m, p, d)
}

#[unsafe(no_mangle)]
pub unsafe fn ir_masked_load_vec(m: I32x4, p: *const u32, d: U32x4) -> U32x4 {
    simd_masked_load::<I32x4, *const u32, U32x4, { SimdAlign::Vector }>(m, p, d)
}
"""


PART_D_MCP838_SRC = """\
#![forbid(unsafe_code)]
#![feature(repr_simd)]

#[repr(simd)]
pub struct U32x4(pub [u32; 4]);

pub fn safe_proj_ice(v: U32x4) -> [u32; 4] {
    v.0
}
"""


def _extract_ir_functions(ll_text: str) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    meta: list[str] = []
    cur_name: str | None = None
    cur_lines: list[str] = []
    for raw in ll_text.splitlines():
        line = raw.rstrip()
        if line.startswith("target datalayout =") or line.startswith("target triple ="):
            meta.append(line)
        elif line.startswith("declare ") and ("masked.load" in line or "fptoui" in line):
            meta.append(line)
        elif line.startswith("define "):
            m = re.search(r"@([A-Za-z0-9_.$]+)\(", line)
            cur_name = m.group(1) if m else "unknown"
            cur_lines = [line]
        elif cur_name is not None:
            cur_lines.append(line)
            if line == "}":
                out[cur_name] = cur_lines
                cur_name = None
                cur_lines = []
    out["_meta"] = meta
    return out


def _extract_asm_fn(asm_text: str, sym: str) -> list[str]:
    lines = asm_text.splitlines()
    captured: list[str] = []
    in_fn = False
    for raw in lines:
        s = raw.strip()
        if s == f"{sym}:":
            in_fn = True
            captured.append(raw)
            continue
        if in_fn:
            if s.startswith(".Lfunc_end") or s.startswith(".size"):
                captured.append(raw)
                break
            if not s.startswith(".cfi_"):
                captured.append(raw)
    return captured


def _run_miri_nocore(
    miri_bin: str,
    miri_env: dict[str, str],
    src_path: Path,
    target: str,
    tree_borrows: bool,
    tmpdir: Path,
) -> dict[str, Any]:
    cmd = [miri_bin, "--edition=2024", f"--target={target}", "-Zmiri-strict-provenance"]
    if tree_borrows:
        cmd.append("-Zmiri-tree-borrows")
    cmd.append(str(src_path))
    res = _run(cmd, env=miri_env, cwd=tmpdir)
    return {
        "rc": res["rc"],
        "stdout": _scrub(res["stdout"], tmpdir).strip(),
        "stderr_excerpt": _scrub(res["stderr"], tmpdir)[:900],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        default=str(Path(__file__).resolve().parent / "probe_results.json"),
        help="Path to write JSON results ('-' for stdout)",
    )
    args = parser.parse_args()

    rustc = _find_tool("rustc")
    sysroot = subprocess.check_output([rustc, "--print", "sysroot"], text=True).strip()
    miri_bin = str(Path(sysroot) / "bin" / "miri")
    if not Path(miri_bin).is_file():
        raise RuntimeError(f"miri binary not found at {miri_bin}")

    rustc_vv = subprocess.check_output([rustc, "--version", "--verbose"], text=True).strip()
    miri_env = os.environ.copy()
    ld_prev = miri_env.get("LD_LIBRARY_PATH", "")
    sysroot_lib = str(Path(sysroot) / "lib")
    miri_env["LD_LIBRARY_PATH"] = f"{sysroot_lib}:{ld_prev}" if ld_prev else sysroot_lib
    miri_v = subprocess.check_output([miri_bin, "--version"], env=miri_env, text=True).strip()

    results: dict[str, Any] = {
        "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "rustc_version": rustc_vv,
        "miri_version": miri_v,
    }

    with tempfile.TemporaryDirectory(prefix="simd_probe_") as td:
        tmpdir = Path(td)

        # --- Part A ---
        part_a_std = tmpdir / "part_a_std.rs"
        part_a_bin = tmpdir / "part_a_std"
        part_a_std.write_text(PART_A_STD_SRC)
        comp_a = _run([rustc, "--edition=2024", "-O", str(part_a_std), "-o", str(part_a_bin)])
        nat_a = _run([str(part_a_bin)]) if comp_a["rc"] == 0 else {"rc": -1, "stdout": "", "stderr": "compile failed"}

        part_a_nocore = tmpdir / "part_a_nocore.rs"
        part_a_nocore.write_text(NOCORE_PRELUDE + "\n" + PART_A_NOCORE_MIRI_BODY)
        miri_a_x86_sb = _run_miri_nocore(miri_bin, miri_env, part_a_nocore, "x86_64-unknown-linux-gnu", False, tmpdir)
        miri_a_x86_tb = _run_miri_nocore(miri_bin, miri_env, part_a_nocore, "x86_64-unknown-linux-gnu", True, tmpdir)
        miri_a_s390x_sb = _run_miri_nocore(miri_bin, miri_env, part_a_nocore, "s390x-unknown-linux-gnu", False, tmpdir)
        miri_a_s390x_tb = _run_miri_nocore(miri_bin, miri_env, part_a_nocore, "s390x-unknown-linux-gnu", True, tmpdir)

        results["part_a_valid_masked_load_saturating_as_and_bitmask"] = {
            "native_compile_rc": comp_a["rc"],
            "native_rc": nat_a["rc"],
            "native_stdout": nat_a["stdout"].strip(),
            "miri_nocore_x86_64_sb_bitmask_exit": miri_a_x86_sb["rc"],
            "miri_nocore_x86_64_tb_bitmask_exit": miri_a_x86_tb["rc"],
            "miri_nocore_s390x_sb_bitmask_exit": miri_a_s390x_sb["rc"],
            "miri_nocore_s390x_tb_bitmask_exit": miri_a_s390x_tb["rc"],
            "miri_bitmask_hex": {
                "x86_64_le": f"0x{miri_a_x86_tb['rc']:02x}",
                "s390x_be": f"0x{miri_a_s390x_tb['rc']:02x}",
            },
        }

        # --- Part B ---
        part_b: dict[str, Any] = {}
        for name, spec in PART_B_CASES.items():
            nc_path = tmpdir / f"{name}_nocore.rs"
            nc_path.write_text(NOCORE_PRELUDE + "\n" + spec["nocore_body"])
            miri_x86_sb = _run_miri_nocore(miri_bin, miri_env, nc_path, "x86_64-unknown-linux-gnu", False, tmpdir)
            miri_x86_tb = _run_miri_nocore(miri_bin, miri_env, nc_path, "x86_64-unknown-linux-gnu", True, tmpdir)

            std_path = tmpdir / f"{name}_std.rs"
            std_bin = tmpdir / f"{name}_std"
            std_path.write_text(spec["std_src"])
            comp = _run([rustc, "--edition=2024", "-O", str(std_path), "-o", str(std_bin)])
            nat = _run([str(std_bin)]) if comp["rc"] == 0 else {"rc": -1, "stdout": "", "stderr": "compile failed"}

            entry: dict[str, Any] = {
                "miri_x86_64_sb_rc": miri_x86_sb["rc"],
                "miri_x86_64_tb_rc": miri_x86_tb["rc"],
                "miri_x86_64_tb_stderr": miri_x86_tb["stderr_excerpt"],
                "native_compile_rc": comp["rc"],
                "native_rc": nat["rc"],
                "native_stdout": nat["stdout"].strip(),
            }
            if name == "all_masked_align8_vector_align_target_split":
                miri_s390x_sb = _run_miri_nocore(miri_bin, miri_env, nc_path, "s390x-unknown-linux-gnu", False, tmpdir)
                miri_s390x_tb = _run_miri_nocore(miri_bin, miri_env, nc_path, "s390x-unknown-linux-gnu", True, tmpdir)
                entry["miri_s390x_sb_rc"] = miri_s390x_sb["rc"]
                entry["miri_s390x_tb_rc"] = miri_s390x_tb["rc"]
                entry["miri_s390x_tb_stderr"] = miri_s390x_tb["stderr_excerpt"]
            part_b[name] = entry
        results["part_b_miri_ub_sharpness_matrix"] = part_b

        # --- Part C ---
        ir_src = tmpdir / "part_c_ir.rs"
        ir_src.write_text(PART_C_IR_SRC)
        part_c: dict[str, Any] = {}
        for target in ("x86_64-unknown-linux-gnu", "s390x-unknown-linux-gnu"):
            t_res: dict[str, Any] = {}
            for opt_label, opt_flag in (("opt0", "-Copt-level=0"), ("opt2", "-O")):
                ll_path = tmpdir / f"part_c_{target}_{opt_label}.ll"
                r = _run([
                    rustc,
                    "--edition=2024",
                    "--crate-type=lib",
                    opt_flag,
                    "--emit=llvm-ir",
                    f"--target={target}",
                    str(ir_src),
                    "-o",
                    str(ll_path),
                ])
                t_res[opt_label] = {
                    "rc": r["rc"],
                    "ir": _extract_ir_functions(ll_path.read_text()) if r["rc"] == 0 else {},
                }
            asm_path = tmpdir / f"part_c_{target}_opt2.s"
            r_asm = _run([
                rustc,
                "--edition=2024",
                "--crate-type=lib",
                "-O",
                "--emit=asm",
                f"--target={target}",
                str(ir_src),
                "-o",
                str(asm_path),
            ])
            t_res["asm_ir_bitmask"] = {
                "rc": r_asm["rc"],
                "lines": _extract_asm_fn(asm_path.read_text(), "ir_bitmask") if r_asm["rc"] == 0 else [],
            }
            part_c[target] = t_res
        results["part_c_x86_64_vs_s390x_llvm_ir_and_asm"] = part_c

        # --- Part D ---
        mcp_src = tmpdir / "mcp838_ice.rs"
        mcp_src.write_text(PART_D_MCP838_SRC)
        d_lib = _run([
            rustc, "--edition=2024", "--crate-type=lib", str(mcp_src),
            "-o", str(tmpdir / "libmcp.rlib"),
        ], cwd=tmpdir)
        d_meta = _run([
            rustc, "--edition=2024", "--crate-type=lib", "--emit=metadata", str(mcp_src),
            "-o", str(tmpdir / "libmcp.rmeta"),
        ], cwd=tmpdir)
        d_nomiropt = _run([
            rustc, "--edition=2024", "--crate-type=lib", "-Zmir-opt-level=0", str(mcp_src),
            "-o", str(tmpdir / "libmcp_opt0.rlib"),
        ], cwd=tmpdir)
        results["part_d_mcp838_repr_simd_field_projection_mir_validator_ice"] = {
            "crate_type_lib": {
                "rc": d_lib["rc"],
                "stderr_excerpt": _scrub(d_lib["stderr"], tmpdir)[:1200],
            },
            "emit_metadata_only": {
                "rc": d_meta["rc"],
                "stderr_excerpt": _scrub(d_meta["stderr"], tmpdir)[:600],
            },
            "mir_opt_level_0": {
                "rc": d_nomiropt["rc"],
                "stderr_excerpt": _scrub(d_nomiropt["stderr"], tmpdir)[:1200],
            },
        }

    rendered = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.out == "-":
        sys.stdout.write(rendered)
    else:
        out_path = Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(rendered)
        print(f"Wrote {out_path} ({len(rendered)} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
