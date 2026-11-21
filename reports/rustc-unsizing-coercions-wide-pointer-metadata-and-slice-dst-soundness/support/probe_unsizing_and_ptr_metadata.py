#!/usr/bin/env python3
"""Empirical rustc + Miri probe for unsizing coercions, wide pointer metadata, and dynamic DST layout.

Executes real `rustc` compilations across `-Zmir-opt-level=0..2` (`--emit=mir,llvm-ir`),
runs the native binary to record concrete layout/offset/vtable invariants, and executes a
12-case Miri (`-Zmiri-tree-borrows`) litmus suite against a hermetically compiled `-Zalways-encode-mir`
`core` sysroot so that no network access or external crates are required.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import socket
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


RUST_PROBE_SOURCE = r'''#![feature(
    core_intrinsics,
    ptr_metadata,
    layout_for_ptr,
    unsize,
    coerce_unsized,
    dispatch_from_dyn
)]
#![allow(dead_code, internal_features)]

use std::marker::{PhantomData, Unsize};
use std::mem::{self, offset_of};
use std::ops::{CoerceUnsized, DispatchFromDyn};
use std::ptr::{self, DynMetadata};

#[repr(Rust)]
pub struct DstWrap<T: ?Sized> {
    pub tag: u8,
    pub header: u16,
    pub tail: T,
}

#[repr(Rust)]
pub struct SizedWrap<T> {
    pub tag: u8,
    pub header: u16,
    pub tail: T,
}

#[repr(Rust)]
pub struct OuterWrap<U: ?Sized> {
    pub flag: u8,
    pub magic: u64,
    pub inner: U,
}

#[repr(packed(2))]
pub struct PackedDst<T: ?Sized> {
    pub tag: u8,
    pub tail: mem::ManuallyDrop<T>,
}

pub trait BaseA {
    fn base_a(&self) -> u64;
}

pub trait BaseB {
    fn base_b(&self) -> u64;
}

pub trait SubTrait: BaseA + BaseB {
    fn sub_val(&self) -> u64;
}

#[repr(align(16))]
pub struct AlignedPayload(pub [u64; 3]);

impl BaseA for AlignedPayload {
    #[inline(never)]
    fn base_a(&self) -> u64 {
        self.0[0]
    }
}

impl BaseB for AlignedPayload {
    #[inline(never)]
    fn base_b(&self) -> u64 {
        self.0[1]
    }
}

impl SubTrait for AlignedPayload {
    #[inline(never)]
    fn sub_val(&self) -> u64 {
        self.0[2]
    }
}

pub struct CustomPtr<'a, T: ?Sized> {
    pub raw: *const T,
    pub _lt: PhantomData<&'a T>,
}

impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<CustomPtr<'a, U>> for CustomPtr<'a, T> {}
impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<CustomPtr<'a, U>> for CustomPtr<'a, T> {}

pub struct TaggedPtr<T: ?Sized> {
    pub epoch: u32,
    pub raw: *const T,
}

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<TaggedPtr<U>> for TaggedPtr<T> {}

#[inline(never)]
pub fn s01_array_to_slice_len(a: &[u32; 4]) -> usize {
    let s: &[u32] = a;
    s.len()
}

#[inline(never)]
pub fn s02_zst_slice_max_len() -> (usize, usize, usize) {
    let dangling = ptr::NonNull::<()>::dangling().as_ptr();
    let raw_slice: *const [()] = ptr::from_raw_parts(dangling, usize::MAX);
    let s: &[()] = unsafe { &*raw_slice };
    (ptr::metadata(s), mem::size_of_val(s), mem::align_of_val(s))
}

#[inline(never)]
pub fn s03_dst_wrap_slice_tail(w: &DstWrap<[u32; 4]>) -> (usize, usize, usize, u16, u8, u32) {
    let uw: &DstWrap<[u32]> = w;
    let meta = std::intrinsics::ptr_metadata(uw as *const DstWrap<[u32]>);
    let sz = unsafe { std::intrinsics::size_of_val(uw as *const DstWrap<[u32]>) };
    let al = unsafe { std::intrinsics::align_of_val(uw as *const DstWrap<[u32]>) };
    (meta, sz, al, uw.header, uw.tag, uw.tail[3])
}

#[inline(never)]
pub fn s04_nested_2level_dst_wrap(
    w: &OuterWrap<DstWrap<[u32; 3]>>,
) -> (usize, usize, usize, u64, u16, u32) {
    let uw: &OuterWrap<DstWrap<[u32]>> = w;
    let meta = ptr::metadata(uw);
    let sz = unsafe { mem::size_of_val_raw(uw as *const OuterWrap<DstWrap<[u32]>>) };
    let al = unsafe { mem::align_of_val_raw(uw as *const OuterWrap<DstWrap<[u32]>>) };
    (meta, sz, al, uw.magic, uw.inner.header, uw.inner.tail[2])
}

#[inline(never)]
pub fn s05_dyn_supertrait_upcast(
    p: &AlignedPayload,
) -> (usize, usize, usize, usize, u64, u64, u64, bool) {
    let sub: &dyn SubTrait = p;
    let meta_sub: DynMetadata<dyn SubTrait> = ptr::metadata(sub);
    let up_a: &dyn BaseA = sub;
    let up_b: &dyn BaseB = sub;
    let meta_a: DynMetadata<dyn BaseA> = ptr::metadata(up_a);
    let meta_b: DynMetadata<dyn BaseB> = ptr::metadata(up_b);
    let raw_sub = sub as *const dyn SubTrait as *const () as usize;
    let raw_b = up_b as *const dyn BaseB as *const () as usize;
    let vptr_sub = unsafe { mem::transmute::<DynMetadata<dyn SubTrait>, usize>(meta_sub) };
    let vptr_a = unsafe { mem::transmute::<DynMetadata<dyn BaseA>, usize>(meta_a) };
    let vptr_b = unsafe { mem::transmute::<DynMetadata<dyn BaseB>, usize>(meta_b) };
    let _ = vptr_a;
    (
        meta_sub.size_of(),
        meta_sub.align_of(),
        meta_b.size_of(),
        meta_b.align_of(),
        sub.sub_val(),
        up_a.base_a(),
        up_b.base_b(),
        raw_sub == raw_b && vptr_sub != vptr_b,
    )
}

#[inline(never)]
pub fn s06_dst_wrap_dyn_tail(w: &DstWrap<AlignedPayload>) -> (usize, usize, usize, usize, u64) {
    let uw: &DstWrap<dyn SubTrait> = w;
    let dm: DynMetadata<dyn SubTrait> = ptr::metadata(uw);
    let total_sz = unsafe { mem::size_of_val_raw(uw as *const DstWrap<dyn SubTrait>) };
    let total_al = unsafe { mem::align_of_val_raw(uw as *const DstWrap<dyn SubTrait>) };
    (dm.size_of(), dm.align_of(), total_sz, total_al, uw.tail.sub_val())
}

#[inline(never)]
pub fn s07_custom_coerce_unsized<'a>(
    a: &'a [u32; 4],
    p: &'a AlignedPayload,
) -> (usize, usize, usize) {
    let cp_arr = CustomPtr { raw: a as *const [u32; 4], _lt: PhantomData };
    let cp_slice: CustomPtr<'a, [u32]> = cp_arr;
    let tp_concrete = TaggedPtr { epoch: 77, raw: p as *const AlignedPayload };
    let tp_dyn: TaggedPtr<dyn SubTrait> = tp_concrete;
    let dm = ptr::metadata(tp_dyn.raw);
    (ptr::metadata(cp_slice.raw), tp_dyn.epoch as usize, dm.size_of())
}

#[inline(never)]
pub fn s08_from_raw_parts_roundtrip(s: &[u32], thin_ref: &u32) -> (usize, *const u32) {
    let raw_s: *const [u32] = s;
    let data = raw_s as *const ();
    let len = std::intrinsics::ptr_metadata(raw_s);
    let rebuilt: *const [u32] = std::intrinsics::aggregate_raw_ptr(data, len);
    let rebuilt_thin: *const u32 =
        std::intrinsics::aggregate_raw_ptr(thin_ref as *const u32 as *const (), ());
    (std::intrinsics::ptr_metadata(rebuilt), rebuilt_thin)
}

#[inline(never)]
pub fn s09_size_and_align_peephole(
    x: &u64,
    s: &[u32],
    w: &DstWrap<[u32]>,
) -> (usize, usize, usize, usize, usize, usize) {
    unsafe {
        (
            std::intrinsics::size_of_val(x as *const u64),
            std::intrinsics::align_of_val(x as *const u64),
            std::intrinsics::size_of_val(s as *const [u32]),
            std::intrinsics::align_of_val(s as *const [u32]),
            std::intrinsics::size_of_val(w as *const DstWrap<[u32]>),
            std::intrinsics::align_of_val(w as *const DstWrap<[u32]>),
        )
    }
}

#[inline(never)]
pub fn s10_packed_dst_wrap(w: &PackedDst<AlignedPayload>) -> (usize, usize, u8) {
    let uw: *const PackedDst<dyn SubTrait> = w as *const PackedDst<AlignedPayload>;
    let sz = unsafe { mem::size_of_val_raw(uw) };
    let al = unsafe { mem::align_of_val_raw(uw) };
    let tg = unsafe { (*uw).tag };
    (sz, al, tg)
}

fn main() {
    let arr = [10u32, 20, 30, 40];
    let r01 = s01_array_to_slice_len(&arr);
    let r02 = s02_zst_slice_max_len();

    let dw_arr = DstWrap { tag: 7, header: 0x1234, tail: [1u32, 2, 3, 4] };
    let r03 = s03_dst_wrap_slice_tail(&dw_arr);

    let ow = OuterWrap {
        flag: 1,
        magic: 0xCAFE_BABE,
        inner: DstWrap { tag: 9, header: 0x55AA, tail: [11u32, 22, 33] },
    };
    let r04 = s04_nested_2level_dst_wrap(&ow);

    let payload = AlignedPayload([101, 202, 303]);
    let r05 = s05_dyn_supertrait_upcast(&payload);

    let dw_dyn = DstWrap { tag: 3, header: 0x99, tail: AlignedPayload([7, 8, 9]) };
    let r06 = s06_dst_wrap_dyn_tail(&dw_dyn);

    let r07 = s07_custom_coerce_unsized(&arr, &payload);
    let r08 = s08_from_raw_parts_roundtrip(&arr, &arr[0]);
    let dw_slice_ref: &DstWrap<[u32]> = &dw_arr;
    let r09 = s09_size_and_align_peephole(&42u64, &arr, dw_slice_ref);

    let packed_w = PackedDst { tag: 0x5A, tail: mem::ManuallyDrop::new(AlignedPayload([1, 2, 3])) };
    let r10 = s10_packed_dst_wrap(&packed_w);

    // Measure field-offset invariance across MaybeUnsized (DstWrap<T: ?Sized>) vs
    // AlwaysSized (SizedWrap<T: Sized>)!
    let dst_u8_offsets = (
        offset_of!(DstWrap<u8>, header),
        offset_of!(DstWrap<u8>, tag),
        offset_of!(DstWrap<u8>, tail),
        mem::size_of::<DstWrap<u8>>(),
        mem::align_of::<DstWrap<u8>>(),
    );
    let dst_arr_offsets = (
        offset_of!(DstWrap<[u32; 4]>, header),
        offset_of!(DstWrap<[u32; 4]>, tag),
        offset_of!(DstWrap<[u32; 4]>, tail),
        mem::size_of::<DstWrap<[u32; 4]>>(),
        mem::align_of::<DstWrap<[u32; 4]>>(),
    );
    let dst_u64_offsets = (
        offset_of!(DstWrap<u64>, header),
        offset_of!(DstWrap<u64>, tag),
        offset_of!(DstWrap<u64>, tail),
        mem::size_of::<DstWrap<u64>>(),
        mem::align_of::<DstWrap<u64>>(),
    );
    let dst_aligned16_offsets = (
        offset_of!(DstWrap<AlignedPayload>, header),
        offset_of!(DstWrap<AlignedPayload>, tag),
        offset_of!(DstWrap<AlignedPayload>, tail),
        mem::size_of::<DstWrap<AlignedPayload>>(),
        mem::align_of::<DstWrap<AlignedPayload>>(),
    );
    let sized_u8_offsets = (
        offset_of!(SizedWrap<u8>, header),
        offset_of!(SizedWrap<u8>, tag),
        offset_of!(SizedWrap<u8>, tail),
        mem::size_of::<SizedWrap<u8>>(),
        mem::align_of::<SizedWrap<u8>>(),
    );
    let sized_u64_offsets = (
        offset_of!(SizedWrap<u64>, header),
        offset_of!(SizedWrap<u64>, tag),
        offset_of!(SizedWrap<u64>, tail),
        mem::size_of::<SizedWrap<u64>>(),
        mem::align_of::<SizedWrap<u64>>(),
    );

    // Runtime offset verification on unsized &DstWrap<dyn SubTrait>
    let uw_dyn_ref: &DstWrap<dyn SubTrait> = &dw_dyn;
    let base_addr = uw_dyn_ref as *const DstWrap<dyn SubTrait> as *const u8 as usize;
    let dyn_header_off = (&raw const uw_dyn_ref.header as usize) - base_addr;
    let dyn_tag_off = (&raw const uw_dyn_ref.tag as usize) - base_addr;
    let dyn_tail_off = (&raw const uw_dyn_ref.tail as *const u8 as usize) - base_addr;

    println!(
        "{{\"s01_len\":{},\"s02_zst\":[{},{},{}],\"s03_dst_slice\":[{},{},{},{},{},{}],\"s04_nested\":[{},{},{},{},{},{}],\"s05_dyn_upcast\":[{},{},{},{},{},{},{},{}],\"s06_dst_dyn\":[{},{},{},{},{}],\"s07_custom_ptr\":[{},{},{}],\"s08_roundtrip_len\":{},\"s08_thin_eq\":{},\"s09_peephole\":[{},{},{},{},{},{}],\"s10_packed\":[{},{},{}],\"ptr_sizes\":{{\"thin_ref_u32\":{},\"wide_ref_slice_u32\":{},\"wide_ref_dyn\":{},\"wide_ref_dst_wrap\":{},\"tagged_ptr_thin\":{},\"tagged_ptr_wide\":{}}},\"offsets\":{{\"DstWrap_u8\":[{},{},{},{},{}],\"DstWrap_arr4_u32\":[{},{},{},{},{}],\"DstWrap_u64\":[{},{},{},{},{}],\"DstWrap_Aligned16\":[{},{},{},{},{}],\"DstWrap_dyn_SubTrait_runtime\":[{},{},{}],\"SizedWrap_u8\":[{},{},{},{},{}],\"SizedWrap_u64\":[{},{},{},{},{}]}}}}",
        r01,
        r02.0, r02.1, r02.2,
        r03.0, r03.1, r03.2, r03.3, r03.4, r03.5,
        r04.0, r04.1, r04.2, r04.3, r04.4, r04.5,
        r05.0, r05.1, r05.2, r05.3, r05.4, r05.5, r05.6, str_bool(r05.7),
        r06.0, r06.1, r06.2, r06.3, r06.4,
        r07.0, r07.1, r07.2,
        r08.0, str_bool(r08.1 == (&arr[0] as *const u32)),
        r09.0, r09.1, r09.2, r09.3, r09.4, r09.5,
        r10.0, r10.1, r10.2,
        mem::size_of::<&u32>(),
        mem::size_of::<&[u32]>(),
        mem::size_of::<&dyn SubTrait>(),
        mem::size_of::<&DstWrap<[u32]>>(),
        mem::size_of::<TaggedPtr<u32>>(),
        mem::size_of::<TaggedPtr<[u32]>>(),
        dst_u8_offsets.0, dst_u8_offsets.1, dst_u8_offsets.2, dst_u8_offsets.3, dst_u8_offsets.4,
        dst_arr_offsets.0, dst_arr_offsets.1, dst_arr_offsets.2, dst_arr_offsets.3, dst_arr_offsets.4,
        dst_u64_offsets.0, dst_u64_offsets.1, dst_u64_offsets.2, dst_u64_offsets.3, dst_u64_offsets.4,
        dst_aligned16_offsets.0, dst_aligned16_offsets.1, dst_aligned16_offsets.2, dst_aligned16_offsets.3, dst_aligned16_offsets.4,
        dyn_header_off, dyn_tag_off, dyn_tail_off,
        sized_u8_offsets.0, sized_u8_offsets.1, sized_u8_offsets.2, sized_u8_offsets.3, sized_u8_offsets.4,
        sized_u64_offsets.0, sized_u64_offsets.1, sized_u64_offsets.2, sized_u64_offsets.3, sized_u64_offsets.4,
    );
}

fn str_bool(b: bool) -> &'static str {
    if b { "true" } else { "false" }
}
'''


MIRI_PRELUDE = r'''#![feature(ptr_metadata, layout_for_ptr, unsize, coerce_unsized, dispatch_from_dyn)]
#![allow(dead_code, unused_unsafe)]
#![no_std]
#![no_main]

use core::mem;
use core::ptr::{self, DynMetadata, NonNull};

#[repr(Rust)]
struct DstWrap<T: ?Sized> {
    tag: u8,
    header: u16,
    tail: T,
}

#[repr(packed(2))]
struct PackedDst<T: ?Sized> {
    tag: u8,
    tail: mem::ManuallyDrop<T>,
}

#[repr(align(16))]
struct AlignedPayload([u64; 3]);

#[repr(align(8))]
struct ZeroSizedAlign8;

trait BaseA {
    fn a(&self) -> u64;
}
trait BaseB {
    fn b(&self) -> u64;
}
trait SubTrait: BaseA + BaseB {
    fn s(&self) -> u64;
}
trait UnrelatedTrait {
    fn u(&self) -> u64;
}

impl BaseA for AlignedPayload {
    fn a(&self) -> u64 { self.0[0] }
}
impl BaseB for AlignedPayload {
    fn b(&self) -> u64 { self.0[1] }
}
impl SubTrait for AlignedPayload {
    fn s(&self) -> u64 { self.0[2] }
}
impl UnrelatedTrait for AlignedPayload {
    fn u(&self) -> u64 { self.0[0] ^ self.0[2] }
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}
'''


MIRI_CASES: list[tuple[str, bool, str, str]] = [
    (
        "m01_valid_array_to_slice_and_raw_parts",
        True,
        "Valid &[u32; 4] -> &[u32] unsizing, raw-parts round-trip, and size_of_val_raw == 16",
        r'''
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let arr = [10u32, 20, 30, 40];
    let s: &[u32] = &arr;
    let raw = s as *const [u32];
    let rebuilt: *const [u32] = ptr::from_raw_parts(raw as *const (), ptr::metadata(raw));
    assert_eq!(unsafe { mem::size_of_val_raw(rebuilt) }, 16);
    assert_eq!(unsafe { mem::align_of_val_raw(rebuilt) }, 4);
    assert_eq!(unsafe { (&*rebuilt)[2] }, 30);
    0
}
''',
    ),
    (
        "m02_valid_zst_slice_usize_max",
        True,
        "Valid ZST slice &[(); usize::MAX] with 0 total byte size <= isize::MAX",
        r'''
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let raw: *const [()] = ptr::from_raw_parts(NonNull::<()>::dangling().as_ptr(), usize::MAX);
    let s: &[()] = unsafe { &*raw };
    assert_eq!(ptr::metadata(s), usize::MAX);
    assert_eq!(unsafe { mem::size_of_val_raw(raw) }, 0);
    assert_eq!(unsafe { mem::align_of_val_raw(raw) }, 1);
    0
}
''',
    ),
    (
        "m03_valid_nested_dst_wrap_slice_and_dyn",
        True,
        "Valid custom DST struct-tail unsizing for both [u32; 4] -> [u32] and AlignedPayload -> dyn SubTrait",
        r'''
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let ws = DstWrap { tag: 7, header: 0x1234, tail: [1u32, 2, 3, 4] };
    let uws: &DstWrap<[u32]> = &ws;
    assert_eq!(ptr::metadata(uws), 4);
    assert_eq!(unsafe { mem::size_of_val_raw(uws as *const DstWrap<[u32]>) }, mem::size_of::<DstWrap<[u32; 4]>>());
    assert_eq!(unsafe { mem::align_of_val_raw(uws as *const DstWrap<[u32]>) }, mem::align_of::<DstWrap<[u32; 4]>>());

    let wd = DstWrap { tag: 9, header: 0x5678, tail: AlignedPayload([11, 22, 33]) };
    let uwd: &DstWrap<dyn SubTrait> = &wd;
    assert_eq!(unsafe { mem::size_of_val_raw(uwd as *const DstWrap<dyn SubTrait>) }, mem::size_of::<DstWrap<AlignedPayload>>());
    assert_eq!(unsafe { mem::align_of_val_raw(uwd as *const DstWrap<dyn SubTrait>) }, mem::align_of::<DstWrap<AlignedPayload>>());
    let up_b: &dyn BaseB = &uwd.tail;
    assert_eq!(up_b.b(), 22);
    0
}
''',
    ),
    (
        "m04_valid_packed2_dyn_dst_size_align",
        True,
        "Valid #[repr(packed(2))] custom DST with 16-aligned dyn payload: align capped to 2 and size == 34",
        r'''
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let pw = PackedDst { tag: 0x3C, tail: mem::ManuallyDrop::new(AlignedPayload([5, 6, 7])) };
    let upw: *const PackedDst<dyn SubTrait> = &raw const pw;
    assert_eq!(unsafe { mem::size_of_val_raw(upw) }, 34);
    assert_eq!(unsafe { mem::align_of_val_raw(upw) }, 2);
    0
}
''',
    ),
    (
        "m05_valid_zero_len_dangling_slice_size_of_val_raw",
        True,
        "Valid size_of_val_raw on zero-length dangling raw slice pointer without dereference",
        r'''
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let raw: *const [u64] = ptr::from_raw_parts(core::ptr::without_provenance::<()>(8), 0);
    assert_eq!(unsafe { mem::size_of_val_raw(raw) }, 0);
    assert_eq!(unsafe { mem::align_of_val_raw(raw) }, 8);
    0
}
''',
    ),
    (
        "m06_ub_slice_size_of_val_raw_isize_overflow",
        False,
        "UB: size_of_val_raw::<[u32]> when len * 4 == isize::MAX + 1 exceeds isize::MAX (InvalidMeta::SliceTooBig)",
        r'''
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let x = 0u32;
    let bad_len = (isize::MAX as usize / 4) + 1;
    let raw: *const [u32] = ptr::from_raw_parts(&raw const x as *const (), bad_len);
    let _sz = unsafe { mem::size_of_val_raw(raw) };
    0
}
''',
    ),
    (
        "m07_ub_slice_size_of_val_raw_u64_wrap_boundary",
        False,
        "UB: size_of_val_raw::<[u32]> at len = 2^62 + 1 where wrapping len * 4 == 4 mod 2^64 (sharpness witness for CE1)",
        r'''
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let buf = [0u32; 2];
    let wrap_len = (1usize << 62) + 1;
    let raw: *const [u32] = ptr::from_raw_parts(&raw const buf as *const (), wrap_len);
    let _sz = unsafe { mem::size_of_val_raw(raw) };
    0
}
''',
    ),
    (
        "m08_ub_struct_tail_prefix_pushes_over_isize_max",
        False,
        "UB: DstWrap<[u8]> where slice tail alone fits isize::MAX - 1, but prefix + tail rounding exceeds isize::MAX (InvalidMeta::TooBig)",
        r'''
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let b = 0u8;
    let tail_len = (isize::MAX as usize) - 1;
    let ok_slice: *const [u8] = ptr::from_raw_parts(&raw const b as *const (), tail_len);
    assert_eq!(unsafe { mem::size_of_val_raw(ok_slice) }, tail_len);
    let bad_struct: *const DstWrap<[u8]> = ptr::from_raw_parts(&raw const b as *const (), tail_len);
    let _sz = unsafe { mem::size_of_val_raw(bad_struct) };
    0
}
''',
    ),
    (
        "m09_ub_forged_non_vtable_dyn_metadata",
        False,
        "UB: size_of_val_raw::<dyn SubTrait> with forged non-vtable pointer in DynMetadata",
        r'''
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let fake_vtable: [usize; 8] = [0, 32, 16, 0, 0, 0, 0, 0];
    let vptr = NonNull::new(&raw const fake_vtable as *mut ()).unwrap();
    let bad_meta: DynMetadata<dyn SubTrait> = unsafe { mem::transmute(vptr) };
    let payload = AlignedPayload([1, 2, 3]);
    let raw: *const dyn SubTrait = ptr::from_raw_parts(&raw const payload as *const (), bad_meta);
    let _sz = unsafe { mem::size_of_val_raw(raw) };
    0
}
''',
    ),
    (
        "m10_ub_wrong_trait_vtable_transmute",
        False,
        "UB: size_of_val_raw::<dyn SubTrait> when DynMetadata was unsized for UnrelatedTrait",
        r'''
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let payload = AlignedPayload([1, 2, 3]);
    let unrelated: &dyn UnrelatedTrait = &payload;
    let wrong_meta: DynMetadata<dyn SubTrait> = unsafe {
        mem::transmute::<DynMetadata<dyn UnrelatedTrait>, DynMetadata<dyn SubTrait>>(ptr::metadata(unrelated))
    };
    let raw: *const dyn SubTrait = ptr::from_raw_parts(&raw const payload as *const (), wrong_meta);
    let _sz = unsafe { mem::size_of_val_raw(raw) };
    0
}
''',
    ),
    (
        "m11_ub_misaligned_zst_slice_reference",
        False,
        "UB: constructing &[ZeroSizedAlign8] reference with len = 0 at misaligned address 4",
        r'''
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let raw: *const [ZeroSizedAlign8] =
        ptr::from_raw_parts(core::ptr::without_provenance::<()>(4), 0);
    let _bad_ref: &[ZeroSizedAlign8] = unsafe { &*raw };
    0
}
''',
    ),
    (
        "m12_ub_null_zst_slice_reference",
        False,
        "UB: constructing &[()] reference with len = 0 from null data pointer",
        r'''
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let raw: *const [()] = ptr::from_raw_parts(core::ptr::null::<()>(), 0);
    let _bad_ref: &[()] = unsafe { &*raw };
    0
}
''',
    ),
]


def scrub_text(text: str, replacements: list[tuple[str, str]]) -> str:
    out = text
    for src, dst in replacements:
        if src:
            out = out.replace(src, dst)
    home_prefix = str(Path.home().parent) + "/"
    if home_prefix != "//":
        out = re.sub(re.escape(home_prefix) + r"[^/\s:\"']+", "<USER_HOME>", out)
    tmp_prefix = str(Path(tempfile.gettempdir())) + "/"
    out = re.sub(re.escape(tmp_prefix) + r"[^/\s:\"']+", "<TMP>", out)
    return out


def extract_mir_functions(mir_text: str) -> dict[str, str]:
    """Split emitted `.mir` text into top-level `fn <name>(...) -> ... { ... }` bodies."""
    fns: dict[str, str] = {}
    lines = mir_text.splitlines()
    cur_name: str | None = None
    cur_lines: list[str] = []
    brace_depth = 0
    header_re = re.compile(r"^fn\s+([A-Za-z0-9_]+)\s*\(")
    for line in lines:
        if cur_name is None:
            m = header_re.match(line)
            if m:
                cur_name = m.group(1)
                cur_lines = [line]
                brace_depth = line.count("{") - line.count("}")
        else:
            cur_lines.append(line)
            brace_depth += line.count("{") - line.count("}")
            if brace_depth <= 0:
                fns[cur_name] = "\n".join(cur_lines)
                cur_name = None
                cur_lines = []
    return fns


def summarize_mir_body(body: str) -> dict[str, Any]:
    return {
        "ptr_metadata_ops": len(re.findall(r"\bPtrMetadata\(", body)),
        "unsize_coercions": len(re.findall(r"PointerCoercion\(Unsize", body)),
        "raw_ptr_aggregates": len(re.findall(r"\*const\b.*from\s*\(|Aggregate.*RawPtr", body))
        + len(re.findall(r"= \*const \[|= \*const u32 from|= \*const dyn", body)),
        "ptr_to_ptr_casts": len(re.findall(r"\(PtrToPtr\)", body)),
        "slice_len_calls": len(re.findall(r"::len\(", body)),
        "size_of_val_calls": len(re.findall(r"size_of_val", body)),
        "align_of_val_calls": len(re.findall(r"align_of_val", body)),
        "const_4_usize": "const 4_usize" in body,
        "const_3_usize": "const 3_usize" in body,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).resolve().parent / "unsizing_probe_results.json",
        help="Path to write scrubbed JSON probe results",
    )
    args = parser.parse_args()

    env = os.environ.copy()
    cargo_bin = Path.home() / ".cargo" / "bin"
    if cargo_bin.is_dir():
        env["PATH"] = f"{cargo_bin}:{env.get('PATH', '')}"

    rustc_ver = subprocess.run(
        ["rustc", "-vV"], env=env, check=True, capture_output=True, text=True
    ).stdout.strip()
    sysroot = Path(
        subprocess.run(
            ["rustc", "--print", "sysroot"],
            env=env,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
    )
    miri_bin = sysroot / "bin" / "miri"
    if not miri_bin.is_file():
        raise RuntimeError("miri binary not found in rustc sysroot")

    miri_ver = subprocess.run(
        [str(miri_bin), "--version"], env=env, check=True, capture_output=True, text=True
    ).stdout.strip()

    target_triple = "x86_64-unknown-linux-gnu"
    for line in rustc_ver.splitlines():
        if line.startswith("host:"):
            target_triple = line.split(":", 1)[1].strip()

    hostname = socket.gethostname()

    with tempfile.TemporaryDirectory(prefix="unsizing_probe_") as tmp_str:
        tmpdir = Path(tmp_str)
        replacements = [
            (str(sysroot), "<SYSROOT>"),
            (str(tmpdir), "<TMPDIR>"),
            (hostname, "<HOST>"),
        ]

        probe_rs = tmpdir / "probe_specimens.rs"
        probe_rs.write_text(RUST_PROBE_SOURCE, encoding="utf-8")

        target_fns = [
            "s01_array_to_slice_len",
            "s02_zst_slice_max_len",
            "s03_dst_wrap_slice_tail",
            "s04_nested_2level_dst_wrap",
            "s05_dyn_supertrait_upcast",
            "s06_dst_wrap_dyn_tail",
            "s07_custom_coerce_unsized",
            "s08_from_raw_parts_roundtrip",
            "s09_size_and_align_peephole",
            "s10_packed_dst_wrap",
        ]

        mir_levels_summary: dict[str, Any] = {}
        llvm_highlights: dict[str, Any] = {}

        for opt_lvl in (0, 1, 2):
            out_dir = tmpdir / f"mir_opt_{opt_lvl}"
            out_dir.mkdir(parents=True, exist_ok=True)
            subprocess.run(
                [
                    "rustc",
                    "--edition=2024",
                    "--crate-name=probe_specimens",
                    f"-Zmir-opt-level={opt_lvl}",
                    "-Copt-level=0",
                    "--emit=mir,llvm-ir",
                    "--out-dir",
                    str(out_dir),
                    str(probe_rs),
                ],
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )
            mir_text = (out_dir / "probe_specimens.mir").read_text(encoding="utf-8")
            ll_text = (out_dir / "probe_specimens.ll").read_text(encoding="utf-8")
            fn_map = extract_mir_functions(mir_text)
            mir_levels_summary[f"mir_opt_level_{opt_lvl}"] = {
                fn_name: summarize_mir_body(fn_map[fn_name])
                for fn_name in target_fns
                if fn_name in fn_map
            }
            if opt_lvl == 2:
                llvm_highlights = {
                    "unchecked_sumul_nuw_nsw_present": bool(
                        re.search(r"mul nuw nsw i64 %[A-Za-z0-9_.]*, 4", ll_text)
                    ),
                    "dst_align_bitmask_roundup_present": bool(
                        re.search(r"and i64 %[A-Za-z0-9_.]*, %[A-Za-z0-9_.]*", ll_text)
                    ),
                    "s01_mir_body_opt2": scrub_text(
                        fn_map["s01_array_to_slice_len"], replacements
                    ),
                    "s03_mir_body_opt2": scrub_text(
                        fn_map["s03_dst_wrap_slice_tail"], replacements
                    ),
                }
            if opt_lvl == 0:
                s01_mir_opt0 = scrub_text(fn_map["s01_array_to_slice_len"], replacements)
            if opt_lvl == 1:
                s01_mir_opt1 = scrub_text(fn_map["s01_array_to_slice_len"], replacements)

        llvm_highlights["s01_mir_body_opt0"] = s01_mir_opt0
        llvm_highlights["s01_mir_body_opt1"] = s01_mir_opt1

        # Compile and run native binary
        bin_path = tmpdir / "probe_specimens_bin"
        subprocess.run(
            [
                "rustc",
                "--edition=2024",
                "-O",
                str(probe_rs),
                "-o",
                str(bin_path),
            ],
            env=env,
            check=True,
            capture_output=True,
            text=True,
        )
        native_out = subprocess.run(
            [str(bin_path)], env=env, check=True, capture_output=True, text=True
        ).stdout.strip()
        native_metrics = json.loads(native_out)

        # Build hermetic Miri no_std sysroot (`libcore.rlib` + `libcompiler_builtins.rlib`)
        miri_sysroot = tmpdir / "miri_sysroot"
        miri_libdir = miri_sysroot / "lib" / "rustlib" / target_triple / "lib"
        miri_libdir.mkdir(parents=True, exist_ok=True)

        core_src = sysroot / "lib" / "rustlib" / "src" / "rust" / "library" / "core" / "src" / "lib.rs"
        subprocess.run(
            [
                "rustc",
                "--edition=2024",
                "--crate-name",
                "core",
                "--crate-type",
                "rlib",
                "-Cpanic=abort",
                "-Zalways-encode-mir",
                str(core_src),
                "-o",
                str(miri_libdir / "libcore.rlib"),
            ],
            env=env,
            check=True,
            capture_output=True,
            text=True,
        )
        cb_stub = tmpdir / "cb_stub.rs"
        cb_stub.write_text(
            "#![feature(compiler_builtins, no_core)]\n#![no_core]\n#![compiler_builtins]\n",
            encoding="utf-8",
        )
        subprocess.run(
            [
                "rustc",
                "--edition=2024",
                "--crate-name",
                "compiler_builtins",
                "--crate-type",
                "rlib",
                "-Cpanic=abort",
                str(cb_stub),
                "-o",
                str(miri_libdir / "libcompiler_builtins.rlib"),
            ],
            env=env,
            check=True,
            capture_output=True,
            text=True,
        )

        miri_results: list[dict[str, Any]] = []
        for case_id, expect_pass, desc, case_body in MIRI_CASES:
            case_rs = tmpdir / f"{case_id}.rs"
            case_rs.write_text(MIRI_PRELUDE + "\n" + case_body, encoding="utf-8")
            proc = subprocess.run(
                [
                    str(miri_bin),
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Zmiri-tree-borrows",
                    "--sysroot",
                    str(miri_sysroot),
                    str(case_rs),
                ],
                env=env,
                capture_output=True,
                text=True,
            )
            passed = proc.returncode == 0
            if passed != expect_pass:
                raise RuntimeError(
                    f"Miri case {case_id} expected pass={expect_pass}, got rc={proc.returncode}:\n{proc.stderr}"
                )
            ub_headline = None
            for line in proc.stderr.splitlines():
                if "Undefined Behavior:" in line:
                    ub_headline = scrub_text(line.strip(), replacements)
                    break
            miri_results.append(
                {
                    "case_id": case_id,
                    "description": desc,
                    "expected": "PASS" if expect_pass else "UB",
                    "observed": "PASS" if passed else "UB",
                    "exit_code": proc.returncode,
                    "ub_diagnostic": ub_headline,
                }
            )

    payload = {
        "toolchain": {
            "rustc_verbose_version": scrub_text(rustc_ver, []),
            "miri_version": scrub_text(miri_ver, []),
            "target_triple": target_triple,
        },
        "mir_opt_sweep": mir_levels_summary,
        "mir_and_llvm_highlights": llvm_highlights,
        "native_execution": native_metrics,
        "miri_tree_borrows_suite": {
            "total_cases": len(miri_results),
            "expected_matches": sum(1 for r in miri_results if r["expected"] == r["observed"]),
            "valid_pass_cases": sum(1 for r in miri_results if r["observed"] == "PASS"),
            "ub_caught_cases": sum(1 for r in miri_results if r["observed"] == "UB"),
            "cases": miri_results,
        },
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    serialized = json.dumps(payload, indent=2, sort_keys=False) + "\n"
    # Final defensive check against local host or user-home leaks
    home_str = str(Path.home())
    tmp_root = str(Path(tempfile.gettempdir())) + "/"
    for forbidden in (home_str, tmp_root, hostname):
        if forbidden and forbidden in serialized:
            raise AssertionError(f"Forbidden host/path substring {forbidden!r} leaked into JSON output")
    args.out.write_text(serialized, encoding="utf-8")
    print(f"Wrote {args.out.name} ({len(miri_results)}/12 Miri cases matched, 3 MIR opt levels)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
