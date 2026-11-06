// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![no_std]
#![allow(internal_features)]
#![feature(core_intrinsics)]

use core::cell::UnsafeCell;
use core::mem::{MaybeUninit, align_of, size_of, transmute, transmute_copy};
use core::num::NonZeroUsize;
use core::ptr;

// ============================================================================
// Category 1: Aggregates, Arrays, Slices, and Enums
// ============================================================================

#[derive(Copy, Clone)]
pub struct Pair {
    pub a: u32,
    pub b: u64,
}

pub struct ReorderRust {
    pub a: u8,
    pub b: u64,
    pub c: u16,
}

#[repr(C)]
pub struct PairC {
    pub a: u8,
    pub b: u64,
    pub c: u16,
}

#[repr(transparent)]
pub struct Wrapper(pub u64);

#[repr(C, packed)]
pub struct PackedPair {
    pub a: u8,
    pub b: u64,
}

#[repr(u8)]
#[derive(Copy, Clone)]
pub enum CLike {
    A = 1,
    B = 2,
    C = 255,
}

pub enum DataEnum {
    Empty,
    Val(u64),
    Pair { x: u32, y: u64 },
}

pub fn cat1_make_pair(a: u32, b: u64) -> Pair {
    Pair { a, b }
}

pub fn cat1_make_reorder_rust(a: u8, b: u64, c: u16) -> ReorderRust {
    ReorderRust { a, b, c }
}

pub fn cat1_make_pair_c(a: u8, b: u64, c: u16) -> PairC {
    PairC { a, b, c }
}

pub fn cat1_make_wrapper(x: u64) -> Wrapper {
    Wrapper(x)
}

pub fn cat1_make_packed(a: u8, b: u64) -> PackedPair {
    PackedPair { a, b }
}

pub fn cat1_make_tuple(a: u8, b: u64) -> (u8, u64) {
    (a, b)
}

pub fn cat1_make_fixed_array(x: u32, y: u32) -> [u32; 4] {
    [x, y, 10, 20]
}

pub fn cat1_make_array_repeat_zero() -> [u8; 16] {
    [0u8; 16]
}

pub fn cat1_make_array_repeat_val(v: u8) -> [u8; 16] {
    [v; 16]
}

pub fn cat1_slices_passthrough<'a>(s: &'a [u8], m: &'a mut [u8]) -> (&'a [u8], &'a mut [u8]) {
    (s, m)
}

pub fn cat1_make_option_usize(x: usize, some: bool) -> Option<usize> {
    if some { Some(x) } else { None }
}

pub fn cat1_make_option_nonzero(x: NonZeroUsize, some: bool) -> Option<NonZeroUsize> {
    if some { Some(x) } else { None }
}

pub fn cat1_make_result(ok_val: usize, err_val: u32, is_ok: bool) -> Result<usize, u32> {
    if is_ok { Ok(ok_val) } else { Err(err_val) }
}

pub fn cat1_make_enums(x: u32, y: u64) -> (CLike, DataEnum, DataEnum, DataEnum) {
    (CLike::B, DataEnum::Empty, DataEnum::Val(y), DataEnum::Pair { x, y })
}

// ============================================================================
// Category 2: Nested Place Projections & Raw Pointers
// ============================================================================

pub fn cat2_nested_tuple_proj(t: ((u32, u64), u8)) -> u64 {
    t.0.1
}

pub fn cat2_deref_field_proj(p: &Pair) -> u64 {
    (*p).b
}

pub fn cat2_reorder_field_proj(r: &ReorderRust) -> (u8, u64, u16) {
    (r.a, r.b, r.c)
}

pub fn cat2_array_index(arr: &[u32; 4], idx: usize) -> u32 {
    arr[idx]
}

pub fn cat2_slice_index(slice: &[u8], idx: usize) -> u8 {
    slice[idx]
}

pub unsafe fn cat2_raw_ptr_deref(ptr: *const Pair) -> u64 {
    unsafe { (*ptr).b }
}

pub unsafe fn cat2_raw_const_proj(ptr: *const Pair) -> *const u64 {
    unsafe { &raw const (*ptr).b }
}

pub unsafe fn cat2_raw_mut_proj(ptr: *mut Pair) -> *mut u64 {
    unsafe { &raw mut (*ptr).b }
}

pub unsafe fn cat2_addr_of_macros(ptr: *mut Pair) -> (*const u64, *mut u32) {
    unsafe { (ptr::addr_of!((*ptr).b), ptr::addr_of_mut!((*ptr).a)) }
}

pub unsafe fn cat2_packed_raw_proj(ptr: *const PackedPair) -> *const u64 {
    unsafe { &raw const (*ptr).b }
}

// ============================================================================
// Category 3: Casts, Provenance APIs, and Wide Pointer Metadata
// ============================================================================

pub fn cat3_int_casts(u8_val: u8, i32_val: i32, u64_val: u64) -> (u64, i64, u32, u32) {
    let widen_u = u8_val as u64;
    let sext_i = i32_val as i64;
    let trunc_u = u64_val as u32;
    let sign_cast = i32_val as u32;
    (widen_u, sext_i, trunc_u, sign_cast)
}

pub fn cat3_ptr_to_addr_as(ptr: *const u64) -> usize {
    ptr as usize
}

pub fn cat3_ptr_to_addr_method(ptr: *const u64) -> usize {
    ptr.addr()
}

pub fn cat3_ptr_expose_provenance(ptr: *const u64) -> usize {
    ptr.expose_provenance()
}

pub fn cat3_addr_to_ptr_as(addr: usize) -> *const u64 {
    addr as *const u64
}

pub fn cat3_with_exposed_provenance(addr: usize) -> *const u64 {
    ptr::with_exposed_provenance::<u64>(addr)
}

pub fn cat3_without_provenance(addr: usize) -> (*const u64, *mut u64) {
    (ptr::without_provenance::<u64>(addr), ptr::without_provenance_mut::<u64>(addr))
}

pub fn cat3_ref_to_raw_ptr(r: &u64, m: &mut u64) -> (*const u64, *mut u64, *const u8) {
    let p_const = r as *const u64;
    let p_mut = m as *mut u64;
    let p_u8 = p_const as *const u8;
    (p_const, p_mut, p_u8)
}

pub fn cat3_array_to_slice_unsize(arr: &[u32; 4]) -> &[u32] {
    arr as &[u32]
}

pub fn cat3_slice_len(s: &[u8]) -> usize {
    s.len()
}

pub fn cat3_ptr_metadata_intrinsic(s: *const [u8]) -> usize {
    core::intrinsics::ptr_metadata(s)
}

// ============================================================================
// Category 4: Loops & Control Flow
// ============================================================================

pub fn cat4_while_loop(mut n: usize) -> usize {
    let mut acc = 0usize;
    while n > 0 {
        acc = acc.wrapping_add(n);
        n -= 1;
    }
    acc
}

pub fn cat4_loop_break_continue(mut n: usize) -> usize {
    let mut acc = 0usize;
    loop {
        if n == 0 {
            break acc;
        }
        n -= 1;
        if n & 1 == 0 {
            continue;
        }
        acc += n;
    }
}

pub fn cat4_for_range(n: usize) -> usize {
    let mut acc = 0usize;
    for i in 0..n {
        acc = acc.wrapping_add(i);
    }
    acc
}

pub fn cat4_match_int(x: u32) -> u32 {
    match x {
        0 => 10,
        1 => 20,
        2 | 3 => 30,
        _ => x,
    }
}

pub fn cat4_match_clike(e: CLike) -> u8 {
    match e {
        CLike::A => 10,
        CLike::B => 20,
        CLike::C => 30,
    }
}

pub fn cat4_match_data_enum(e: DataEnum) -> u64 {
    match e {
        DataEnum::Empty => 0,
        DataEnum::Val(v) => v,
        DataEnum::Pair { x, y } => (x as u64).wrapping_add(y),
    }
}

pub fn cat4_match_option_usize(o: Option<usize>) -> usize {
    match o {
        Some(v) => v,
        None => 0,
    }
}

pub fn cat4_match_option_nonzero(o: Option<NonZeroUsize>) -> usize {
    match o {
        Some(v) => v.get(),
        None => 0,
    }
}

pub fn cat4_arith_and_div_checks(a: u64, b: u64, sh: u32) -> (u64, u64, u64) {
    (a + b, a << sh, a / b)
}

// ============================================================================
// Category 5: Calls & Generics
// ============================================================================

#[inline(never)]
pub fn callee_0() -> u64 {
    42
}

#[inline(never)]
pub fn callee_1(a: u64) -> u64 {
    a
}

#[inline(never)]
pub fn callee_2(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}

#[inline(never)]
pub fn callee_3(a: u64, b: u64, c: u64) -> u64 {
    a.wrapping_add(b).wrapping_add(c)
}

#[inline(never)]
pub fn callee_7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64) -> u64 {
    a.wrapping_add(b)
        .wrapping_add(c)
        .wrapping_add(d)
        .wrapping_add(e)
        .wrapping_add(f)
        .wrapping_add(g)
}

pub fn cat5_calls(x: u64) -> u64 {
    let r0 = callee_0();
    let r1 = callee_1(r0);
    let r2 = callee_2(r1, x);
    let r3 = callee_3(r1, r2, x);
    callee_7(r0, r1, r2, r3, x, 1, 2)
}

pub fn cat5_generic_id<T: Copy>(x: T) -> T {
    x
}

pub fn cat5_call_generic(p: Pair) -> Pair {
    cat5_generic_id(p)
}

pub trait ComputeTrait {
    fn compute(self, factor: u64) -> u64;
}

impl ComputeTrait for u64 {
    #[inline(never)]
    fn compute(self, factor: u64) -> u64 {
        self.wrapping_mul(factor)
    }
}

pub fn cat5_trait_generic<T: ComputeTrait>(x: T, factor: u64) -> u64 {
    <T as ComputeTrait>::compute(x, factor)
}

pub fn cat5_trait_mono(x: u64, factor: u64) -> u64 {
    cat5_trait_generic(x, factor)
}

#[track_caller]
#[inline(never)]
pub fn cat5_tracked_callee(x: usize) -> usize {
    let loc = core::panic::Location::caller();
    x.wrapping_add(loc.line() as usize)
}

pub fn cat5_call_tracked(x: usize) -> usize {
    cat5_tracked_callee(x)
}

// ============================================================================
// Category 6: Core Intrinsics Used by `zerocopy`
// ============================================================================

pub fn cat6_size_and_align() -> (usize, usize) {
    (size_of::<Pair>(), align_of::<Pair>())
}

pub fn cat6_transmute(x: u64) -> [u32; 2] {
    unsafe { transmute::<u64, [u32; 2]>(x) }
}

pub unsafe fn cat6_transmute_copy(x: &u64) -> [u32; 2] {
    unsafe { transmute_copy::<u64, [u32; 2]>(x) }
}

pub unsafe fn cat6_ptr_read(p: *const u64) -> u64 {
    unsafe { ptr::read(p) }
}

pub unsafe fn cat6_ptr_write(p: *mut u64, v: u64) {
    unsafe { ptr::write(p, v) }
}

pub unsafe fn cat6_ptr_copy(src: *const u64, dst: *mut u64, count: usize) {
    unsafe { ptr::copy(src, dst, count) }
}

pub unsafe fn cat6_ptr_copy_nonoverlapping(src: *const u64, dst: *mut u64, count: usize) {
    unsafe { ptr::copy_nonoverlapping(src, dst, count) }
}

pub unsafe fn cat6_ptr_write_bytes(dst: *mut u64, val: u8, count: usize) {
    unsafe { ptr::write_bytes(dst, val, count) }
}

pub unsafe fn cat6_unreachable_unchecked() -> ! {
    unsafe { core::hint::unreachable_unchecked() }
}

pub unsafe fn cat6_maybe_uninit(v: u64) -> u64 {
    let mut u: MaybeUninit<u64> = MaybeUninit::uninit();
    u.write(v);
    unsafe { u.assume_init() }
}

pub fn cat6_unsafe_cell_get(c: &UnsafeCell<u64>) -> *mut u64 {
    c.get()
}

// Direct `core::intrinsics::*` calls (bypassing `core` wrapper functions)
pub unsafe fn cat6_direct_intrinsics(
    src: *const u64,
    dst: *mut u64,
    count: usize,
) -> (usize, usize, u64, bool) {
    let sz = const { core::intrinsics::size_of::<Pair>() };
    let al = const { core::intrinsics::align_of::<Pair>() };
    let v = unsafe { core::intrinsics::read_via_copy(src) };
    unsafe { core::intrinsics::write_via_move(dst, v) };
    unsafe { core::intrinsics::copy(src, dst, count) };
    unsafe { core::intrinsics::copy_nonoverlapping(src, dst, count) };
    unsafe { core::intrinsics::write_bytes(dst, 0u8, count) };
    let ub = core::intrinsics::ub_checks();
    (sz, al, v, ub)
}

pub unsafe fn cat6_direct_unreachable() -> ! {
    unsafe { core::intrinsics::unreachable() }
}
