// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![no_std]
#![feature(repr_simd, core_intrinsics)]
#![allow(internal_features, non_camel_case_types)]

use core::intrinsics::simd::*;

#[repr(simd)]
#[derive(Copy, Clone)]
pub struct u32x4([u32; 4]);

#[repr(simd)]
#[derive(Copy, Clone)]
pub struct u32x8([u32; 8]);

#[repr(simd)]
#[derive(Copy, Clone)]
pub struct u32x16([u32; 16]);

#[repr(simd)]
#[derive(Copy, Clone)]
pub struct i32x8([i32; 8]);

#[repr(simd)]
#[derive(Copy, Clone)]
pub struct f32x8([f32; 8]);

// Family 1: 512-bit u32x16 arithmetic + bitwise (legalized to 2x256 on AVX2, 4x128 on NEON/i686)
#[no_mangle]
pub unsafe fn probe_f1_u32x16_alu(a: u32x16, b: u32x16) -> u32x16 {
    let sum = simd_add(a, b);
    let xored = simd_xor(sum, b);
    simd_bswap(xored)
}

// Family 2: Saturating arithmetic
#[no_mangle]
pub unsafe fn probe_f2_u32x8_sat(a: u32x8, b: u32x8) -> u32x8 {
    simd_saturating_add(a, b)
}

// Family 3: Comparisons, bitmask, and select_bitmask
#[no_mangle]
pub unsafe fn probe_f3_u32x8_cmp_bitmask(a: u32x8, b: u32x8) -> (u8, u32x8) {
    let mask: i32x8 = simd_eq(a, b);
    let bm: u8 = simd_bitmask(mask);
    let sel: u32x8 = simd_select_bitmask(bm, a, b);
    (bm, sel)
}

// Family 4: Float-to-int saturating (simd_as) vs unchecked (simd_cast)
#[no_mangle]
pub unsafe fn probe_f4_f32x8_casts(v: f32x8) -> (i32x8, i32x8) {
    let safe_sat: i32x8 = simd_as(v);
    let raw_ub: i32x8 = simd_cast(v);
    (safe_sat, raw_ub)
}

// Family 5: Cross-half shuffle (u32x8 -> u32x8)
#[no_mangle]
pub unsafe fn probe_f5_u32x8_shuffle(a: u32x8, b: u32x8) -> u32x8 {
    const IDX: u32x8 = u32x8([0, 8, 4, 12, 2, 10, 6, 14]);
    simd_shuffle(a, b, IDX)
}

// Family 6: Horizontal reductions (ordered vs unordered)
#[no_mangle]
pub unsafe fn probe_f6_f32x8_reduce(v: f32x8, acc: f32) -> (f32, f32) {
    let ord = simd_reduce_add_ordered(v, acc);
    let unord = simd_reduce_add_unordered(v);
    (ord, unord)
}

// Family 8: Floating-point math intrinsics (fma + fsqrt)
#[no_mangle]
pub unsafe fn probe_f8_f32x8_math(a: f32x8, b: f32x8, c: f32x8) -> f32x8 {
    let m = simd_fma(a, b, c);
    simd_fsqrt(m)
}
