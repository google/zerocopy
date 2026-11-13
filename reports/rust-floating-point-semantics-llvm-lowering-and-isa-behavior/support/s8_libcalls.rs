#![feature(f16, f128, core_intrinsics)]
#![allow(internal_features)]
#![no_std]

use core::intrinsics::*;

#[no_mangle] pub fn f16_add(a: f16, b: f16) -> f16 { a + b }
#[no_mangle] pub fn f16_mul(a: f16, b: f16) -> f16 { a * b }
#[no_mangle] pub fn f16_div(a: f16, b: f16) -> f16 { a / b }
#[no_mangle] pub fn f16_rem(a: f16, b: f16) -> f16 { a % b }
#[no_mangle] pub fn f16_fma(a: f16, b: f16, c: f16) -> f16 { fmaf16(a, b, c) }
#[no_mangle] pub fn f16_to_f32(a: f16) -> f32 { a as f32 }
#[no_mangle] pub fn f32_to_f16(a: f32) -> f16 { a as f16 }

#[no_mangle] pub fn f32_rem(a: f32, b: f32) -> f32 { a % b }
#[no_mangle] pub fn f32_fma(a: f32, b: f32, c: f32) -> f32 { fmaf32(a, b, c) }
#[no_mangle] pub fn f32_powi(a: f32, n: i32) -> f32 { powif32(a, n) }
#[no_mangle] pub fn f32_sin(a: f32) -> f32 { sinf32(a) }
#[no_mangle] pub fn f32_minimum(a: f32, b: f32) -> f32 { minimumf32(a, b) }
#[no_mangle] pub fn f32_minnum(a: f32, b: f32) -> f32 { minimum_number_nsz_f32(a, b) }
#[no_mangle] pub fn f32_to_u128(a: f32) -> u128 { a as u128 }
#[no_mangle] pub fn u128_to_f32(a: u128) -> f32 { a as f32 }

#[no_mangle] pub fn f64_rem(a: f64, b: f64) -> f64 { a % b }
#[no_mangle] pub fn f64_fma(a: f64, b: f64, c: f64) -> f64 { fmaf64(a, b, c) }
#[no_mangle] pub fn f64_powi(a: f64, n: i32) -> f64 { powif64(a, n) }
#[no_mangle] pub fn f64_sin(a: f64) -> f64 { sinf64(a) }
#[no_mangle] pub fn f64_minimum(a: f64, b: f64) -> f64 { minimumf64(a, b) }
#[no_mangle] pub fn f64_minnum(a: f64, b: f64) -> f64 { minimum_number_nsz_f64(a, b) }
#[no_mangle] pub fn f64_to_u128(a: f64) -> u128 { a as u128 }
#[no_mangle] pub fn u128_to_f64(a: u128) -> f64 { a as f64 }

#[no_mangle] pub fn f128_add(a: f128, b: f128) -> f128 { a + b }
#[no_mangle] pub fn f128_mul(a: f128, b: f128) -> f128 { a * b }
#[no_mangle] pub fn f128_div(a: f128, b: f128) -> f128 { a / b }
#[no_mangle] pub fn f128_rem(a: f128, b: f128) -> f128 { a % b }
#[no_mangle] pub fn f128_fma(a: f128, b: f128, c: f128) -> f128 { fmaf128(a, b, c) }
