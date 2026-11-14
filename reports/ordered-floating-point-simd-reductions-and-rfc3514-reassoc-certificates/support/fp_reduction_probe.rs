// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]

use core::intrinsics::{fadd_algebraic, fadd_fast, fmaf32, fmul_algebraic, fmul_fast};

// 1. Strict IEEE-754 f32 sum
#[no_mangle]
pub fn k01_sum_f32_strict(xs: &[f32]) -> f32 {
    xs.iter().fold(0.0f32, |acc, &x| acc + x)
}

// 2. Fast-math (RFC 3514 fadd_fast) f32 sum
#[no_mangle]
pub fn k02_sum_f32_fast(xs: &[f32]) -> f32 {
    xs.iter().fold(0.0f32, |acc, &x| unsafe { fadd_fast(acc, x) })
}

// 3. Strict IEEE-754 f64 sum
#[no_mangle]
pub fn k03_sum_f64_strict(xs: &[f64]) -> f64 {
    xs.iter().fold(0.0f64, |acc, &x| acc + x)
}

// 4. Fast-math (RFC 3514 fadd_fast) f64 sum
#[no_mangle]
pub fn k04_sum_f64_fast(xs: &[f64]) -> f64 {
    xs.iter().fold(0.0f64, |acc, &x| unsafe { fadd_fast(acc, x) })
}

// 5. Strict IEEE-754 f32 dot product
#[no_mangle]
pub fn k05_dot_f32_strict(xs: &[f32], ys: &[f32]) -> f32 {
    let n = xs.len().min(ys.len());
    let mut acc = 0.0f32;
    for i in 0..n {
        acc += xs[i] * ys[i];
    }
    acc
}

// 6. Fast-math (fadd_fast + fmul_fast -> FMA + reassoc) f32 dot product
#[no_mangle]
pub fn k06_dot_f32_fast(xs: &[f32], ys: &[f32]) -> f32 {
    let n = xs.len().min(ys.len());
    let mut acc = 0.0f32;
    for i in 0..n {
        unsafe {
            acc = fadd_fast(acc, fmul_fast(xs[i], ys[i]));
        }
    }
    acc
}

// 7. Strict IEEE-754 f64 dot product
#[no_mangle]
pub fn k07_dot_f64_strict(xs: &[f64], ys: &[f64]) -> f64 {
    let n = xs.len().min(ys.len());
    let mut acc = 0.0f64;
    for i in 0..n {
        acc += xs[i] * ys[i];
    }
    acc
}

// 8. Fast-math f64 dot product
#[no_mangle]
pub fn k08_dot_f64_fast(xs: &[f64], ys: &[f64]) -> f64 {
    let n = xs.len().min(ys.len());
    let mut acc = 0.0f64;
    for i in 0..n {
        unsafe {
            acc = fadd_fast(acc, fmul_fast(xs[i], ys[i]));
        }
    }
    acc
}

// 9. Strict Kahan compensated summation (f64)
#[no_mangle]
pub fn k09_kahan_f64_strict(xs: &[f64]) -> f64 {
    let mut sum = 0.0f64;
    let mut c = 0.0f64;
    for &x in xs {
        let y = x - c;
        let t = sum + y;
        c = (t - sum) - y;
        sum = t;
    }
    sum
}

// 10. Explicit 4-lane pairwise sum (f64)
#[no_mangle]
pub fn k10_pairwise4_f64_strict(xs: &[f64]) -> f64 {
    let mut acc = [0.0f64; 4];
    let chunks = xs.chunks_exact(4);
    let rem = chunks.remainder();
    for ch in chunks {
        acc[0] += ch[0];
        acc[1] += ch[1];
        acc[2] += ch[2];
        acc[3] += ch[3];
    }
    let mut total = (acc[0] + acc[1]) + (acc[2] + acc[3]);
    for &r in rem {
        total += r;
    }
    total
}

// 11. Strict L2 squared norm (f32)
#[no_mangle]
pub fn k11_l2norm_sq_f32_strict(xs: &[f32]) -> f32 {
    xs.iter().fold(0.0f32, |acc, &x| acc + x * x)
}

// 12. Algebraic L2 squared norm (f32, safe fadd_algebraic + fmul_algebraic)
#[no_mangle]
pub fn k12_l2norm_sq_f32_algebraic(xs: &[f32]) -> f32 {
    xs.iter().fold(0.0f32, |acc, &x| fadd_algebraic(acc, fmul_algebraic(x, x)))
}

// 13. Strict cosine similarity numerator & norms (f32)
#[no_mangle]
pub fn k13_cosine_f32_strict(xs: &[f32], ys: &[f32]) -> f32 {
    let n = xs.len().min(ys.len());
    let mut dot = 0.0f32;
    for i in 0..n {
        dot = unsafe { fmaf32(xs[i], ys[i], dot) };
    }
    dot
}

// 14. Fast-math cosine similarity numerator (f32)
#[no_mangle]
pub fn k14_cosine_f32_fast(xs: &[f32], ys: &[f32]) -> f32 {
    let n = xs.len().min(ys.len());
    let mut dot = 0.0f32;
    for i in 0..n {
        unsafe {
            dot = fadd_fast(dot, fmul_fast(xs[i], ys[i]));
        }
    }
    dot
}

// 15. Polynomial Horner evaluation across slice (f64)
#[no_mangle]
pub fn k15_horner_f64_strict(coeffs: &[f64], x: f64) -> f64 {
    coeffs.iter().fold(0.0f64, |acc, &c| acc * x + c)
}

// 16. Softmax shifted-exp denominator reduction (f32, fadd_fast)
#[no_mangle]
pub fn k16_softmax_denom_f32_fast(exps: &[f32]) -> f32 {
    exps.iter().fold(0.0f32, |acc, &v| unsafe { fadd_fast(acc, v.max(0.0)) })
}
