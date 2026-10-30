// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![crate_type = "lib"]
#![cfg_attr(feature_simd, feature(repr_simd))]
#![cfg_attr(feature_trivial_bounds, feature(trivial_bounds))]

pub struct Big<T>([T; usize::MAX / 2]);

pub fn size_of_big<T>() -> usize {
    core::mem::size_of::<Big<T>>()
}

#[cfg(call_size_overflow)]
pub fn trigger_size_overflow() -> usize {
    size_of_big::<u32>()
}

#[cfg(feature_simd)]
#[repr(simd)]
pub struct SimdArr<T, const N: usize>([T; N]);

#[cfg(feature_simd)]
pub fn touch_simd<T, const N: usize>(x: SimdArr<T, N>) -> SimdArr<T, N> {
    x
}

#[cfg(all(feature_simd, simd_zero))]
pub fn trigger_simd_zero(x: SimdArr<u32, 0>) -> SimdArr<u32, 0> {
    touch_simd::<u32, 0>(x)
}

#[cfg(all(feature_simd, simd_too_many))]
pub fn trigger_simd_too_many(x: SimdArr<u32, 65536>) -> SimdArr<u32, 65536> {
    touch_simd::<u32, 65536>(x)
}

#[cfg(all(feature_simd, simd_non_primitive))]
pub fn trigger_simd_non_primitive(x: SimdArr<(), 4>) -> SimdArr<(), 4> {
    touch_simd::<(), 4>(x)
}

pub fn poly_rec<T>(n: usize) -> usize {
    if n == 0 {
        core::mem::size_of::<T>()
    } else {
        poly_rec::<(T,)>(n - 1)
    }
}

#[cfg(call_poly_rec)]
pub fn trigger_poly_rec() -> usize {
    poly_rec::<u8>(0)
}

#[cfg(feature_trivial_bounds)]
pub trait Impossible {}

#[cfg(feature_trivial_bounds)]
pub fn impossible_fn()
where
    u32: Impossible,
{
    const {
        panic!("impossible clause body");
    }
}
