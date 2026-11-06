// PROPOSED E33 fixed-width vector fixture. Compile-only, not executed.
// Feature acceptance and ABI shape have NOT been tested during preparation.
#![no_std]
#![feature(repr_simd, simd_ffi)]
#![allow(dead_code)]
#[repr(simd)]
#[derive(Clone, Copy)]
pub struct V4(pub [u32; 4]);
#[no_mangle]
#[inline(never)]
pub extern "C" fn abi_c_vector(x: V4) -> V4 { x }
#[no_mangle]
#[inline(never)]
pub extern "system" fn abi_system_vector(x: V4) -> V4 { x }
#[no_mangle]
#[inline(never)]
pub fn abi_rust_vector(x: V4) -> V4 { x }
