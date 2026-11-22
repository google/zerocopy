#![feature(repr_simd)]
#[repr(simd)]
#[derive(Clone, Copy)]
pub struct Simd256([u64; 4]);
pub extern "C" fn definition_takes_ymm_c(v: Simd256) -> Simd256 { v }
