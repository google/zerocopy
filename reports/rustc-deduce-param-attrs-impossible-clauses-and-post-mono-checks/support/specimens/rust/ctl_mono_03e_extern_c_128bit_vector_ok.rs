#![feature(repr_simd)]
#[repr(simd)]
#[derive(Clone, Copy)]
pub struct Simd128([u64; 2]);
#[inline(never)]
pub extern "C" fn callee_takes_xmm_c(v: Simd128) -> Simd128 { v }

pub fn caller_baseline(v: Simd128) -> Simd128 {
    callee_takes_xmm_c(v)
}
