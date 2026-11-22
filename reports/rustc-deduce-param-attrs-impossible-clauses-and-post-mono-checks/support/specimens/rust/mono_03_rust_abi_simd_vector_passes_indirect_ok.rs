#![feature(repr_simd)]
#[repr(simd)]
#[derive(Clone, Copy)]
pub struct Simd256([u64; 4]);
#[inline(never)]
pub fn callee_takes_ymm_rust(v: Simd256) -> Simd256 {
    v
}
pub fn caller_without_avx(v: Simd256) -> Simd256 {
    callee_takes_ymm_rust(v)
}
