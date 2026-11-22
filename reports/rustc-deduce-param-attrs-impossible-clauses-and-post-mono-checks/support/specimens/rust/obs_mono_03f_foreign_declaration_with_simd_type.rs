#![feature(repr_simd)]
#[repr(simd)]
#[derive(Clone, Copy)]
pub struct Simd256([u64; 4]);
extern "C" {
    fn foreign_takes_ymm_c(v: Simd256) -> u64;
}
pub fn caller_without_avx(v: Simd256) -> u64 {
    unsafe { foreign_takes_ymm_c(v) }
}
