#![feature(repr_simd)]
#[repr(simd)]
#[derive(Clone, Copy)]
pub struct Simd256([u64; 4]);
#[target_feature(enable = "avx2")]
pub unsafe extern "C" fn callee_takes_ymm_c(v: Simd256) -> Simd256 { v }

pub fn caller_without_avx(v: Simd256) -> Simd256 {
    unsafe { callee_takes_ymm_c(v) }
}
