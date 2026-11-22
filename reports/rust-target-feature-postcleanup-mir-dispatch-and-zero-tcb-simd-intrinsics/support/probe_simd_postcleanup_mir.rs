#![allow(unused)]
use core::arch::x86_64::*;

#[target_feature(enable = "avx2")]
pub fn safe_tf_add(a: __m256i, b: __m256i) -> __m256i {
    _mm256_add_epi8(a, b)
}

#[target_feature(enable = "avx2")]
pub fn safe_tf_caller(p: *const __m256i) -> __m256i {
    let a = unsafe { _mm256_loadu_si256(p) };
    let b = unsafe { _mm256_load_si256(p) };
    safe_tf_add(a, _mm256_shuffle_epi8(a, b))
}

#[target_feature(enable = "avx512f,avx512bw,avx512vbmi,avx512vbmi2")]
pub fn avx512_ops(mask: __mmask64, idx: __m512i, v: __m512i) -> __m512i {
    let e = _mm512_maskz_expand_epi8(mask, v);
    _mm512_permutexvar_epi8(idx, e)
}

pub fn dispatch_entry(p: *const __m256i) -> bool {
    if std::arch::is_x86_feature_detected!("avx2") {
        let _ = unsafe { safe_tf_caller(p) };
        true
    } else {
        false
    }
}
