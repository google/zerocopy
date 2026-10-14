#![feature(portable_simd)]
use std::simd::Simd;
use std::arch::aarch64::{vaddq_u32, vld1q_u32, vst1q_u32};

#[target_feature(enable = "neon")]
unsafe fn intrinsic_add(a: &[u32; 4], b: &[u32; 4]) -> [u32; 4] {
    let mut out = [0u32; 4];
    // Each array has four initialized u32 elements; the arrays live throughout
    // these loads/stores. The caller checks the actual target feature.
    let va = unsafe { vld1q_u32(a.as_ptr()) };
    let vb = unsafe { vld1q_u32(b.as_ptr()) };
    let vc = vaddq_u32(va, vb);
    unsafe { vst1q_u32(out.as_mut_ptr(), vc) };
    out
}

#[repr(C)]
union Word { word: u32, bytes: [u8; 4] }

fn main() {
    let neon = std::arch::is_aarch64_feature_detected!("neon");
    assert!(neon);
    let values = [0, 1, 255, 256, 0x7fff_ffff, 0x8000_0000, u32::MAX-1, u32::MAX];
    let mut cases = 0;
    for &x in &values { for &y in &values {
        let a = [x, y, x, u32::MAX];
        let b = [y, x, 1, 1];
        let scalar = std::array::from_fn(|i| a[i].wrapping_add(b[i]));
        let portable = (Simd::<u32,4>::from_array(a) + Simd::from_array(b)).to_array();
        let intrinsic = unsafe { intrinsic_add(&a, &b) };
        assert_eq!(portable, scalar);
        assert_eq!(intrinsic, scalar);
        cases += 1;
    }}
    assert_eq!(u32::MAX.checked_add(1), None);
    assert_eq!((Simd::<u32,4>::splat(u32::MAX) + Simd::splat(1)).to_array(), [0;4]);
    for &word in &values {
        // u32 and [u8;4] have no invalid initialized bit patterns. Both fields
        // start at offset zero, and all four bytes were initialized by word.
        let bytes = unsafe { Word { word }.bytes };
        assert_eq!(bytes, word.to_ne_bytes());
    }
    println!("neon={neon} checked_overflow=None portable_max_plus1=0 add_cases={cases} union_cases={} simd_size={} simd_align={} array_align={} union_size={} union_align={}",
        values.len(), std::mem::size_of::<Simd<u32,4>>(), std::mem::align_of::<Simd<u32,4>>(),
        std::mem::align_of::<[u32;4]>(), std::mem::size_of::<Word>(), std::mem::align_of::<Word>());
}
