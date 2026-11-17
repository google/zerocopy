// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Wide x86-64 Ice Lake SIMD probe:
//! 1. L1 (32 KiB) / L2 (256 KiB) / L3 (2 MiB) cache-tier throughput across
//!    safe 64-lane `u16 -> u32` (`+prefer-256-bit` vs `-prefer-256-bit`) and
//!    AVX-512 VNNI (`vpdpbusd` + `vpsadbw`).
//! 2. `k = 1, 2, 4` accumulator ILP scaling under AVX-512 VNNI.
//! 3. IFMA52 (`vpmadd52luq`) generation in trailing `s1_32`/`s2_32` weights.
//! 4. Signed `i32` wrap hazard inside `_mm512_reduce_add_epi32(v_s2) as u64`.
//! 5. SSSE3 `pshufb` overlap period smearing (`dist = 1..=15`) vs scalar copy.
//! 6. BMI2 `shrx` / `bzhi` instruction emission in bitreader unpacking.

#![allow(dead_code)]
use std::arch::x86_64::*;
use std::hint::black_box;
use std::time::Instant;

const MOD_ADLER: u32 = 65521;

#[inline(always)]
fn adler_reduce_u32(v: u32) -> u32 {
    let t1 = (v & 0xffff) + ((v >> 16) * 15);
    let t2 = (t1 & 0xffff) + ((t1 >> 16) * 15);
    if t2 >= MOD_ADLER { t2 - MOD_ADLER } else { t2 }
}

#[inline(always)]
fn adler_reduce_u64(v: u64) -> u32 {
    let lo = v & 0xffff;
    let mid = (v >> 16) & 0xffff;
    let hi = v >> 32;
    adler_reduce_u32((lo + mid * 15 + hi * 225) as u32)
}

#[no_mangle]
#[inline(never)]
pub fn adler_serial_1lane(data: &[u8]) -> u32 {
    let (mut a, mut b) = (1u32, 0u32);
    let mut off = 0usize;
    while off < data.len() {
        let end = (off + 5552).min(data.len());
        while off < end {
            a += data[off] as u32;
            b += a;
            off += 1;
        }
        a %= MOD_ADLER;
        b %= MOD_ADLER;
    }
    (b << 16) | a
}

#[no_mangle]
#[inline(never)]
pub fn adler_safe_64lane_u16_16(data: &[u8]) -> u32 {
    let (mut s1, mut s2) = (1u32, 0u32);
    let (super_blocks, tail_after_super) = data.as_chunks::<1024>();
    for big in super_blocks.chunks(347) {
        let mut s1_32 = [0u32; 64];
        let mut s2_32 = [0u32; 64];
        for sb in big {
            let mut s1_16 = [0u16; 64];
            let mut s2_16 = [0u16; 64];
            let (blocks, _) = sb.as_chunks::<64>();
            for blk in blocks {
                for i in 0..64 {
                    s2_16[i] += s1_16[i];
                    s1_16[i] += blk[i] as u16;
                }
            }
            for i in 0..64 {
                s2_32[i] = (s2_32[i] + (s1_32[i] << 4)) + (s2_16[i] as u32);
                s1_32[i] += s1_16[i] as u32;
            }
        }
        let num_bytes = (big.len() * 1024) as u64;
        let (mut sum_s1, mut sum_s2, mut weighted_s1) = (0u64, 0u64, 0u64);
        for i in 0..64 {
            let a = s1_32[i] as u64;
            sum_s1 += a;
            sum_s2 += s2_32[i] as u64;
            weighted_s1 += ((64 - i) as u64) * a;
        }
        s2 = adler_reduce_u64((s2 as u64) + (s1 as u64) * num_bytes + (sum_s2 << 6) + weighted_s1);
        s1 = adler_reduce_u64((s1 as u64) + sum_s1);
    }
    let (rem_blocks, scalar_tail) = tail_after_super.as_chunks::<64>();
    if !rem_blocks.is_empty() {
        let mut s1_16 = [0u16; 64];
        let mut s2_16 = [0u16; 64];
        for blk in rem_blocks {
            for i in 0..64 {
                s2_16[i] += s1_16[i];
                s1_16[i] += blk[i] as u16;
            }
        }
        let num_bytes = (rem_blocks.len() * 64) as u64;
        let (mut sum_s1, mut sum_s2, mut weighted_s1) = (0u64, 0u64, 0u64);
        for i in 0..64 {
            let a = s1_16[i] as u64;
            sum_s1 += a;
            sum_s2 += s2_16[i] as u64;
            weighted_s1 += ((64 - i) as u64) * a;
        }
        s2 = adler_reduce_u64((s2 as u64) + (s1 as u64) * num_bytes + (sum_s2 << 6) + weighted_s1);
        s1 = adler_reduce_u64((s1 as u64) + sum_s1);
    }
    for &b in scalar_tail {
        s1 += b as u32;
        if s1 >= MOD_ADLER { s1 -= MOD_ADLER; }
        s2 += s1;
        if s2 >= MOD_ADLER { s2 -= MOD_ADLER; }
    }
    (s2 << 16) | s1
}

#[no_mangle]
#[inline(never)]
pub fn adler_reduce_weights_only(s1_32: &[u32; 64], s2_32: &[u32; 64]) -> (u32, u32) {
    let (mut a, mut b) = (1u64, 0u64);
    for k in 0..64 {
        a += u64::from(s1_32[k]);
        b += 64 * u64::from(s2_32[k]) + (64 - k as u64) * u64::from(s1_32[k]);
    }
    ((a % 65521) as u32, (b % 65521) as u32)
}

#[no_mangle]
#[inline(never)]
pub fn bmi2_shrx_bzhi(mut bb: u64, tbl: &[u32; 2048], n: usize) -> u64 {
    let mut acc = 0u64;
    for _ in 0..n {
        let e = tbl[(bb as usize) & 2047];
        bb = bb.wrapping_shr(e & 63);
        let extra = (e >> 8) & 15;
        let bits = (bb as u32) & ((1u32 << extra) - 1);
        acc = acc.wrapping_add(bits as u64);
        bb ^= (e as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
    acc
}

#[target_feature(enable = "avx512vnni,avx512bw,avx512f")]
unsafe fn adler_unsafe_vnni_128b(data: &[u8]) -> u32 {
    let (mut s1, mut s2) = (1u64, 0u64);
    let mut ptr = data.as_ptr();
    let mut rem_blocks = data.len() >> 7;
    static WEIGHTS: [i8; 64] = [
        64,63,62,61,60,59,58,57,56,55,54,53,52,51,50,49,
        48,47,46,45,44,43,42,41,40,39,38,37,36,35,34,33,
        32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,
        16,15,14,13,12,11,10, 9, 8, 7, 6, 5, 4, 3, 2, 1,
    ];
    let zero = _mm512_setzero_si512();
    let w = _mm512_loadu_si512(WEIGHTS.as_ptr().cast());
    while rem_blocks > 0 {
        let chunk_blocks = rem_blocks.min(2048);
        rem_blocks -= chunk_blocks;
        let (mut s1_a, mut s1_b) = (zero, zero);
        let (mut prev_a, mut prev_b) = (zero, zero);
        let (mut dot_a, mut dot_b) = (zero, zero);
        for _ in 0..chunk_blocks {
            let v0 = _mm512_loadu_si512(ptr.cast());
            let v1 = _mm512_loadu_si512(ptr.add(64).cast());
            ptr = ptr.add(128);
            prev_a = _mm512_add_epi64(prev_a, s1_a);
            prev_b = _mm512_add_epi64(prev_b, s1_b);
            s1_a = _mm512_add_epi64(s1_a, _mm512_sad_epu8(v0, zero));
            s1_b = _mm512_add_epi64(s1_b, _mm512_sad_epu8(v1, zero));
            dot_a = _mm512_dpbusd_epi32(dot_a, v0, w);
            dot_b = _mm512_dpbusd_epi32(dot_b, v1, w);
        }
        let sum_a = _mm512_reduce_add_epi64(s1_a) as u64;
        let sum_b = _mm512_reduce_add_epi64(s1_b) as u64;
        let prev_sum = _mm512_reduce_add_epi64(_mm512_add_epi64(prev_a, prev_b)) as u64;
        let lo_a = _mm512_cvtepu32_epi64(_mm512_castsi512_si256(dot_a));
        let hi_a = _mm512_cvtepu32_epi64(_mm512_extracti64x4_epi64::<1>(dot_a));
        let lo_b = _mm512_cvtepu32_epi64(_mm512_castsi512_si256(dot_b));
        let hi_b = _mm512_cvtepu32_epi64(_mm512_extracti64x4_epi64::<1>(dot_b));
        let dot_sum = _mm512_reduce_add_epi64(_mm512_add_epi64(
            _mm512_add_epi64(lo_a, hi_a),
            _mm512_add_epi64(lo_b, hi_b),
        )) as u64;
        let bytes = (chunk_blocks as u64) * 128;
        s2 = (s2 + s1 * bytes + 128 * prev_sum + 64 * sum_a + dot_sum) % (MOD_ADLER as u64);
        s1 = (s1 + sum_a + sum_b) % (MOD_ADLER as u64);
    }
    let mut idx = (data.len() >> 7) << 7;
    let (mut s1_32, mut s2_32) = (s1 as u32, s2 as u32);
    while idx < data.len() {
        s1_32 += data[idx] as u32;
        if s1_32 >= MOD_ADLER { s1_32 -= MOD_ADLER; }
        s2_32 += s1_32;
        if s2_32 >= MOD_ADLER { s2_32 -= MOD_ADLER; }
        idx += 1;
    }
    (s2_32 << 16) | s1_32
}

#[target_feature(enable = "avx512vnni,avx512bw,avx512f")]
unsafe fn adler_unsafe_vnni_signed_bug(data: &[u8]) -> u32 {
    let (mut s1, mut s2) = (1u64, 0u64);
    let mut ptr = data.as_ptr();
    let mut rem_blocks = data.len() >> 6;
    static WEIGHTS: [i8; 64] = [
        64,63,62,61,60,59,58,57,56,55,54,53,52,51,50,49,
        48,47,46,45,44,43,42,41,40,39,38,37,36,35,34,33,
        32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,
        16,15,14,13,12,11,10, 9, 8, 7, 6, 5, 4, 3, 2, 1,
    ];
    let zero = _mm512_setzero_si512();
    let w = _mm512_loadu_si512(WEIGHTS.as_ptr().cast());
    while rem_blocks > 0 {
        let chunk_blocks = rem_blocks.min(5552);
        rem_blocks -= chunk_blocks;
        let (mut v_s1, mut v_s1_sum, mut v_s2) = (zero, zero, zero);
        for _ in 0..chunk_blocks {
            let va = _mm512_loadu_si512(ptr.cast());
            ptr = ptr.add(64);
            v_s1_sum = _mm512_add_epi64(v_s1_sum, v_s1);
            v_s1 = _mm512_add_epi64(v_s1, _mm512_sad_epu8(va, zero));
            v_s2 = _mm512_dpbusd_epi32(v_s2, va, w);
        }
        // _mm512_reduce_add_epi32 returns i32: sign-extends when unsigned sum >= 2^31!
        let s2_weighted = _mm512_reduce_add_epi32(v_s2) as u64;
        let s1_delta = _mm512_reduce_add_epi64(v_s1) as u64;
        let s1_prefix = _mm512_reduce_add_epi64(v_s1_sum) as u64;
        let bytes = (chunk_blocks as u64) * 64;
        s2 = s2.wrapping_add(s1 * bytes).wrapping_add(64 * s1_prefix).wrapping_add(s2_weighted)
            % (MOD_ADLER as u64);
        s1 = (s1 + s1_delta) % (MOD_ADLER as u64);
    }
    let mut idx = (data.len() >> 6) << 6;
    let (mut s1_32, mut s2_32) = (s1 as u32, s2 as u32);
    while idx < data.len() {
        s1_32 += data[idx] as u32;
        if s1_32 >= MOD_ADLER { s1_32 -= MOD_ADLER; }
        s2_32 += s1_32;
        if s2_32 >= MOD_ADLER { s2_32 -= MOD_ADLER; }
        idx += 1;
    }
    (s2_32 << 16) | s1_32
}

#[target_feature(enable = "avx512bw,avx512vnni")]
unsafe fn vnni_kstream(bytes: &[u8], k: usize) -> u32 {
    let w = _mm512_set_epi8(
        1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,
        17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,
        33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,
        49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,
    );
    let zero = _mm512_setzero_si512();
    let ptr = bytes.as_ptr();
    let n = bytes.len();
    match k {
        1 => {
            let (mut s1, mut s2, mut p) = (zero, zero, zero);
            let mut i = 0;
            while i + 64 <= n {
                let x = _mm512_loadu_si512(ptr.add(i).cast());
                p = _mm512_add_epi64(p, s1);
                s1 = _mm512_add_epi64(s1, _mm512_sad_epu8(x, zero));
                s2 = _mm512_dpbusd_epi32(s2, x, w);
                i += 64;
            }
            let mut arr = [0u32; 16];
            _mm512_storeu_si512(arr.as_mut_ptr().cast(), _mm512_add_epi64(p, _mm512_add_epi64(s1, s2)));
            arr[0].wrapping_add(arr[4]).wrapping_add(arr[8])
        }
        2 => {
            let (mut s1a, mut s1b, mut s2a, mut s2b, mut pa, mut pb) = (zero, zero, zero, zero, zero, zero);
            let mut i = 0;
            while i + 128 <= n {
                let xa = _mm512_loadu_si512(ptr.add(i).cast());
                let xb = _mm512_loadu_si512(ptr.add(i + 64).cast());
                pa = _mm512_add_epi64(pa, s1a);
                pb = _mm512_add_epi64(pb, s1b);
                s1a = _mm512_add_epi64(s1a, _mm512_sad_epu8(xa, zero));
                s1b = _mm512_add_epi64(s1b, _mm512_sad_epu8(xb, zero));
                s2a = _mm512_dpbusd_epi32(s2a, xa, w);
                s2b = _mm512_dpbusd_epi32(s2b, xb, w);
                i += 128;
            }
            let mut arr = [0u32; 16];
            let sum = _mm512_add_epi64(
                _mm512_add_epi64(pa, pb),
                _mm512_add_epi64(_mm512_add_epi64(s1a, s1b), _mm512_add_epi64(s2a, s2b)),
            );
            _mm512_storeu_si512(arr.as_mut_ptr().cast(), sum);
            arr[0].wrapping_add(arr[4]).wrapping_add(arr[8])
        }
        _ => {
            let (mut s1a, mut s1b, mut s1c, mut s1d) = (zero, zero, zero, zero);
            let (mut s2a, mut s2b, mut s2c, mut s2d) = (zero, zero, zero, zero);
            let (mut pa, mut pb, mut pc, mut pd) = (zero, zero, zero, zero);
            let mut i = 0;
            while i + 256 <= n {
                let xa = _mm512_loadu_si512(ptr.add(i).cast());
                let xb = _mm512_loadu_si512(ptr.add(i + 64).cast());
                let xc = _mm512_loadu_si512(ptr.add(i + 128).cast());
                let xd = _mm512_loadu_si512(ptr.add(i + 192).cast());
                pa = _mm512_add_epi64(pa, s1a); pb = _mm512_add_epi64(pb, s1b);
                pc = _mm512_add_epi64(pc, s1c); pd = _mm512_add_epi64(pd, s1d);
                s1a = _mm512_add_epi64(s1a, _mm512_sad_epu8(xa, zero));
                s1b = _mm512_add_epi64(s1b, _mm512_sad_epu8(xb, zero));
                s1c = _mm512_add_epi64(s1c, _mm512_sad_epu8(xc, zero));
                s1d = _mm512_add_epi64(s1d, _mm512_sad_epu8(xd, zero));
                s2a = _mm512_dpbusd_epi32(s2a, xa, w);
                s2b = _mm512_dpbusd_epi32(s2b, xb, w);
                s2c = _mm512_dpbusd_epi32(s2c, xc, w);
                s2d = _mm512_dpbusd_epi32(s2d, xd, w);
                i += 256;
            }
            let mut arr = [0u32; 16];
            let sum = _mm512_add_epi64(
                _mm512_add_epi64(_mm512_add_epi64(pa, pb), _mm512_add_epi64(pc, pd)),
                _mm512_add_epi64(
                    _mm512_add_epi64(_mm512_add_epi64(s1a, s1b), _mm512_add_epi64(s1c, s1d)),
                    _mm512_add_epi64(_mm512_add_epi64(s2a, s2b), _mm512_add_epi64(s2c, s2d)),
                ),
            );
            _mm512_storeu_si512(arr.as_mut_ptr().cast(), sum);
            arr[0].wrapping_add(arr[4]).wrapping_add(arr[8])
        }
    }
}

/// SSSE3 `_mm_shuffle_epi8` period smearing over `[out_pos - 16 .. out_pos)`
/// for overlap `1 <= dist < 16`. Safe w.r.t. initialized prefix once `out_pos >= 16`.
#[target_feature(enable = "ssse3")]
unsafe fn pshufb_smear_16(buf: &mut [u8], out_pos: usize, dist: usize) {
    assert!(out_pos >= 16 && (1..16).contains(&dist) && out_pos + 16 <= buf.len());
    let mut mask_bytes = [0u8; 16];
    let start = 16 - dist;
    for (i, slot) in mask_bytes.iter_mut().enumerate() {
        *slot = (start + (i % dist)) as u8;
    }
    let src = _mm_loadu_si128(buf.as_ptr().add(out_pos - 16).cast());
    let mask = _mm_loadu_si128(mask_bytes.as_ptr().cast());
    let smeared = _mm_shuffle_epi8(src, mask);
    _mm_storeu_si128(buf.as_mut_ptr().add(out_pos).cast(), smeared);
}

fn verify_pshufb_periods() {
    for dist in 1..16 {
        let mut ref_buf = vec![0u8; 64];
        let mut simd_buf = vec![0u8; 64];
        for i in 0..16 {
            let b = ((i * 29 + 7) & 0xFF) as u8;
            ref_buf[i] = b;
            simd_buf[i] = b;
        }
        for k in 0..16 {
            ref_buf[16 + k] = ref_buf[16 + k - dist];
        }
        unsafe { pshufb_smear_16(&mut simd_buf, 16, dist) };
        assert_eq!(simd_buf[16..32], ref_buf[16..32], "pshufb mismatch dist={dist}");
    }
}

fn bench_gbps<F: FnMut(&[u8]) -> u32>(data: &[u8], expected: u32, iters: usize, reps: usize, mut f: F) -> f64 {
    for _ in 0..3 {
        assert_eq!(black_box(f(black_box(data))), expected);
    }
    let mut ts = Vec::with_capacity(iters);
    for _ in 0..iters {
        let t0 = Instant::now();
        let mut x = 0u32;
        for _ in 0..reps {
            x ^= black_box(f(black_box(data)));
        }
        black_box(x);
        ts.push(t0.elapsed().as_secs_f64());
    }
    ts.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (reps as f64 * data.len() as f64 / 1e9) / ts[iters / 2]
}

fn main() {
    verify_pshufb_periods();
    println!("PSHUFB_1_TO_15=PASS");

    for (label, sz, reps) in [
        ("32KiB_L1", 32 * 1024usize, 4000),
        ("256KiB_L2", 256 * 1024usize, 500),
        ("2MiB_L3", 2048 * 1024usize, 60),
    ] {
        let data: Vec<u8> = (0..sz).map(|i| ((i * 131 + 17) & 0xff) as u8).collect();
        let exp = adler_serial_1lane(&data);
        let scalar_g = bench_gbps(&data, exp, 15, (reps / 4).max(4), adler_serial_1lane);
        let safe64_g = bench_gbps(&data, exp, 15, reps, adler_safe_64lane_u16_16);
        let vnni_g = bench_gbps(&data, exp, 15, reps, |d| unsafe { adler_unsafe_vnni_128b(d) });
        println!("TIER {label} serial={scalar_g:.2} safe64={safe64_g:.2} vnni_2stream={vnni_g:.2}");
        for k in [1usize, 2, 4] {
            let mut ts = Vec::with_capacity(15);
            for _ in 0..3 {
                black_box(unsafe { vnni_kstream(&data, k) });
            }
            for _ in 0..15 {
                let t0 = Instant::now();
                let mut acc = 0u32;
                for _ in 0..reps {
                    acc ^= unsafe { vnni_kstream(black_box(&data), k) };
                }
                black_box(acc);
                ts.push(t0.elapsed().as_secs_f64());
            }
            ts.sort_by(|a, b| a.partial_cmp(b).unwrap());
            let gbps = (reps as f64 * sz as f64 / 1e9) / ts[7];
            println!("KSTREAM {label} k={k} {gbps:.2}");
        }
    }

    let ff_5552 = vec![0xFFu8; 5552 * 64];
    let exp_ff = adler_serial_1lane(&ff_5552);
    let ok_ff = unsafe { adler_unsafe_vnni_128b(&ff_5552) };
    let bug_ff = unsafe { adler_unsafe_vnni_signed_bug(&ff_5552) };
    assert_eq!(ok_ff, exp_ff);
    assert_ne!(bug_ff, exp_ff);
    println!("SIGNED_I32_BUG expected=0x{exp_ff:08x} ok=0x{ok_ff:08x} signed_bug=0x{bug_ff:08x}");
}
