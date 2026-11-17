// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Safe Rust bounds-check elimination (BCE), SLP/AVX2 vectorization, cold-error
//! outlining, double-literal fusion, and glibc mmap zero-page allocation probes.

#![allow(dead_code)]
use std::hint::black_box;
use std::time::Instant;

const MOD_ADLER: u32 = 65521;

// --- 1. Loop Indexing & Masking BCE Kernels (inspected in emitted asm) ---

#[no_mangle]
#[inline(never)]
pub fn bce_while_index4(s: &[u8]) -> u32 {
    let mut i = 0usize;
    let mut acc = 0u32;
    while i + 4 <= s.len() {
        let w = u32::from_le_bytes([s[i], s[i + 1], s[i + 2], s[i + 3]]);
        acc = acc.wrapping_add(w);
        i += 4;
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub fn bce_chunks_exact4(s: &[u8]) -> u32 {
    let mut acc = 0u32;
    for c in s.chunks_exact(4) {
        let w = u32::from_le_bytes([c[0], c[1], c[2], c[3]]);
        acc = acc.wrapping_add(w);
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub fn bce_as_chunks4(s: &[u8]) -> u32 {
    let mut acc = 0u32;
    let (chunks, _) = s.as_chunks::<4>();
    for c in chunks {
        acc = acc.wrapping_add(u32::from_le_bytes(*c));
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub fn bce_slice_mask(tbl: &[u32], keys: &[usize]) -> u32 {
    let mut acc = 0u32;
    for &k in keys {
        acc ^= tbl[k & 2047];
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub fn bce_box_array_mask(tbl: &Box<[u32; 2048]>, keys: &[usize]) -> u32 {
    let mut acc = 0u32;
    for &k in keys {
        acc ^= tbl[k & 2047];
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub fn bce_ref_array_mask(tbl: &[u32; 2048], keys: &[usize]) -> u32 {
    let mut acc = 0u32;
    for &k in keys {
        acc ^= tbl[k & 2047];
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub fn bce_shifted_read4(s: &[u8], pos: usize, cands: &[usize]) -> u32 {
    let win = &s[..pos + 4];
    let cur = u32::from_le_bytes([win[pos], win[pos + 1], win[pos + 2], win[pos + 3]]);
    let mut hits = 0u32;
    for &c in cands {
        if c < pos {
            let v = u32::from_le_bytes([win[c], win[c + 1], win[c + 2], win[c + 3]]);
            if v == cur {
                hits += 1;
            }
        }
    }
    hits
}

#[no_mangle]
#[inline(never)]
pub fn bce_first_chunk4(s: &[u8], pos: usize, cands: &[usize]) -> u32 {
    let Some(cur_arr) = s.get(pos..).and_then(|r| r.first_chunk::<4>()) else {
        return 0;
    };
    let cur = u32::from_le_bytes(*cur_arr);
    let mut hits = 0u32;
    for &c in cands {
        if let Some(arr) = s.get(c..).and_then(|r| r.first_chunk::<4>()) {
            if u32::from_le_bytes(*arr) == cur {
                hits += 1;
            }
        }
    }
    hits
}

// --- 2. Safe Prefilter, Zipped-Slice DP, and 4-Way Adler-32 SLP Isolation ---

#[no_mangle]
#[inline(never)]
pub fn prefilter_1b_safe(src: &[u8], pos: usize, cands: &[usize], best_len: usize) -> usize {
    let target = src[pos + best_len];
    let mut best = 0usize;
    let mut i = 0;
    while i < cands.len() {
        let c = cands[i];
        if c + best_len < src.len() && src[c + best_len] == target && src[c..c + 4] == src[pos..pos + 4] {
            best += 1;
        }
        i += 1;
    }
    best
}

#[no_mangle]
#[inline(never)]
pub fn prefilter_4b_safe(src: &[u8], pos: usize, cands: &[usize], best_len: usize) -> usize {
    let tail4 = u32::from_le_bytes(src[pos + best_len - 3..pos + best_len + 1].try_into().unwrap());
    let head4 = u32::from_le_bytes(src[pos..pos + 4].try_into().unwrap());
    let mut best = 0usize;
    let mut i = 0;
    while i < cands.len() {
        let c = cands[i];
        if c + best_len + 1 <= src.len()
            && u32::from_le_bytes(src[c + best_len - 3..c + best_len + 1].try_into().unwrap()) == tail4
            && u32::from_le_bytes(src[c..c + 4].try_into().unwrap()) == head4
        {
            best += 1;
        }
        i += 1;
    }
    best
}

#[no_mangle]
#[inline(never)]
pub fn dp_relax_zipped(dp: &mut [u64], len_hi: &[u64], base_cost_dm1: u64, hi: usize) {
    for (d, &lh) in dp[3..=hi].iter_mut().zip(&len_hi[3..=hi]) {
        *d = (*d).min(base_cost_dm1 + lh);
    }
}

#[no_mangle]
#[inline(never)]
pub fn adler_chunks_exact_4lane(bytes: &[u8]) -> u32 {
    let (mut a, mut b) = (1u32, 0u32);
    let mut chunks = bytes.chunks_exact(5552);
    for chunk in &mut chunks {
        let (mut av, mut bv) = ([0u32; 4], [0u32; 4]);
        for c in chunk.chunks_exact(4) {
            for k in 0..4 {
                av[k] += u32::from(c[k]);
                bv[k] += av[k];
            }
        }
        b += 5552 * a;
        for k in 0..4 {
            av[k] %= MOD_ADLER;
            bv[k] %= MOD_ADLER;
            bv[k] *= 4;
        }
        bv[1] += MOD_ADLER - av[1];
        bv[2] += (MOD_ADLER - av[2]) * 2;
        bv[3] += (MOD_ADLER - av[3]) * 3;
        for k in 0..4 {
            a += av[k];
            b += bv[k];
        }
        a %= MOD_ADLER;
        b %= MOD_ADLER;
    }
    for &byte in chunks.remainder() {
        a += u32::from(byte);
        b += a;
    }
    ((b % MOD_ADLER) << 16) | (a % MOD_ADLER)
}

#[no_mangle]
#[inline(never)]
pub fn adler_while_fixed4(bytes: &[u8]) -> u32 {
    let (mut a, mut b) = (1u32, 0u32);
    let len = bytes.len();
    let mut pos = 0;
    while pos + 5552 <= len {
        let chunk = &bytes[pos..pos + 5552];
        let (mut av, mut bv) = ([0u32; 4], [0u32; 4]);
        let mut i = 0;
        while i < 5552 {
            let s = &chunk[i..i + 4];
            av[0] += u32::from(s[0]); bv[0] += av[0];
            av[1] += u32::from(s[1]); bv[1] += av[1];
            av[2] += u32::from(s[2]); bv[2] += av[2];
            av[3] += u32::from(s[3]); bv[3] += av[3];
            i += 4;
        }
        b += 5552 * a;
        for k in 0..4 {
            av[k] %= MOD_ADLER;
            bv[k] %= MOD_ADLER;
            bv[k] *= 4;
        }
        bv[1] += MOD_ADLER - av[1];
        bv[2] += (MOD_ADLER - av[2]) * 2;
        bv[3] += (MOD_ADLER - av[3]) * 3;
        for k in 0..4 {
            a += av[k];
            b += bv[k];
        }
        a %= MOD_ADLER;
        b %= MOD_ADLER;
        pos += 5552;
    }
    while pos < len {
        a += u32::from(bytes[pos]);
        b += a;
        pos += 1;
    }
    ((b % MOD_ADLER) << 16) | (a % MOD_ADLER)
}

#[no_mangle]
#[inline(never)]
pub fn adler_while_varindex4(bytes: &[u8]) -> u32 {
    let (mut a, mut b) = (1u32, 0u32);
    let len = bytes.len();
    let mut pos = 0;
    while pos < len {
        let end = pos + (len - pos).min(5552);
        let (mut av, mut bv) = ([0u32; 4], [0u32; 4]);
        let mut i = pos;
        let mut rem_pos = end;
        while i + 4 <= end {
            av[0] += u32::from(bytes[i]);     bv[0] += av[0];
            av[1] += u32::from(bytes[i + 1]); bv[1] += av[1];
            av[2] += u32::from(bytes[i + 2]); bv[2] += av[2];
            av[3] += u32::from(bytes[i + 3]); bv[3] += av[3];
            i += 4;
            rem_pos = i;
        }
        let chunk_n = (rem_pos - pos) as u32;
        b += chunk_n * a;
        for k in 0..4 {
            av[k] %= MOD_ADLER;
            bv[k] %= MOD_ADLER;
            bv[k] *= 4;
        }
        bv[1] += MOD_ADLER - av[1];
        bv[2] += (MOD_ADLER - av[2]) * 2;
        bv[3] += (MOD_ADLER - av[3]) * 3;
        for k in 0..4 {
            a += av[k];
            b += bv[k];
        }
        a %= MOD_ADLER;
        b %= MOD_ADLER;
        while rem_pos < end {
            a += u32::from(bytes[rem_pos]);
            b += a;
            rem_pos += 1;
        }
        a %= MOD_ADLER;
        b %= MOD_ADLER;
        pos = end;
    }
    (b << 16) | a
}

#[no_mangle]
#[inline(never)]
pub fn adler_serial_while(bytes: &[u8]) -> u32 {
    let (mut a, mut b) = (1u32, 0u32);
    let len = bytes.len();
    let mut pos = 0;
    while pos < len {
        let end = pos + (len - pos).min(5552);
        let mut i = pos;
        while i < end {
            a += u32::from(bytes[i]);
            b += a;
            i += 1;
        }
        a %= MOD_ADLER;
        b %= MOD_ADLER;
        pos = end;
    }
    (b << 16) | a
}

// --- 3. Double-Literal Root Fusion Safe vs Unsafe Asymmetry ---

const LIT_FLAG: u32 = 0x8000_0000;
const DBL_FLAG: u32 = 0x4000_0000;

fn build_decode_table(single_only: bool) -> [u32; 2048] {
    let mut t = [0u32; 2048];
    for (i, slot) in t.iter_mut().enumerate() {
        let b0 = ((i.wrapping_mul(73) ^ (i >> 3)) & 0x7f) as u32 | 0x20;
        let b1 = ((i.wrapping_mul(41) ^ (i >> 5)) & 0x7f) as u32 | 0x20;
        let len0 = match i & 15 {
            0..=3 => 4u32,
            4..=9 => 5u32,
            10..=13 => 6u32,
            _ => 8u32,
        };
        let len1 = match (i >> 4) & 7 {
            0..=2 => 4u32,
            3..=5 => 5u32,
            _ => 7u32,
        };
        if !single_only && len0 + len1 <= 11 && (i & 31) != 31 {
            *slot = LIT_FLAG | DBL_FLAG | (len0 + len1) | (b0 << 8) | (b1 << 16);
        } else {
            *slot = LIT_FLAG | len0 | (b0 << 8);
        }
    }
    t
}

#[no_mangle]
#[inline(never)]
pub fn loop_unsafe_lit(in_buf: &[u8], out_buf: &mut [u8], tbl: &[u32; 2048]) -> usize {
    let mut in_next = in_buf.as_ptr();
    let in_fast_end = unsafe { in_next.add(in_buf.len().saturating_sub(32)) };
    let out_start = out_buf.as_mut_ptr();
    let mut out_next = out_start;
    let out_fast_end = unsafe { out_start.add(out_buf.len().saturating_sub(64)) };
    let mut bitbuf = 0u64;
    let mut bits_in = 0u32;
    let tbl_ptr = tbl.as_ptr();
    unsafe {
        while in_next <= in_fast_end && out_next <= out_fast_end {
            if bits_in < 56 {
                let word = (in_next as *const u64).read_unaligned().to_le();
                bitbuf |= word << (bits_in & 63);
                in_next = in_next.add(((63 - bits_in) >> 3) as usize);
                bits_in |= 56;
            }
            let mut e = *tbl_ptr.add((bitbuf as usize) & 2047);
            for _ in 0..3 {
                if (e as i32) < 0 {
                    let cl = e & 63;
                    bitbuf >>= cl;
                    bits_in -= cl;
                    (out_next as *mut u16).write_unaligned(((e >> 8) as u16).to_le());
                    out_next = out_next.add(1 + (((e >> 30) & 1) as usize));
                    if bits_in < 12 {
                        break;
                    }
                    e = *tbl_ptr.add((bitbuf as usize) & 2047);
                } else {
                    break;
                }
            }
        }
        out_next.offset_from(out_start) as usize
    }
}

#[no_mangle]
#[inline(never)]
pub fn loop_safe_single_lit(in_buf: &[u8], out_buf: &mut [u8], tbl: &[u32; 2048]) -> usize {
    let mut in_pos = 0usize;
    let in_limit = in_buf.len().saturating_sub(32);
    let mut out_pos = 0usize;
    let out_limit = out_buf.len().saturating_sub(64);
    let mut bitbuf = 0u64;
    let mut bits_in = 0u32;
    while in_pos <= in_limit && out_pos <= out_limit {
        let win: &[u8; 8] = in_buf[in_pos..in_pos + 8].try_into().unwrap();
        bitbuf |= u64::from_le_bytes(*win) << (bits_in & 63);
        in_pos += ((63 - bits_in) >> 3) as usize;
        bits_in |= 56;
        let (_, dst) = out_buf.split_at_mut(out_pos);
        if dst.len() < 8 {
            break;
        }
        let mut e = tbl[(bitbuf as usize) & 2047];
        for step in 0..3 {
            if (e as i32) < 0 {
                let cl = e & 63;
                bitbuf >>= cl;
                bits_in -= cl;
                dst[step] = (e >> 8) as u8;
                out_pos += 1;
                e = tbl[(bitbuf as usize) & 2047];
            } else {
                break;
            }
        }
    }
    out_pos
}

#[no_mangle]
#[inline(never)]
pub fn loop_safe_double_lit(in_buf: &[u8], out_buf: &mut [u8], tbl: &[u32; 2048]) -> usize {
    let mut in_pos = 0usize;
    let in_limit = in_buf.len().saturating_sub(32);
    let mut out_pos = 0usize;
    let out_limit = out_buf.len().saturating_sub(64);
    let mut bitbuf = 0u64;
    let mut bits_in = 0u32;
    while in_pos <= in_limit && out_pos <= out_limit {
        let win: &[u8; 8] = in_buf[in_pos..in_pos + 8].try_into().unwrap();
        bitbuf |= u64::from_le_bytes(*win) << (bits_in & 63);
        in_pos += ((63 - bits_in) >> 3) as usize;
        bits_in |= 56;
        let (_, dst) = out_buf.split_at_mut(out_pos);
        if dst.len() < 8 {
            break;
        }
        let mut e = tbl[(bitbuf as usize) & 2047];
        let mut d_idx = 0usize;
        for _ in 0..3 {
            if (e as i32) < 0 {
                let cl = e & 63;
                bitbuf >>= cl;
                bits_in -= cl;
                dst[d_idx] = (e >> 8) as u8;
                if (e & DBL_FLAG) != 0 {
                    dst[d_idx + 1] = (e >> 16) as u8;
                    d_idx += 2;
                    out_pos += 2;
                } else {
                    d_idx += 1;
                    out_pos += 1;
                }
                if bits_in < 12 {
                    break;
                }
                e = tbl[(bitbuf as usize) & 2047];
            } else {
                break;
            }
        }
    }
    out_pos
}

// --- 4. Real-Slice Chain Walk: Shifted Prefix Window vs Per-Candidate first_chunk ---

#[inline(always)]
fn read_u16_le(src: &[u8], pos: usize) -> u16 {
    u16::from_le_bytes(src[pos..pos + 2].try_into().unwrap())
}

#[inline(always)]
fn read_u32_le(src: &[u8], pos: usize) -> u32 {
    u32::from_le_bytes(src[pos..pos + 4].try_into().unwrap())
}

#[no_mangle]
#[inline(never)]
pub fn chain_shifted_views(
    src: &[u8],
    pos: usize,
    cur4: u32,
    first_cand: usize,
    max_chain: usize,
    best_len: usize,
    prev4: &[u16; 32768],
) -> (usize, usize) {
    let min_cand = pos.saturating_sub(32768);
    if first_cand >= pos || first_cand < min_cand || best_len < 4 || pos + best_len + 1 > src.len() {
        return (0, 0);
    }
    let src_win = &src[..pos + 3];
    let end_slice = &src[best_len - 1..pos + best_len + 1];
    let end2 = read_u16_le(end_slice, pos);
    let mut cand = first_cand;
    let mut chain_left = max_chain;
    let mut hits = 0usize;
    loop {
        if cand < pos
            && read_u16_le(end_slice, cand) == end2
            && read_u32_le(src_win, cand) == cur4
        {
            hits += cand;
        }
        chain_left -= 1;
        if chain_left == 0 {
            break;
        }
        let step = prev4[cand & 32767] as usize;
        if step == 0 || cand - min_cand < step {
            break;
        }
        cand -= step;
    }
    (hits, cand)
}

#[no_mangle]
#[inline(never)]
pub fn chain_subslice_first_chunk(
    src: &[u8],
    pos: usize,
    cur4: u32,
    first_cand: usize,
    max_chain: usize,
    best_len: usize,
    prev4: &[u16; 32768],
) -> (usize, usize) {
    let min_cand = pos.saturating_sub(32768);
    if first_cand >= pos || first_cand < min_cand || best_len < 4 || pos + best_len + 1 > src.len() {
        return (0, 0);
    }
    let end2 = u16::from_le_bytes(*src[pos + best_len - 1..].first_chunk::<2>().unwrap());
    let mut cand = first_cand;
    let mut chain_left = max_chain;
    let mut hits = 0usize;
    loop {
        if cand < pos {
            if let Some(tail) = src[cand + best_len - 1..].first_chunk::<2>() {
                if u16::from_le_bytes(*tail) == end2 {
                    if let Some(head) = src[cand..].first_chunk::<4>() {
                        if u32::from_le_bytes(*head) == cur4 {
                            hits += cand;
                        }
                    }
                }
            }
        }
        chain_left -= 1;
        if chain_left == 0 {
            break;
        }
        let step = prev4[cand & 32767] as usize;
        if step == 0 || cand - min_cand < step {
            break;
        }
        cand -= step;
    }
    (hits, cand)
}

fn bench_adler(name: &str, data: &[u8], expected: u32, iters: usize, f: fn(&[u8]) -> u32) -> f64 {
    for _ in 0..3 {
        assert_eq!(black_box(f(black_box(data))), expected);
    }
    let mut ts = Vec::with_capacity(iters);
    for _ in 0..iters {
        let t0 = Instant::now();
        let got = black_box(f(black_box(data)));
        let dt = t0.elapsed().as_secs_f64();
        assert_eq!(got, expected);
        ts.push(dt);
    }
    ts.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let mbps = (data.len() as f64 / 1e6) / ts[iters / 2];
    println!("ADLER {name:<26} {mbps:8.1} MB/s");
    mbps
}

fn main() {
    let data: Vec<u8> = (0..(1024 * 1024)).map(|i| ((i * 131 + 17) & 0xff) as u8).collect();
    let exp = adler_serial_while(&data);
    bench_adler("chunks_exact_4lane", &data, exp, 21, adler_chunks_exact_4lane);
    bench_adler("while_fixed4", &data, exp, 21, adler_while_fixed4);
    bench_adler("while_varindex4", &data, exp, 15, adler_while_varindex4);
    bench_adler("serial_while", &data, exp, 15, adler_serial_while);

    let tbl_s = build_decode_table(true);
    let tbl_d = build_decode_table(false);
    let mut out_buf = vec![0u8; 4 * 1024 * 1024];
    for (name, f, tbl) in [
        ("unsafe_single", loop_unsafe_lit as fn(&[u8], &mut [u8], &[u32; 2048]) -> usize, &tbl_s),
        ("unsafe_double", loop_unsafe_lit as fn(&[u8], &mut [u8], &[u32; 2048]) -> usize, &tbl_d),
        ("safe_single", loop_safe_single_lit as fn(&[u8], &mut [u8], &[u32; 2048]) -> usize, &tbl_s),
        ("safe_double", loop_safe_double_lit as fn(&[u8], &mut [u8], &[u32; 2048]) -> usize, &tbl_d),
    ] {
        for _ in 0..3 {
            black_box(f(black_box(&data), black_box(&mut out_buf), tbl));
        }
        let mut ts = Vec::with_capacity(21);
        let mut out_n = 0;
        for _ in 0..21 {
            let t0 = Instant::now();
            out_n = black_box(f(black_box(&data), black_box(&mut out_buf), tbl));
            ts.push(t0.elapsed().as_secs_f64());
        }
        ts.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let mbps = (out_n as f64 / 1e6) / ts[10];
        println!("LIT {name:<26} out={out_n:<8} {mbps:7.1} MB/s");
    }

    // glibc mmap_threshold calloc vs reserve+fill_resize timing on 4 MiB buffers
    let mut calloc_us = Vec::with_capacity(15);
    let mut resize_us = Vec::with_capacity(15);
    for _ in 0..15 {
        let t0 = Instant::now();
        let mut v = vec![0u8; 4 * 1024 * 1024];
        v[0] = 1;
        v[4 * 1024 * 1024 - 1] = 2;
        black_box(&v);
        calloc_us.push(t0.elapsed().as_secs_f64() * 1e6);

        let t1 = Instant::now();
        let mut r = Vec::with_capacity(1024);
        r.resize(4 * 1024 * 1024, 0);
        r[0] = 1;
        r[4 * 1024 * 1024 - 1] = 2;
        black_box(&r);
        resize_us.push(t1.elapsed().as_secs_f64() * 1e6);
    }
    calloc_us.sort_by(|a, b| a.partial_cmp(b).unwrap());
    resize_us.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!(
        "ALLOC vec_zero_4MiB_med_us={:.1} resize_4MiB_med_us={:.1}",
        calloc_us[7], resize_us[7]
    );
}
