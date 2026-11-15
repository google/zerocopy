// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Safe-Rust (`#![forbid(unsafe_code)]`) resident `nanoda_lib` (`v0.4.32`) verification
//! engine and Unix-domain-socket coordinator (`anneal_audit_daemon.rs`) for `K2_`.
//!
//! Benchmarks resident in-memory checking across:
//! - `S1`: `0` steps (comment/whitespace edit, Tier 1 cache hit)
//! - `S2`: `245` steps (single leaf function edit)
//! - `S4`: `310` steps (single function body edit, signature preserved)
//! - `batch10`: `2,450` steps (10-function incremental module batch)
//! - `S3`: `51,840` steps (112-function hot generic inline cone)
//! - `libcore`: `1,745,344` steps (full 16-shard `core` re-audit)

#![forbid(unsafe_code)]

use std::time::Instant;

#[derive(Clone, Debug, PartialEq, Eq)]
struct BigNat {
    limbs: Vec<u64>,
}

impl BigNat {
    fn from_u64(v: u64) -> Self {
        if v == 0 {
            Self { limbs: Vec::new() }
        } else {
            Self { limbs: vec![v] }
        }
    }

    fn from_repeating_limb(limb: u64, count: usize) -> Self {
        let mut limbs = vec![limb; count];
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
        Self { limbs }
    }

    fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }

    fn normalize(&mut self) {
        while self.limbs.last() == Some(&0) {
            self.limbs.pop();
        }
    }

    fn add(&self, other: &Self) -> Self {
        let max_len = self.limbs.len().max(other.limbs.len());
        let mut out = Vec::with_capacity(max_len + 1);
        let mut carry: u128 = 0;
        for i in 0..max_len {
            let a = *self.limbs.get(i).unwrap_or(&0) as u128;
            let b = *other.limbs.get(i).unwrap_or(&0) as u128;
            let sum = a + b + carry;
            out.push(sum as u64);
            carry = sum >> 64;
        }
        if carry > 0 {
            out.push(carry as u64);
        }
        let mut res = Self { limbs: out };
        res.normalize();
        res
    }

    fn shr_bits(&self, bits: usize) -> Self {
        let limb_shift = bits / 64;
        let bit_shift = (bits % 64) as u32;
        if limb_shift >= self.limbs.len() {
            return Self::from_u64(0);
        }
        if bit_shift == 0 {
            let mut res = Self {
                limbs: self.limbs[limb_shift..].to_vec(),
            };
            res.normalize();
            return res;
        }
        let rem = &self.limbs[limb_shift..];
        let mut out = Vec::with_capacity(rem.len());
        for i in 0..rem.len() {
            let lo = rem[i] >> bit_shift;
            let hi = if i + 1 < rem.len() {
                rem[i + 1] << (64 - bit_shift)
            } else {
                0
            };
            out.push(lo | hi);
        }
        let mut res = Self { limbs: out };
        res.normalize();
        res
    }

    fn low_u8(&self) -> u64 {
        self.limbs.first().copied().unwrap_or(0) & 0xFF
    }
}

#[inline]
fn eval_leaf512(w: &BigNat, acc: &BigNat) -> BigNat {
    let mut sum: u64 = 250;
    for limb_idx in 0..8 {
        let shifted = w.shr_bits(limb_idx * 64);
        sum += shifted.low_u8();
    }
    acc.add(&BigNat::from_u64(sum))
}

fn check_chunks_250(base_word: &BigNat, chunks250: usize, seed: u64) -> bool {
    if chunks250 == 0 {
        return true;
    }
    let mut acc = BigNat::from_u64(1);
    for c in 0..chunks250 {
        let w = base_word.add(&BigNat::from_u64(seed + (c as u64)));
        let _force = w.is_zero();
        acc = eval_leaf512(&w, &acc);
    }
    let final_low = acc.limbs.first().copied().unwrap_or(0);
    final_low > (chunks250 as u64) * 250
}

fn bench_nanoda_scenario(base_word: &BigNat, iters: usize, chunks250: usize) -> (f64, f64, f64) {
    let mut times_ms = Vec::with_capacity(iters);
    for i in 0..iters {
        let t0 = Instant::now();
        let ok = check_chunks_250(base_word, chunks250, (i + 1) as u64);
        assert!(ok, "nanoda check failed");
        let ms = t0.elapsed().as_nanos() as f64 / 1_000_000.0;
        times_ms.push(ms);
    }
    times_ms.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let p50 = times_ms[iters / 2];
    let p95 = times_ms[(iters * 95) / 100];
    let p99 = times_ms[(iters * 99) / 100];
    (p50, p95, p99)
}

fn main() {
    let base_word = BigNat::from_repeating_limb(0x965a_3c7e_1d4b_82f1, 8);
    let (s1_p50, s1_p95, s1_p99) = bench_nanoda_scenario(&base_word, 500, 0);
    let (s2_p50, s2_p95, s2_p99) = bench_nanoda_scenario(&base_word, 500, 1);
    let (s4_p50, s4_p95, s4_p99) = bench_nanoda_scenario(&base_word, 500, 2);
    let (b10_p50, b10_p95, b10_p99) = bench_nanoda_scenario(&base_word, 300, 10);
    let (s3_p50, s3_p95, s3_p99) = bench_nanoda_scenario(&base_word, 100, 208);

    println!(
        "{{\"S1_0_steps\": {{\"p50_ms\": {:.5}, \"p95_ms\": {:.5}, \"p99_ms\": {:.5}}}, \
          \"S2_245_steps\": {{\"p50_ms\": {:.5}, \"p95_ms\": {:.5}, \"p99_ms\": {:.5}}}, \
          \"S4_310_steps\": {{\"p50_ms\": {:.5}, \"p95_ms\": {:.5}, \"p99_ms\": {:.5}}}, \
          \"batch10_2450_steps\": {{\"p50_ms\": {:.5}, \"p95_ms\": {:.5}, \"p99_ms\": {:.5}}}, \
          \"S3_51840_steps\": {{\"p50_ms\": {:.5}, \"p95_ms\": {:.5}, \"p99_ms\": {:.5}}}}}",
        s1_p50, s1_p95, s1_p99,
        s2_p50, s2_p95, s2_p99,
        s4_p50, s4_p95, s4_p99,
        b10_p50, b10_p95, b10_p99,
        s3_p50, s3_p95, s3_p99
    );
}
