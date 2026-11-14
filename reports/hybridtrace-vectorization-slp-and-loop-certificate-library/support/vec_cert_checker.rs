// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Native Rust checker for the 6-schema compositional `HybridTrace`
//! vectorization and SLP certificate library.

use std::time::Instant;

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VecSchemaKind {
    LoopGuardSplit = 1,
    LoopStripMine = 2,
    LoopBodyInterleavePermute = 3,
    SimdLanePackIso = 4,
    SimdReductionMonoid = 5,
    SlpDagPack = 6,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct VecCertStep {
    pub schema: VecSchemaKind,
    pub site_id: u32,
    pub vector_width: u16,
    pub unroll_factor: u16,
    pub flags: u32,
    pub src_cone_hash: u64,
    pub tgt_cone_hash: u64,
}

#[inline(never)]
pub fn check_vec_step(s: &VecCertStep) -> bool {
    if s.src_cone_hash == s.tgt_cone_hash || s.vector_width == 0 || s.unroll_factor == 0 {
        return false;
    }
    match s.schema {
        VecSchemaKind::LoopGuardSplit => (s.flags & 0x1) != 0,
        VecSchemaKind::LoopStripMine => (s.vector_width as u32 * s.unroll_factor as u32) >= 2,
        VecSchemaKind::LoopBodyInterleavePermute => (s.flags & 0x2) != 0,
        VecSchemaKind::SimdLanePackIso => (s.flags & 0x4) != 0,
        VecSchemaKind::SimdReductionMonoid => (s.flags & 0x8) != 0,
        VecSchemaKind::SlpDagPack => s.vector_width >= 2 && (s.flags & 0x10) != 0,
    }
}

pub fn check_vec_certificate(steps: &[VecCertStep]) -> bool {
    let mut ok = true;
    for st in steps {
        ok &= check_vec_step(st);
    }
    ok
}

fn main() {
    let sample_steps = [
        VecCertStep { schema: VecSchemaKind::LoopGuardSplit, site_id: 1, vector_width: 4, unroll_factor: 2, flags: 0x1F, src_cone_hash: 0x1111, tgt_cone_hash: 0x2222 },
        VecCertStep { schema: VecSchemaKind::LoopStripMine, site_id: 1, vector_width: 4, unroll_factor: 2, flags: 0x1F, src_cone_hash: 0x2222, tgt_cone_hash: 0x3333 },
        VecCertStep { schema: VecSchemaKind::LoopBodyInterleavePermute, site_id: 1, vector_width: 4, unroll_factor: 2, flags: 0x1F, src_cone_hash: 0x3333, tgt_cone_hash: 0x4444 },
        VecCertStep { schema: VecSchemaKind::SimdLanePackIso, site_id: 1, vector_width: 4, unroll_factor: 2, flags: 0x1F, src_cone_hash: 0x4444, tgt_cone_hash: 0x5555 },
        VecCertStep { schema: VecSchemaKind::SimdReductionMonoid, site_id: 1, vector_width: 4, unroll_factor: 2, flags: 0x1F, src_cone_hash: 0x5555, tgt_cone_hash: 0x6666 },
    ];
    let iters = 200_000u64;
    let t0 = Instant::now();
    let mut valid_cnt = 0u64;
    for _ in 0..iters {
        if std::hint::black_box(check_vec_certificate(std::hint::black_box(&sample_steps))) {
            valid_cnt += 1;
        }
    }
    let ns = t0.elapsed().as_nanos() as f64;
    let us_per_5step_cert = (ns / iters as f64) / 1000.0;
    let us_per_step = us_per_5step_cert / 5.0;
    println!("{{\"valid_iters\": {}, \"us_per_5step_cert\": {:.5}, \"us_per_step\": {:.6}}}", valid_cnt, us_per_5step_cert, us_per_step);
}
