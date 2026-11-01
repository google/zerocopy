// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Representative Rust patterns for measuring the differential impact of
//! `rustc_mir_transform` passes (`-Zmir-opt-level=0`, selective M2 passes, and
//! `-Zmir-opt-level=2`) before and after LLVM's `opt -passes='default<O2>'`.

#![crate_type = "lib"]
#![no_std]

#[repr(C)]
pub struct Packet256 {
    pub words: [u64; 32],
}

impl Packet256 {
    #[inline(always)]
    pub fn new(seed: u64) -> Self {
        let mut words = [0u64; 32];
        words[0] = seed;
        words[1] = seed.wrapping_add(1);
        words[15] = seed.wrapping_mul(3);
        words[31] = seed ^ 0x5555_5555_5555_5555;
        Self { words }
    }

    #[inline(always)]
    pub fn with_header(mut self, tag: u64, seq: u64) -> Self {
        self.words[2] = tag;
        self.words[3] = seq;
        self
    }

    #[inline(always)]
    pub fn with_footer(mut self, checksum: u64) -> Self {
        self.words[30] = checksum;
        self.words[31] ^= checksum;
        self
    }
}

extern "C" {
    fn observe_packet_word(w: u64);
    fn drop_hook(id: u64);
}

/// Pattern 1: Large aggregate (`[u64; 32]`) move chains / builder pattern.
/// Tests `DestinationPropagation` + `CopyProp` on 256-byte aggregate moves.
#[no_mangle]
pub fn pattern1_large_aggregate_builder(
    seed: u64,
    tag: u64,
    seq: u64,
    flag: bool,
) -> Packet256 {
    let stage0 = Packet256::new(seed);
    let stage1 = stage0.with_header(tag, seq);
    let stage2 = if flag {
        let mut tmp = stage1;
        tmp.words[4] = seed ^ tag;
        unsafe { observe_packet_word(tmp.words[0]) };
        tmp
    } else {
        let mut tmp = stage1;
        tmp.words[4] = seed.wrapping_add(seq);
        unsafe { observe_packet_word(tmp.words[1]) };
        tmp
    };
    let stage3 = stage2.with_footer(tag.wrapping_add(seq));
    stage3
}

/// Pattern 2: Nested generic iterator / `Option::map` adapter chain.
/// Tests `MIR Inline` + `ScalarReplacementOfAggregates` (`MirSROA`).
#[derive(Copy, Clone)]
pub struct Pair<A, B> {
    pub fst: A,
    pub snd: B,
}

#[inline]
fn wrap_pair(x: u64) -> Option<Pair<u64, u64>> {
    if x != 0 {
        Some(Pair { fst: x, snd: x.wrapping_mul(3) })
    } else {
        None
    }
}

#[inline]
fn transform_pair(p: Pair<u64, u64>, delta: u64) -> Pair<u64, u64> {
    Pair {
        fst: p.fst.wrapping_add(delta),
        snd: p.snd ^ delta,
    }
}

#[no_mangle]
pub fn pattern2_option_adapter_chain(input: &[u64; 8], delta: u64) -> u64 {
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < 8 {
        let v = input[i];
        let mapped = wrap_pair(v)
            .map(|p| transform_pair(p, delta))
            .map(|p| Pair { fst: p.fst ^ p.snd, snd: p.snd.wrapping_add(1) })
            .and_then(|p| if p.fst > 10 { Some(p.fst.wrapping_add(p.snd)) } else { None });
        if let Some(res) = mapped {
            acc = acc.wrapping_add(res);
        }
        i += 1;
    }
    acc
}

/// Pattern 3: Enum state machine / `Result` match chain.
/// Tests `SimplifyCfg` / `SwitchInt` / enum branch simplification.
#[derive(Copy, Clone)]
pub enum StepState {
    Init(u64),
    Running { acc: u64, rem: u64 },
    Done(u64),
    Fault(u32),
}

#[no_mangle]
pub fn pattern3_enum_state_machine(x: u64, y: u64, z: u64) -> Result<u64, u32> {
    let s0 = if x == 0 {
        StepState::Fault(1)
    } else {
        StepState::Init(x)
    };
    let s1 = match s0 {
        StepState::Init(v) => StepState::Running { acc: v.wrapping_add(y), rem: z },
        StepState::Running { acc, rem } => StepState::Running { acc, rem },
        StepState::Done(v) => StepState::Done(v),
        StepState::Fault(e) => StepState::Fault(e),
    };
    let s2 = match s1 {
        StepState::Running { acc, rem } if rem > 0 => {
            StepState::Done(acc.wrapping_mul(rem))
        }
        StepState::Running { acc, .. } => StepState::Done(acc),
        StepState::Done(v) => StepState::Done(v),
        StepState::Init(_) => StepState::Fault(2),
        StepState::Fault(e) => StepState::Fault(e),
    };
    match s2 {
        StepState::Done(v) => Ok(v),
        StepState::Fault(e) => Err(e),
        _ => Err(99),
    }
}

/// Pattern 4: Scalar arithmetic & CSE loop.
/// Tests overlap between `MIR GVN`/`InstSimplify` and `LLVM GVN + InstCombine`.
#[no_mangle]
pub fn pattern4_scalar_cse_loop(data: &[u64; 16], k1: u64, k2: u64) -> u64 {
    let mut sum = 0u64;
    let mut i = 0usize;
    while i < 16 {
        let x = data[i];
        let a = x.wrapping_mul(k1).wrapping_add(k2);
        let b = x.wrapping_mul(k1).wrapping_add(k2);
        let c = (a ^ b).wrapping_add(a);
        let d = x.wrapping_add(0).wrapping_mul(1);
        sum = sum.wrapping_add(c ^ d);
        i += 1;
    }
    sum
}

/// Pattern 5: `Drop` elaboration with conditional move.
/// Tests `ElaborateDrops` static dead/initialized drop elimination vs. dynamic
/// drop flags.
pub struct Guard(pub u64);

impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { drop_hook(self.0) };
    }
}

#[no_mangle]
pub fn pattern5_drop_elaboration(id1: u64, id2: u64, take_early: bool) -> u64 {
    let g_unconditional = Guard(id1);
    let g_conditional = Guard(id2);
    let moved_unconditional = g_unconditional;
    let out = if take_early {
        let taken = g_conditional;
        taken.0.wrapping_add(moved_unconditional.0)
    } else {
        moved_unconditional.0
    };
    out
}
