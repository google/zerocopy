// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Curated multi-category differential trace corpus spanning:
//! 1. Multi-arg scalar & bitwise functions (`5` cases)
//! 2. Padded `#[repr(C)]` structs & fieldless enums (`4` cases)
//! 3. Multi-block branching & loop CFGs (`5` `FullBranchesAndCalls` cases)
//! 4. Multi-step & multi-call chains (`8` cases covering `0..3+` calls, nested
//!    stacks, cleanup unwinds, scheduled `ReturnBytes`, scheduled `Abort`
//!    without drop execution, and invalid scheduled bit-pattern `FaultUb`)
//! 5. Metamorphic inlining duality pairs (`5` cases comparing multi-call
//!    execution against source-inlined single-body twins across all active
//!    authorities)
//! 6. Negative UB, conservative over-approximation, and disclosed-gap probes
//!    (`6` cases)

use crate::{
    outcome::{
        ConservativeRefKind, DisclosedGapKind, DisclosedGapSpec, ExpectedConservativeSpec,
        ExpectedUbSpec, IntKind, SpineCompareMode, TraceVal, UbFaultClass,
    },
    spec::{
        CaseCategory, ExpectedCaseClass, LeanProgramSpec, MetamorphicTwin, ReturnShape,
        TraceTestCase,
    },
    trace_observer::{EnvAction, EnvSchedule},
};

const CAT1_SCALAR_SRC: &str = r#"
#![no_std]

#[inline(never)]
pub fn clamp_u32_range(x: u32, lo: u32, hi: u32) -> u32 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

#[inline(never)]
pub fn rotate_xor_mix(a: u32, b: u32, shift: u32) -> u32 {
    let s = shift & 7;
    let mixed = a ^ b;
    if s == 0 {
        mixed
    } else {
        (mixed << s) | (mixed >> (32 - s))
    }
}

#[inline(never)]
pub fn checked_affine_step(x: u32, scale: u32, bias: u32) -> u32 {
    let prod = x * scale;
    if prod > u32::MAX - bias {
        u32::MAX
    } else {
        prod + bias
    }
}

#[inline(never)]
pub fn signed_abs_diff(a: i32, b: i32) -> u32 {
    if a >= b {
        (a - b) as u32
    } else {
        (b - a) as u32
    }
}

#[inline(never)]
pub fn bitfield_extract(word: u32, offset: u32, mask: u32) -> u32 {
    let safe_off = offset & 15;
    (word >> safe_off) & mask
}
"#;

const CAT2_ENUM_SRC: &str = r#"
#![no_std]

#[repr(u8)]
#[derive(Clone, Copy)]
pub enum DispatchMode {
    Add = 0,
    Sub = 1,
    Xor = 2,
    SelectLeft = 3,
}

#[inline(never)]
pub fn c_like_enum_dispatch(mode: DispatchMode, x: u32, y: u32) -> u32 {
    match mode {
        DispatchMode::Add => x + y,
        DispatchMode::Sub => {
            if x >= y {
                x - y
            } else {
                y - x
            }
        }
        DispatchMode::Xor => x ^ y,
        DispatchMode::SelectLeft => x,
    }
}
"#;

const CAT2_ENUM_TRACED_SRC: &str = r#"
#[repr(u8)]
#[derive(Clone, Copy)]
pub enum DispatchMode {
    Add = 0,
    Sub = 1,
    Xor = 2,
    SelectLeft = 3,
}

impl anneal_rt::TraceCapture for DispatchMode {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let raw = *self as u8;
        raw.write_captured_bytes(dst);
    }
    fn trace_repr(&self) -> String {
        format!("enum({})", *self as u8)
    }
}

#[inline(never)]
pub fn c_like_enum_dispatch(mode: DispatchMode, x: u32, y: u32) -> u32 {
    match mode {
        DispatchMode::Add => x.wrapping_add(y),
        DispatchMode::Sub => {
            if x >= y {
                x.wrapping_sub(y)
            } else {
                y.wrapping_sub(x)
            }
        }
        DispatchMode::Xor => x ^ y,
        DispatchMode::SelectLeft => x,
    }
}
"#;

const CAT2_PADDED_PURE_SRC: &str = r#"
#![no_std]

#[repr(C)]
#[derive(Clone, Copy)]
pub struct PaddedHeader {
    pub tag: u8,
    pub len: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct NestedPair {
    pub flag: u8,
    pub left: u32,
    pub right: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct MaybeU32 {
    pub is_some: bool,
    pub val: u32,
}

#[inline(never)]
pub fn repr_c_padded_header(tag: u8, len: u32, bonus: u32) -> PaddedHeader {
    let out_len = if tag == 1 { len + bonus } else { len ^ bonus };
    PaddedHeader { tag, len: out_len }
}

#[inline(never)]
pub fn nested_padded_pair_sum(flag: u8, left: u32, right: u32, scale: u32) -> u32 {
    let pair = NestedPair { flag, left, right };
    let base = pair.left + pair.right;
    if pair.flag != 0 {
        base * scale
    } else {
        base
    }
}

#[inline(never)]
pub fn option_u32_map_or(is_some: bool, val: u32, fallback: u32, addend: u32) -> u32 {
    let opt = MaybeU32 { is_some, val };
    if opt.is_some {
        opt.val + addend
    } else {
        fallback
    }
}
"#;

const CAT2_PADDED_TRACED_SRC: &str = r#"
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PaddedHeader {
    pub tag: u8,
    pub len: u32,
}

impl anneal_rt::TraceCapture for PaddedHeader {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let off_tag = core::mem::offset_of!(PaddedHeader, tag);
        self.tag.write_captured_bytes(&mut dst[off_tag..off_tag + core::mem::size_of::<u8>()]);
        let off_len = core::mem::offset_of!(PaddedHeader, len);
        self.len.write_captured_bytes(&mut dst[off_len..off_len + core::mem::size_of::<u32>()]);
    }
    fn trace_repr(&self) -> String {
        format!("PaddedHeader{{tag={},len={}}}", self.tag, self.len)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NestedPair {
    pub flag: u8,
    pub left: u32,
    pub right: u32,
}

impl anneal_rt::TraceCapture for NestedPair {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let o0 = core::mem::offset_of!(NestedPair, flag);
        self.flag.write_captured_bytes(&mut dst[o0..o0 + 1]);
        let o1 = core::mem::offset_of!(NestedPair, left);
        self.left.write_captured_bytes(&mut dst[o1..o1 + 4]);
        let o2 = core::mem::offset_of!(NestedPair, right);
        self.right.write_captured_bytes(&mut dst[o2..o2 + 4]);
    }
    fn trace_repr(&self) -> String {
        format!("NestedPair{{flag={},left={},right={}}}", self.flag, self.left, self.right)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MaybeU32 {
    pub is_some: bool,
    pub val: u32,
}

#[inline(never)]
pub fn repr_c_padded_header(tag: u8, len: u32, bonus: u32) -> PaddedHeader {
    let out_len = if tag == 1 { len + bonus } else { len ^ bonus };
    PaddedHeader { tag, len: out_len }
}

#[inline(never)]
pub fn nested_padded_pair_sum(flag: u8, left: u32, right: u32, scale: u32) -> u32 {
    let pair = NestedPair { flag, left, right };
    let cap = anneal_rt::capture_value_bytes(&pair);
    assert!(cap[1].is_none() && cap[2].is_none() && cap[3].is_none());
    let base = pair.left + pair.right;
    if pair.flag != 0 {
        base * scale
    } else {
        base
    }
}

#[inline(never)]
pub fn option_u32_map_or(is_some: bool, val: u32, fallback: u32, addend: u32) -> u32 {
    let opt = MaybeU32 { is_some, val };
    if opt.is_some {
        opt.val + addend
    } else {
        fallback
    }
}
"#;

const CAT3_CFG_SRC: &str = r#"
#![no_std]

#[inline(never)]
pub fn match_four_way_tag(tag: u32, a: u32, b: u32) -> u32 {
    match tag {
        0 => a + b,
        1 => (a * 2) + b,
        2 => {
            if b >= a {
                b - a
            } else {
                a - b
            }
        }
        _ => a ^ b ^ 0x55,
    }
}

#[inline(never)]
pub fn short_circuit_guard_chain(a: u32, b: u32, c: u32) -> u32 {
    if a > 0 && b > a && c > b {
        a + b + c
    } else if a == 0 || b == 0 {
        c
    } else if b >= a {
        b - a
    } else {
        a - b
    }
}

#[inline(never)]
pub fn while_loop_accumulate(limit: u32, step: u32) -> u32 {
    let bounded = if limit > 6 { 6 } else { limit };
    let mut i = 0u32;
    let mut acc = 0u32;
    while i < bounded {
        acc = acc + (i * step);
        i = i + 1;
    }
    acc
}

#[inline(never)]
pub fn early_return_search_4(k0: u32, k1: u32, k2: u32, k3: u32, needle: u32) -> i32 {
    if k0 == needle {
        return 0;
    }
    if k1 == needle {
        return 1;
    }
    if k2 == needle {
        return 2;
    }
    if k3 == needle {
        return 3;
    }
    -1
}

#[inline(never)]
pub fn nested_if_else_matrix(row: u32, col: u32, val: u32) -> u32 {
    if row < 2 {
        if col < 2 {
            val + 10
        } else {
            val + 20
        }
    } else if col < 2 {
        val + 30
    } else {
        val + 40
    }
}
"#;

// Cat 3 `FullBranchesAndCalls` `emit_branch` block IDs mirror the pinned
// `rustc` `Runtime(PostCleanup)` MIR basic-block numbering emitted into
// `Captured.lean`; re-index if a future `rustc` toolchain pin bump reorders
// basic blocks.
const CAT3_CFG_TRACED_SRC: &str = r#"
#[inline(never)]
pub fn match_four_way_tag(tag: u32, a: u32, b: u32) -> u32 {
    match tag {
        0 => {
            anneal_rt::emit_branch(0, "0", 1);
            a + b
        }
        1 => {
            anneal_rt::emit_branch(0, "1", 3);
            (a * 2) + b
        }
        2 => {
            anneal_rt::emit_branch(0, "2", 2);
            if b >= a {
                anneal_rt::emit_branch(2, "true", 5);
                b - a
            } else {
                anneal_rt::emit_branch(2, "false", 6);
                a - b
            }
        }
        d => {
            anneal_rt::emit_branch(0, &format!("{d}"), 4);
            a ^ b ^ 0x55
        }
    }
}

#[inline(never)]
pub fn short_circuit_guard_chain(a: u32, b: u32, c: u32) -> u32 {
    let cond_a = a > 0;
    anneal_rt::emit_branch(0, if cond_a { "true" } else { "false" }, if cond_a { 1 } else { 4 });
    if cond_a {
        let cond_b = b > a;
        anneal_rt::emit_branch(1, if cond_b { "true" } else { "false" }, if cond_b { 2 } else { 4 });
        if cond_b {
            let cond_c = c > b;
            anneal_rt::emit_branch(2, if cond_c { "true" } else { "false" }, if cond_c { 3 } else { 4 });
            if cond_c {
                return a + b + c;
            }
        }
    }
    let zero_a = a == 0;
    anneal_rt::emit_branch(4, if zero_a { "true" } else { "false" }, if zero_a { 6 } else { 5 });
    if zero_a {
        return c;
    }
    let zero_b = b == 0;
    anneal_rt::emit_branch(5, if zero_b { "true" } else { "false" }, if zero_b { 6 } else { 7 });
    if zero_b {
        return c;
    }
    let ge = b >= a;
    anneal_rt::emit_branch(7, if ge { "true" } else { "false" }, if ge { 8 } else { 9 });
    if ge {
        b - a
    } else {
        a - b
    }
}

#[inline(never)]
pub fn while_loop_accumulate(limit: u32, step: u32) -> u32 {
    let gt6 = limit > 6;
    anneal_rt::emit_branch(0, if gt6 { "true" } else { "false" }, if gt6 { 1 } else { 2 });
    let bounded = if gt6 { 6 } else { limit };
    let mut i = 0u32;
    let mut acc = 0u32;
    loop {
        let cont = i < bounded;
        anneal_rt::emit_branch(4, if cont { "true" } else { "false" }, if cont { 5 } else { 6 });
        if !cont {
            break;
        }
        acc = acc + (i * step);
        i = i + 1;
    }
    acc
}

#[inline(never)]
pub fn early_return_search_4(k0: u32, k1: u32, k2: u32, k3: u32, needle: u32) -> i32 {
    let m0 = k0 == needle;
    anneal_rt::emit_branch(0, if m0 { "true" } else { "false" }, if m0 { 1 } else { 2 });
    if m0 {
        return 0;
    }
    let m1 = k1 == needle;
    anneal_rt::emit_branch(2, if m1 { "true" } else { "false" }, if m1 { 3 } else { 4 });
    if m1 {
        return 1;
    }
    let m2 = k2 == needle;
    anneal_rt::emit_branch(4, if m2 { "true" } else { "false" }, if m2 { 5 } else { 6 });
    if m2 {
        return 2;
    }
    let m3 = k3 == needle;
    anneal_rt::emit_branch(6, if m3 { "true" } else { "false" }, if m3 { 7 } else { 8 });
    if m3 {
        return 3;
    }
    -1
}

#[inline(never)]
pub fn nested_if_else_matrix(row: u32, col: u32, val: u32) -> u32 {
    let r_lt = row < 2;
    anneal_rt::emit_branch(0, if r_lt { "true" } else { "false" }, if r_lt { 1 } else { 5 });
    if r_lt {
        let c_lt = col < 2;
        anneal_rt::emit_branch(1, if c_lt { "true" } else { "false" }, if c_lt { 2 } else { 3 });
        if c_lt {
            val + 10
        } else {
            val + 20
        }
    } else {
        let c_lt = col < 2;
        anneal_rt::emit_branch(5, if c_lt { "true" } else { "false" }, if c_lt { 6 } else { 7 });
        if c_lt {
            val + 30
        } else {
            val + 40
        }
    }
}
"#;

const CAT4_HELPERS_PURE_SRC: &str = r#"
#![no_std]

#[inline(never)]
pub fn ext_transform_u32(v: u32) -> u32 {
    v * 3 + 7
}

#[inline(never)]
pub fn ext_combine_u32(a: u32, b: u32) -> u32 {
    a + (b * 5)
}

#[inline(never)]
pub fn ext_oracle_bool(x: u32) -> bool {
    (x & 1) == 1
}
"#;

const CAT4_MULTICALL_TRACED_SRC: &str = r#"
#[inline(never)]
pub fn ext_transform_u32(v: u32) -> u32 {
    anneal_rt::handle_scheduled_call(
        "ext_transform_u32",
        vec![anneal_rt::capture_value_bytes(&v)],
        vec![format!("{v}")],
        || v.wrapping_mul(3).wrapping_add(7),
    )
}

#[inline(never)]
pub fn ext_combine_u32(a: u32, b: u32) -> u32 {
    anneal_rt::handle_scheduled_call(
        "ext_combine_u32",
        vec![anneal_rt::capture_value_bytes(&a), anneal_rt::capture_value_bytes(&b)],
        vec![format!("{a}"), format!("{b}")],
        || a.wrapping_add(b.wrapping_mul(5)),
    )
}

#[inline(never)]
pub fn ext_may_panic_u32(trigger: u32, x: u32) -> u32 {
    anneal_rt::handle_scheduled_call(
        "ext_may_panic_u32",
        vec![anneal_rt::capture_value_bytes(&trigger), anneal_rt::capture_value_bytes(&x)],
        vec![format!("{trigger}"), format!("{x}")],
        || {
            if trigger == 0xDEAD {
                panic!("simulated external callee panic");
            }
            x.wrapping_add(trigger)
        },
    )
}

#[inline(never)]
pub fn ext_oracle_bool(x: u32) -> bool {
    anneal_rt::handle_scheduled_call(
        "ext_oracle_bool",
        vec![anneal_rt::capture_value_bytes(&x)],
        vec![format!("{x}")],
        || (x & 1) == 1,
    )
}

#[inline(never)]
pub fn call_once_and_postprocess(x: u32, bias: u32) -> u32 {
    let raw = ext_transform_u32(x);
    raw.wrapping_add(bias)
}

#[inline(never)]
pub fn call_twice_sequential(x: u32, y: u32) -> u32 {
    let first = ext_transform_u32(x);
    ext_transform_u32(first.wrapping_add(y))
}

#[inline(never)]
pub fn call_in_branch_arms(sel: u32, x: u32, y: u32) -> u32 {
    if sel & 1 == 0 {
        ext_transform_u32(x)
    } else {
        ext_combine_u32(x, y)
    }
}

#[inline(never)]
pub fn call_in_bounded_loop_3x(seed: u32) -> u32 {
    let a = ext_transform_u32(seed);
    let b = ext_transform_u32(a);
    ext_transform_u32(b)
}

#[inline(never)]
pub fn callee_panic_unwind_cleanup(trigger: u32, x: u32) -> u32 {
    struct CleanupGuard(u32);
    impl Drop for CleanupGuard {
        fn drop(&mut self) {
            let _ = std::hint::black_box(self.0.wrapping_add(1));
        }
    }
    let _guard = CleanupGuard(x);
    let out = ext_may_panic_u32(trigger, x);
    out.wrapping_add(1)
}

#[inline(never)]
pub fn callee_abort_skips_drops(trigger: u32, x: u32) -> u32 {
    struct DropBomb;
    impl Drop for DropBomb {
        fn drop(&mut self) {
            // If `Abort` unwound instead of calling `std::process::abort()`,
            // this drop would print a bogus trace JSON line and fail framing.
            println!("ANNEAL_ITREE_TRACE_JSON:{{\"outcome_kind\":\"unwound\"}}");
        }
    }
    let _bomb = DropBomb;
    let out = ext_may_panic_u32(trigger, x);
    core::mem::forget(_bomb);
    out
}

#[inline(never)]
pub fn call_bool_oracle_select(x: u32, a: u32, b: u32) -> u32 {
    if ext_oracle_bool(x) {
        a
    } else {
        b
    }
}
"#;

const CAT5_HELPERS_PURE_SRC: &str = r#"
#![no_std]

#[inline(never)]
pub fn helper_add_const(x: u32, c: u32) -> u32 {
    x + c
}

#[inline(never)]
pub fn helper_xor_fold(a: u32, b: u32) -> u32 {
    (a ^ b) + (a & 0xFF)
}

#[inline(never)]
pub fn helper_step_counter(cur: u32, delta: u32) -> u32 {
    (cur + delta) * 2
}

#[inline(never)]
pub fn helper_depth_step(n: u32, acc: u32) -> u32 {
    if n == 0 {
        acc
    } else {
        acc + (n * 4)
    }
}
"#;

const CAT5_TRACED_SRC: &str = r#"
#[inline(never)]
pub fn helper_add_const(x: u32, c: u32) -> u32 {
    anneal_rt::handle_scheduled_call(
        "helper_add_const",
        vec![anneal_rt::capture_value_bytes(&x), anneal_rt::capture_value_bytes(&c)],
        vec![format!("{x}"), format!("{c}")],
        || x.wrapping_add(c),
    )
}

#[inline(never)]
pub fn helper_xor_fold(a: u32, b: u32) -> u32 {
    anneal_rt::handle_scheduled_call(
        "helper_xor_fold",
        vec![anneal_rt::capture_value_bytes(&a), anneal_rt::capture_value_bytes(&b)],
        vec![format!("{a}"), format!("{b}")],
        || (a ^ b).wrapping_add(a & 0xFF),
    )
}

#[inline(never)]
pub fn helper_step_counter(cur: u32, delta: u32) -> u32 {
    anneal_rt::handle_scheduled_call(
        "helper_step_counter",
        vec![anneal_rt::capture_value_bytes(&cur), anneal_rt::capture_value_bytes(&delta)],
        vec![format!("{cur}"), format!("{delta}")],
        || cur.wrapping_add(delta).wrapping_mul(2),
    )
}

#[inline(never)]
pub fn helper_depth_step(n: u32, acc: u32) -> u32 {
    anneal_rt::handle_scheduled_call(
        "helper_depth_step",
        vec![anneal_rt::capture_value_bytes(&n), anneal_rt::capture_value_bytes(&acc)],
        vec![format!("{n}"), format!("{acc}")],
        || if n == 0 { acc } else { acc.wrapping_add(n.wrapping_mul(4)) },
    )
}

#[inline(never)]
pub fn pipeline_two_helpers(x: u32, y: u32) -> u32 {
    let stepped = helper_add_const(x, 12);
    helper_xor_fold(stepped, y)
}

#[inline(never)]
pub fn diamond_helper_dag(x: u32) -> u32 {
    let left = helper_add_const(x, 5);
    let right = helper_add_const(x, 9);
    helper_xor_fold(left, right)
}

#[inline(never)]
pub fn conditional_helper_dispatch(flag: u32, x: u32, y: u32) -> u32 {
    if flag == 0 {
        helper_add_const(x, y)
    } else {
        helper_xor_fold(x, y)
    }
}

#[inline(never)]
pub fn stateful_counter_pair(start: u32, delta: u32) -> u32 {
    let mid = helper_step_counter(start, delta);
    helper_step_counter(mid, delta.wrapping_add(1))
}

#[inline(never)]
pub fn recursive_depth_2_unroll(n: u32, acc: u32) -> u32 {
    let step1 = helper_depth_step(n, acc);
    let next_n = if n > 0 { n - 1 } else { 0 };
    helper_depth_step(next_n, step1)
}
"#;

const CAT5_INLINED_TWINS_SRC: &str = r#"
#![no_std]

#[inline(never)]
pub fn pipeline_two_helpers_inlined(x: u32, y: u32) -> u32 {
    let stepped = x + 12;
    (stepped ^ y) + (stepped & 0xFF)
}

#[inline(never)]
pub fn diamond_helper_dag_inlined(x: u32) -> u32 {
    let left = x + 5;
    let right = x + 9;
    (left ^ right) + (left & 0xFF)
}

#[inline(never)]
pub fn conditional_helper_dispatch_inlined(flag: u32, x: u32, y: u32) -> u32 {
    if flag == 0 {
        x + y
    } else {
        (x ^ y) + (x & 0xFF)
    }
}

#[inline(never)]
pub fn stateful_counter_pair_inlined(start: u32, delta: u32) -> u32 {
    let mid = (start + delta) * 2;
    (mid + (delta + 1)) * 2
}

#[inline(never)]
pub fn recursive_depth_2_unroll_inlined(n: u32, acc: u32) -> u32 {
    let step1 = if n == 0 { acc } else { acc + (n * 4) };
    let next_n = if n > 0 { n - 1 } else { 0 };
    if next_n == 0 {
        step1
    } else {
        step1 + (next_n * 4)
    }
}
"#;

const CAT6_NEG_SRC: &str = r#"
#![no_std]

#[inline(never)]
pub fn unreachable_ub(flag: u32) -> u32 {
    if flag == 0 {
        unsafe { core::hint::unreachable_unchecked() }
    } else {
        flag + 1
    }
}

#[inline(never)]
pub fn shift_overflow_ub(x: u32, shift: u32) -> u32 {
    unsafe { x.unchecked_shl(shift) }
}

#[inline(never)]
pub fn div_by_zero_probe(a: u32, b: u32) -> u32 {
    a / b
}

#[inline(never)]
pub fn oob_index_probe(idx: usize) -> u32 {
    let arr: [u32; 4] = [10, 20, 30, 40];
    arr[idx]
}

#[inline(never)]
pub fn caller_raw_ptr_aliasing_gap(x: u32) -> *const u32 {
    let local = x;
    let r: &u32 = &local;
    let p: *const u32 = core::ptr::addr_of!(local);
    if *r == 0 { p } else { p }
}
"#;

/// Filter corpus cases by substring match on `case.id`, failing closed when an
/// explicit filter matches zero cases so typos never silently pass with
/// `total=0`.
pub fn filter_corpus_cases(
    mut corpus: Vec<TraceTestCase>,
    filter: Option<&str>,
) -> Result<Vec<TraceTestCase>, String> {
    if let Some(substr) = filter {
        corpus.retain(|c| c.id.contains(substr));
        if corpus.is_empty() {
            return Err(format!("corpus filter {substr:?} matched 0 cases"));
        }
    }
    Ok(corpus)
}

/// Build the full curated differential trace corpus covering all 6 categories
/// (`33` cases).
pub fn curated_corpus() -> Vec<TraceTestCase> {
    let mut cases = Vec::with_capacity(33);

    // -----------------------------------------------------------------------
    // Category 1: Multi-arg scalar & bitwise (5 cases — real captured MIR)
    // -----------------------------------------------------------------------
    cases.push(captured_u32_case(
        "cat1_clamp_u32_range",
        CaseCategory::ScalarBitwise,
        "cat1_scalar",
        CAT1_SCALAR_SRC,
        None,
        "clamp_u32_range",
        &[42, 10, 30],
        SpineCompareMode::ObsErasedCallsOnly,
    ));
    cases.push(captured_u32_case(
        "cat1_rotate_xor_mix",
        CaseCategory::ScalarBitwise,
        "cat1_scalar",
        CAT1_SCALAR_SRC,
        None,
        "rotate_xor_mix",
        &[0x1234_5678, 0x9ABC_DEF0, 3],
        SpineCompareMode::ObsErasedCallsOnly,
    ));
    cases.push(captured_u32_case(
        "cat1_checked_affine_step",
        CaseCategory::ScalarBitwise,
        "cat1_scalar",
        CAT1_SCALAR_SRC,
        None,
        "checked_affine_step",
        &[100, 7, 55],
        SpineCompareMode::ObsErasedCallsOnly,
    ));
    cases.push(TraceTestCase {
        id: "cat1_signed_abs_diff".to_string(),
        category: CaseCategory::ScalarBitwise,
        pure_rust_source: CAT1_SCALAR_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "signed_abs_diff".to_string(),
        rust_arg_exprs: vec!["-15i32".to_string(), "27i32".to_string()],
        lean_args: vec![TraceVal::i32(-15), TraceVal::i32(27)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat1_scalar".to_string(),
            select_fn: "signed_abs_diff".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(captured_u32_case(
        "cat1_bitfield_extract",
        CaseCategory::ScalarBitwise,
        "cat1_scalar",
        CAT1_SCALAR_SRC,
        None,
        "bitfield_extract",
        &[0xABCD_1234, 4, 0x0FFF],
        SpineCompareMode::ObsErasedCallsOnly,
    ));

    // -----------------------------------------------------------------------
    // Category 2: Padded #[repr(C)] structs & fieldless enums (4 cases)
    // -----------------------------------------------------------------------
    cases.push(TraceTestCase {
        id: "cat2_c_like_enum_dispatch".to_string(),
        category: CaseCategory::PaddedAggregatesAndEnums,
        pure_rust_source: CAT2_ENUM_SRC.to_string(),
        traced_rust_source: Some(CAT2_ENUM_TRACED_SRC.to_string()),
        entry_fn: "c_like_enum_dispatch".to_string(),
        rust_arg_exprs: vec![
            "subject::DispatchMode::Xor".to_string(),
            "0xF0F0u32".to_string(),
            "0x0FF0u32".to_string(),
        ],
        lean_args: vec![
            TraceVal::Enum {
                type_name: "DispatchMode".to_string(),
                variant_name: "Xor".to_string(),
                variant_index: 2,
                discriminant: 2,
                tag_bytes: Some(1),
            },
            TraceVal::u32(0xF0F0),
            TraceVal::u32(0x0FF0),
        ],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat2_enum".to_string(),
            select_fn: "c_like_enum_dispatch".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat2_repr_c_padded_header".to_string(),
        category: CaseCategory::PaddedAggregatesAndEnums,
        pure_rust_source: CAT2_PADDED_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT2_PADDED_TRACED_SRC.to_string()),
        entry_fn: "repr_c_padded_header".to_string(),
        rust_arg_exprs: vec!["1u8".to_string(), "100u32".to_string(), "23u32".to_string()],
        lean_args: vec![TraceVal::u8(1), TraceVal::u32(100), TraceVal::u32(23)],
        ret_shape: ReturnShape::PaddedStruct { type_name: "PaddedHeader".to_string() },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat2_padded".to_string(),
            select_fn: "repr_c_padded_header".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::ConservativeOverApprox,
        expected_ub: None,
        expected_conservative: Some(ExpectedConservativeSpec::new(
            ConservativeRefKind::Returned,
            "unsupported type: PaddedHeader",
        )),
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat2_nested_padded_pair_sum".to_string(),
        category: CaseCategory::PaddedAggregatesAndEnums,
        pure_rust_source: CAT2_PADDED_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT2_PADDED_TRACED_SRC.to_string()),
        entry_fn: "nested_padded_pair_sum".to_string(),
        rust_arg_exprs: vec![
            "1u8".to_string(),
            "7u32".to_string(),
            "13u32".to_string(),
            "3u32".to_string(),
        ],
        lean_args: vec![TraceVal::u8(1), TraceVal::u32(7), TraceVal::u32(13), TraceVal::u32(3)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat2_padded".to_string(),
            select_fn: "nested_padded_pair_sum".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::ConservativeOverApprox,
        expected_ub: None,
        expected_conservative: Some(ExpectedConservativeSpec::new(
            ConservativeRefKind::Returned,
            "unsupported type: NestedPair",
        )),
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat2_option_u32_map_or".to_string(),
        category: CaseCategory::PaddedAggregatesAndEnums,
        pure_rust_source: CAT2_PADDED_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT2_PADDED_TRACED_SRC.to_string()),
        entry_fn: "option_u32_map_or".to_string(),
        rust_arg_exprs: vec![
            "true".to_string(),
            "40u32".to_string(),
            "99u32".to_string(),
            "2u32".to_string(),
        ],
        lean_args: vec![
            TraceVal::bool_val(true),
            TraceVal::u32(40),
            TraceVal::u32(99),
            TraceVal::u32(2),
        ],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat2_padded".to_string(),
            select_fn: "option_u32_map_or".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::ConservativeOverApprox,
        expected_ub: None,
        expected_conservative: Some(ExpectedConservativeSpec::new(
            ConservativeRefKind::Returned,
            "unsupported type: MaybeU32",
        )),
        disclosed_gap: None,
    });

    // -----------------------------------------------------------------------
    // Category 3: Multi-block branching & loop CFGs (5 cases — real captured
    // MIR cross-checked under `SpineCompareMode::FullBranchesAndCalls`)
    // -----------------------------------------------------------------------
    cases.push(captured_u32_case(
        "cat3_match_four_way_tag",
        CaseCategory::BranchLoopCfg,
        "cat3_cfg",
        CAT3_CFG_SRC,
        Some(CAT3_CFG_TRACED_SRC),
        "match_four_way_tag",
        &[2, 9, 25],
        SpineCompareMode::FullBranchesAndCalls,
    ));
    cases.push(captured_u32_case(
        "cat3_short_circuit_guard_chain",
        CaseCategory::BranchLoopCfg,
        "cat3_cfg",
        CAT3_CFG_SRC,
        Some(CAT3_CFG_TRACED_SRC),
        "short_circuit_guard_chain",
        &[3, 7, 15],
        SpineCompareMode::FullBranchesAndCalls,
    ));
    cases.push(captured_u32_case(
        "cat3_while_loop_accumulate",
        CaseCategory::BranchLoopCfg,
        "cat3_cfg",
        CAT3_CFG_SRC,
        Some(CAT3_CFG_TRACED_SRC),
        "while_loop_accumulate",
        &[5, 4],
        SpineCompareMode::FullBranchesAndCalls,
    ));
    cases.push(TraceTestCase {
        id: "cat3_early_return_search_4".to_string(),
        category: CaseCategory::BranchLoopCfg,
        pure_rust_source: CAT3_CFG_SRC.to_string(),
        traced_rust_source: Some(CAT3_CFG_TRACED_SRC.to_string()),
        entry_fn: "early_return_search_4".to_string(),
        rust_arg_exprs: vec![
            "11u32".to_string(),
            "22u32".to_string(),
            "33u32".to_string(),
            "44u32".to_string(),
            "33u32".to_string(),
        ],
        lean_args: vec![
            TraceVal::u32(11),
            TraceVal::u32(22),
            TraceVal::u32(33),
            TraceVal::u32(44),
            TraceVal::u32(33),
        ],
        ret_shape: ReturnShape::Scalar { kind: IntKind::I32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat3_cfg".to_string(),
            select_fn: "early_return_search_4".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::FullBranchesAndCalls,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(captured_u32_case(
        "cat3_nested_if_else_matrix",
        CaseCategory::BranchLoopCfg,
        "cat3_cfg",
        CAT3_CFG_SRC,
        Some(CAT3_CFG_TRACED_SRC),
        "nested_if_else_matrix",
        &[3, 1, 100],
        SpineCompareMode::FullBranchesAndCalls,
    ));

    // -----------------------------------------------------------------------
    // Category 4: Multi-step & multi-call chains (8 cases — captured leaf
    // callees + scheduled ReturnBytes, Unwind cleanup, real Abort, & invalid
    // ReturnBytes UB)
    // -----------------------------------------------------------------------
    cases.push(TraceTestCase {
        id: "cat4_call_once_and_postprocess".to_string(),
        category: CaseCategory::MultiCallChain,
        pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
        entry_fn: "call_once_and_postprocess".to_string(),
        rust_arg_exprs: vec!["10u32".to_string(), "5u32".to_string()],
        lean_args: vec![TraceVal::u32(10), TraceVal::u32(5)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
            crate_name: "cat4_helpers".to_string(),
            captured_callees: vec!["ext_transform_u32".to_string()],
            caller_identity: "call_once_and_postprocess".to_string(),
            caller_lean_body: lean_body_call_once_and_postprocess(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::FullBranchesAndCalls,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat4_call_twice_sequential".to_string(),
        category: CaseCategory::MultiCallChain,
        pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
        entry_fn: "call_twice_sequential".to_string(),
        rust_arg_exprs: vec!["4u32".to_string(), "6u32".to_string()],
        lean_args: vec![TraceVal::u32(4), TraceVal::u32(6)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
            crate_name: "cat4_helpers".to_string(),
            captured_callees: vec!["ext_transform_u32".to_string()],
            caller_identity: "call_twice_sequential".to_string(),
            caller_lean_body: lean_body_call_twice_sequential(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat4_call_in_branch_arms".to_string(),
        category: CaseCategory::MultiCallChain,
        pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
        entry_fn: "call_in_branch_arms".to_string(),
        rust_arg_exprs: vec!["3u32".to_string(), "11u32".to_string(), "7u32".to_string()],
        lean_args: vec![TraceVal::u32(3), TraceVal::u32(11), TraceVal::u32(7)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
            crate_name: "cat4_helpers".to_string(),
            captured_callees: vec!["ext_transform_u32".to_string(), "ext_combine_u32".to_string()],
            caller_identity: "call_in_branch_arms".to_string(),
            caller_lean_body: lean_body_call_in_branch_arms(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 256,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat4_call_in_bounded_loop_3x".to_string(),
        category: CaseCategory::MultiCallChain,
        pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
        entry_fn: "call_in_bounded_loop_3x".to_string(),
        rust_arg_exprs: vec!["2u32".to_string()],
        lean_args: vec![TraceVal::u32(2)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
            crate_name: "cat4_helpers".to_string(),
            captured_callees: vec!["ext_transform_u32".to_string()],
            caller_identity: "call_in_bounded_loop_3x".to_string(),
            caller_lean_body: lean_body_call_in_bounded_loop_3x(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 512,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    });
    {
        let mut unwind_sched = EnvSchedule::default();
        unwind_sched.push_callee(
            "ext_may_panic_u32",
            EnvAction::Unwind { message: "simulated external callee panic".to_string() },
        );
        cases.push(TraceTestCase {
            id: "cat4_callee_panic_unwind_cleanup".to_string(),
            category: CaseCategory::MultiCallChain,
            pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
            traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
            entry_fn: "callee_panic_unwind_cleanup".to_string(),
            rust_arg_exprs: vec!["0xDEADu32".to_string(), "17u32".to_string()],
            lean_args: vec![TraceVal::u32(0xDEAD), TraceVal::u32(17)],
            ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
            lean_program_spec: LeanProgramSpec::SyntheticMirAst {
                program_lean_expr: lean_prog_unwind_cleanup(),
                external_callees: vec!["ext_may_panic_u32".to_string()],
            },
            metamorphic_inlined_twin: None,
            env_schedule: unwind_sched,
            fuel: 256,
            spine_mode: SpineCompareMode::FullBranchesAndCalls,
            expected_class: ExpectedCaseClass::Unwind,
            expected_ub: None,
            expected_conservative: None,
            disclosed_gap: None,
        });
    }
    {
        let mut ret_sched = EnvSchedule::default();
        ret_sched.push_callee(
            "ext_transform_u32",
            EnvAction::ReturnBytes(777u32.to_le_bytes().to_vec()),
        );
        cases.push(TraceTestCase {
            id: "cat4_scheduled_return_bytes_override".to_string(),
            category: CaseCategory::MultiCallChain,
            pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
            traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
            entry_fn: "call_twice_sequential".to_string(),
            rust_arg_exprs: vec!["4u32".to_string(), "6u32".to_string()],
            lean_args: vec![TraceVal::u32(4), TraceVal::u32(6)],
            ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
            lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
                crate_name: "cat4_helpers".to_string(),
                captured_callees: vec!["ext_transform_u32".to_string()],
                caller_identity: "call_twice_sequential".to_string(),
                caller_lean_body: lean_body_call_twice_sequential(),
                external_callees: vec!["ext_transform_u32".to_string()],
            },
            metamorphic_inlined_twin: None,
            env_schedule: ret_sched,
            fuel: 256,
            spine_mode: SpineCompareMode::FullBranchesAndCalls,
            expected_class: ExpectedCaseClass::Agree,
            expected_ub: None,
            expected_conservative: None,
            disclosed_gap: None,
        });
    }
    {
        let mut abort_sched = EnvSchedule::default();
        abort_sched.push_callee(
            "ext_may_panic_u32",
            EnvAction::Abort { reason: "halt_boundary".to_string() },
        );
        cases.push(TraceTestCase {
            id: "cat4_scheduled_abort_no_drop".to_string(),
            category: CaseCategory::MultiCallChain,
            pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
            traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
            entry_fn: "callee_abort_skips_drops".to_string(),
            rust_arg_exprs: vec!["1u32".to_string(), "17u32".to_string()],
            lean_args: vec![TraceVal::u32(1), TraceVal::u32(17)],
            ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
            lean_program_spec: LeanProgramSpec::SyntheticMirAst {
                program_lean_expr: lean_prog_unwind_cleanup(),
                external_callees: vec!["ext_may_panic_u32".to_string()],
            },
            metamorphic_inlined_twin: None,
            env_schedule: abort_sched,
            fuel: 256,
            spine_mode: SpineCompareMode::ObsErasedCallsOnly,
            expected_class: ExpectedCaseClass::Abort,
            expected_ub: None,
            expected_conservative: None,
            disclosed_gap: None,
        });
    }
    {
        let mut bad_bool_sched = EnvSchedule::default();
        bad_bool_sched.push_callee("ext_oracle_bool", EnvAction::ReturnBytes(vec![2u8]));
        cases.push(TraceTestCase {
            id: "cat4_scheduled_invalid_bool_return_ub".to_string(),
            category: CaseCategory::MultiCallChain,
            pure_rust_source: CAT4_HELPERS_PURE_SRC.to_string(),
            traced_rust_source: Some(CAT4_MULTICALL_TRACED_SRC.to_string()),
            entry_fn: "call_bool_oracle_select".to_string(),
            rust_arg_exprs: vec!["5u32".to_string(), "100u32".to_string(), "200u32".to_string()],
            lean_args: vec![TraceVal::u32(5), TraceVal::u32(100), TraceVal::u32(200)],
            ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
            lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
                crate_name: "cat4_helpers".to_string(),
                captured_callees: vec!["ext_oracle_bool".to_string()],
                caller_identity: "call_bool_oracle_select".to_string(),
                caller_lean_body: lean_body_call_bool_oracle_select(),
                external_callees: vec!["ext_oracle_bool".to_string()],
            },
            metamorphic_inlined_twin: None,
            env_schedule: bad_bool_sched,
            fuel: 256,
            spine_mode: SpineCompareMode::OutcomeOnly,
            expected_class: ExpectedCaseClass::UndefinedBehavior,
            expected_ub: Some(
                ExpectedUbSpec::new(
                    UbFaultClass::ScheduledReturnDecode,
                    "callee `ext_oracle_bool` scheduled ReturnBytes invalid",
                    Some("invalid scheduled ReturnBytes for ext_oracle_bool"),
                )
                .with_lean_refusal_marker(
                    "external callee unsupported in StrictVerbatim: ext_oracle_bool",
                ),
            ),
            expected_conservative: None,
            disclosed_gap: None,
        });
    }

    // -----------------------------------------------------------------------
    // Category 5: Metamorphic Inlining Duality Pairs (5 cases)
    // -----------------------------------------------------------------------
    cases.push(metamorphic_case(
        "cat5_pipeline_two_helpers",
        "pipeline_two_helpers",
        "pipeline_two_helpers_inlined",
        &[19, 77],
        vec!["helper_add_const".to_string(), "helper_xor_fold".to_string()],
        lean_body_pipeline_two_helpers(),
    ));
    cases.push(metamorphic_case(
        "cat5_diamond_helper_dag",
        "diamond_helper_dag",
        "diamond_helper_dag_inlined",
        &[23],
        vec!["helper_add_const".to_string(), "helper_xor_fold".to_string()],
        lean_body_diamond_helper_dag(),
    ));
    cases.push(metamorphic_case(
        "cat5_conditional_helper_dispatch",
        "conditional_helper_dispatch",
        "conditional_helper_dispatch_inlined",
        &[1, 35, 19],
        vec!["helper_add_const".to_string(), "helper_xor_fold".to_string()],
        lean_body_conditional_helper_dispatch(),
    ));
    cases.push(metamorphic_case(
        "cat5_stateful_counter_pair",
        "stateful_counter_pair",
        "stateful_counter_pair_inlined",
        &[8, 3],
        vec!["helper_step_counter".to_string()],
        lean_body_stateful_counter_pair(),
    ));
    cases.push(metamorphic_case(
        "cat5_recursive_depth_2_unroll",
        "recursive_depth_2_unroll",
        "recursive_depth_2_unroll_inlined",
        &[3, 10],
        vec!["helper_depth_step".to_string()],
        lean_body_recursive_depth_2_unroll(),
    ));

    // -----------------------------------------------------------------------
    // Category 6: Negative UB / Conservative Over-Approx / Disclosed Gaps (6)
    // -----------------------------------------------------------------------
    cases.push(TraceTestCase {
        id: "cat6_unreachable_ub".to_string(),
        category: CaseCategory::NegativeUbAndOverApprox,
        pure_rust_source: CAT6_NEG_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "unreachable_ub".to_string(),
        rust_arg_exprs: vec!["0u32".to_string()],
        lean_args: vec![TraceVal::u32(0)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat6_neg".to_string(),
            select_fn: "unreachable_ub".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 128,
        spine_mode: SpineCompareMode::OutcomeOnly,
        expected_class: ExpectedCaseClass::UndefinedBehavior,
        expected_ub: Some(
            ExpectedUbSpec::new(
                UbFaultClass::UnreachableOrNoUnwind,
                "entering unreachable code",
                None,
            )
            .with_lean_refusal_marker(
                "unsupported terminator: Trusted.MirSemantics.FaultKind.unsupported",
            )
            .with_mir_eval_marker("executed Unreachable terminator"),
        ),
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat6_mir_unreachable_ub".to_string(),
        category: CaseCategory::NegativeUbAndOverApprox,
        pure_rust_source: CAT6_NEG_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "unreachable_ub".to_string(),
        rust_arg_exprs: vec!["0u32".to_string()],
        lean_args: vec![TraceVal::u32(0)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::SyntheticMirAst {
            program_lean_expr: lean_prog_unreachable_ub(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 128,
        spine_mode: SpineCompareMode::OutcomeOnly,
        expected_class: ExpectedCaseClass::UndefinedBehavior,
        expected_ub: Some(ExpectedUbSpec::new(
            UbFaultClass::UnreachableOrNoUnwind,
            "entering unreachable code",
            Some("entering unreachable code"),
        )),
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat6_shift_overflow_ub".to_string(),
        category: CaseCategory::NegativeUbAndOverApprox,
        pure_rust_source: CAT6_NEG_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "shift_overflow_ub".to_string(),
        rust_arg_exprs: vec!["1u32".to_string(), "32u32".to_string()],
        lean_args: vec![TraceVal::u32(1), TraceVal::u32(32)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::SyntheticMirAst {
            program_lean_expr: lean_prog_shl_unchecked_ub(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 128,
        spine_mode: SpineCompareMode::OutcomeOnly,
        expected_class: ExpectedCaseClass::UndefinedBehavior,
        expected_ub: Some(ExpectedUbSpec::new(
            UbFaultClass::UncheckedShiftOverflow,
            "unchecked_shl",
            Some("unchecked shift overflow"),
        )),
        expected_conservative: None,
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat6_div_by_zero_probe".to_string(),
        category: CaseCategory::NegativeUbAndOverApprox,
        pure_rust_source: CAT6_NEG_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "div_by_zero_probe".to_string(),
        rust_arg_exprs: vec!["9u32".to_string(), "0u32".to_string()],
        lean_args: vec![TraceVal::u32(9), TraceVal::u32(0)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat6_neg".to_string(),
            select_fn: "div_by_zero_probe".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 128,
        spine_mode: SpineCompareMode::OutcomeOnly,
        expected_class: ExpectedCaseClass::ConservativeOverApprox,
        expected_ub: None,
        expected_conservative: Some(ExpectedConservativeSpec::new(
            ConservativeRefKind::Unwound,
            "initStateBy unsupported",
        )),
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat6_oob_index_probe".to_string(),
        category: CaseCategory::NegativeUbAndOverApprox,
        pure_rust_source: CAT6_NEG_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "oob_index_probe".to_string(),
        rust_arg_exprs: vec!["9usize".to_string()],
        lean_args: vec![TraceVal::usize_val(9)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat6_neg".to_string(),
            select_fn: "oob_index_probe".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 128,
        spine_mode: SpineCompareMode::OutcomeOnly,
        expected_class: ExpectedCaseClass::ConservativeOverApprox,
        expected_ub: None,
        expected_conservative: Some(ExpectedConservativeSpec::new(
            ConservativeRefKind::Unwound,
            "unsupported place projection `Index(",
        )),
        disclosed_gap: None,
    });
    cases.push(TraceTestCase {
        id: "cat6_caller_raw_ptr_aliasing_gap".to_string(),
        category: CaseCategory::NegativeUbAndOverApprox,
        pure_rust_source: CAT6_NEG_SRC.to_string(),
        traced_rust_source: None,
        entry_fn: "caller_raw_ptr_aliasing_gap".to_string(),
        rust_arg_exprs: vec!["7u32".to_string()],
        lean_args: vec![TraceVal::u32(7)],
        ret_shape: ReturnShape::OpaquePtr,
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: "cat6_neg".to_string(),
            select_fn: "caller_raw_ptr_aliasing_gap".to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 128,
        spine_mode: SpineCompareMode::OutcomeOnly,
        expected_class: ExpectedCaseClass::DisclosedGap,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: Some(DisclosedGapSpec::new(
            DisclosedGapKind::CallerRawPtrAliasing,
            "does not model Rust's pointer aliasing rules",
        )),
    });

    cases
}

#[allow(clippy::too_many_arguments)]
fn captured_u32_case(
    id: &str,
    category: CaseCategory,
    crate_name: &str,
    src: &str,
    traced_src: Option<&str>,
    fn_name: &str,
    args: &[u32],
    spine_mode: SpineCompareMode,
) -> TraceTestCase {
    TraceTestCase {
        id: id.to_string(),
        category,
        pure_rust_source: src.to_string(),
        traced_rust_source: traced_src.map(ToString::to_string),
        entry_fn: fn_name.to_string(),
        rust_arg_exprs: args.iter().map(|v| format!("{v}u32")).collect(),
        lean_args: args.iter().copied().map(TraceVal::u32).collect(),
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::CapturedRust {
            crate_name: crate_name.to_string(),
            select_fn: fn_name.to_string(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 512,
        spine_mode,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    }
}

fn metamorphic_case(
    id: &str,
    entry_fn: &str,
    inlined_fn: &str,
    args: &[u32],
    captured_callees: Vec<String>,
    caller_lean_body: String,
) -> TraceTestCase {
    TraceTestCase {
        id: id.to_string(),
        category: CaseCategory::MetamorphicInliningDuality,
        pure_rust_source: CAT5_HELPERS_PURE_SRC.to_string(),
        traced_rust_source: Some(CAT5_TRACED_SRC.to_string()),
        entry_fn: entry_fn.to_string(),
        rust_arg_exprs: args.iter().map(|v| format!("{v}u32")).collect(),
        lean_args: args.iter().copied().map(TraceVal::u32).collect(),
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
            crate_name: "cat5_helpers".to_string(),
            captured_callees,
            caller_identity: entry_fn.to_string(),
            caller_lean_body,
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: Some(MetamorphicTwin {
            crate_name: "cat5_inlined".to_string(),
            pure_rust_source: CAT5_INLINED_TWINS_SRC.to_string(),
            entry_fn: inlined_fn.to_string(),
        }),
        env_schedule: EnvSchedule::default(),
        fuel: 512,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    }
}

// ---------------------------------------------------------------------------
// Lean `Trusted.MirAst.Body` definitions for multi-call callers whose callees
// are REAL `anneal-rustc-capture` captured MIR bodies at indices 1, 2, ...
// ---------------------------------------------------------------------------

fn lean_body_call_once_and_postprocess() -> String {
    r#"{
      argumentCount := 2,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨3, []⟩ (some 1) .continue_ },
        { statements := [
            .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.copy ⟨2, []⟩))
          ],
          terminator := .return_ }
      ]
    }"#
    .to_string()
}

fn lean_body_call_twice_sequential() -> String {
    r#"{
      argumentCount := 2,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨3, []⟩ (some 1) .continue_ },
        { statements := [
            .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.copy ⟨2, []⟩))
          ],
          terminator := .call 1 [.copy ⟨4, []⟩] ⟨0, []⟩ (some 2) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

fn lean_body_call_in_branch_arms() -> String {
    r#"{
      argumentCount := 3,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [
            .assign ⟨4, []⟩ (.binaryOp .bitAnd (.copy ⟨1, []⟩)
              (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))
          ],
          terminator := .switchInt (.copy ⟨4, []⟩) ⟨[(BitVec.ofNat 128 0, 1)], 2⟩ },
        { statements := [],
          terminator := .call 1 [.copy ⟨2, []⟩] ⟨0, []⟩ (some 3) .continue_ },
        { statements := [],
          terminator := .call 2 [.copy ⟨2, []⟩, .copy ⟨3, []⟩] ⟨0, []⟩ (some 3) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

fn lean_body_call_in_bounded_loop_3x() -> String {
    r#"{
      argumentCount := 1,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨2, []⟩ (some 1) .continue_ },
        { statements := [],
          terminator := .call 1 [.copy ⟨2, []⟩] ⟨3, []⟩ (some 2) .continue_ },
        { statements := [],
          terminator := .call 1 [.copy ⟨3, []⟩] ⟨0, []⟩ (some 3) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

fn lean_body_call_bool_oracle_select() -> String {
    r#"{
      argumentCount := 3,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .bool],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨4, []⟩ (some 1) .continue_ },
        { statements := [],
          terminator := .switchInt (.copy ⟨4, []⟩) ⟨[(BitVec.ofNat 128 0, 3)], 2⟩ },
        { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))],
          terminator := .return_ },
        { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨3, []⟩))],
          terminator := .return_ }
      ]
    }"#
    .to_string()
}

fn lean_prog_unwind_cleanup() -> String {
    r#"{
      bodies := [
        {
          argumentCount := 2,
          locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
          basicBlocks := [
            { statements := [.storageLive 3],
              terminator := .call 1 [.copy ⟨1, []⟩, .copy ⟨2, []⟩] ⟨3, []⟩ (some 1) (.cleanup 2) },
            { statements := [
                .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨3, []⟩)
                  (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))
              ],
              terminator := .return_ },
            { statements := [.nop, .storageDead 3],
              terminator := .unwindResume,
              cleanup := true }
          ],
          identity := "callee_panic_unwind_cleanup"
        },
        {
          argumentCount := 2,
          locals := [.int .i32 false, .int .i32 false, .int .i32 false],
          basicBlocks := [
            { statements := [
                .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
              ],
              terminator := .return_ }
          ],
          identity := "ext_may_panic_u32"
        }
      ],
      entryDefId := 0,
      pointerWidthBits := 64,
      mirProfileVersion := 1,
      scope := .unit
    }"#
    .to_string()
}

fn lean_body_pipeline_two_helpers() -> String {
    r#"{
      argumentCount := 2,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1
            [.copy ⟨1, []⟩, .constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 12)⟩]
            ⟨3, []⟩ (some 1) .continue_ },
        { statements := [],
          terminator := .call 2 [.copy ⟨3, []⟩, .copy ⟨2, []⟩] ⟨0, []⟩ (some 2) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

fn lean_body_diamond_helper_dag() -> String {
    r#"{
      argumentCount := 1,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1
            [.copy ⟨1, []⟩, .constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 5)⟩]
            ⟨2, []⟩ (some 1) .continue_ },
        { statements := [],
          terminator := .call 1
            [.copy ⟨1, []⟩, .constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 9)⟩]
            ⟨3, []⟩ (some 2) .continue_ },
        { statements := [],
          terminator := .call 2 [.copy ⟨2, []⟩, .copy ⟨3, []⟩] ⟨0, []⟩ (some 3) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

fn lean_body_conditional_helper_dispatch() -> String {
    r#"{
      argumentCount := 3,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .switchInt (.copy ⟨1, []⟩) ⟨[(BitVec.ofNat 128 0, 1)], 2⟩ },
        { statements := [],
          terminator := .call 1 [.copy ⟨2, []⟩, .copy ⟨3, []⟩] ⟨0, []⟩ (some 3) .continue_ },
        { statements := [],
          terminator := .call 2 [.copy ⟨2, []⟩, .copy ⟨3, []⟩] ⟨0, []⟩ (some 3) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

fn lean_body_stateful_counter_pair() -> String {
    r#"{
      argumentCount := 2,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩, .copy ⟨2, []⟩] ⟨3, []⟩ (some 1) .continue_ },
        { statements := [
            .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨2, []⟩)
              (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))
          ],
          terminator := .call 1 [.copy ⟨3, []⟩, .copy ⟨4, []⟩] ⟨0, []⟩ (some 2) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

fn lean_body_recursive_depth_2_unroll() -> String {
    r#"{
      argumentCount := 2,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩, .copy ⟨2, []⟩] ⟨3, []⟩ (some 1) .continue_ },
        { statements := [],
          terminator := .switchInt (.copy ⟨1, []⟩) ⟨[(BitVec.ofNat 128 0, 2)], 3⟩ },
        { statements := [
            .assign ⟨4, []⟩ (.use (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 0)⟩))
          ],
          terminator := .goto 4 },
        { statements := [
            .assign ⟨4, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩)
              (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))
          ],
          terminator := .goto 4 },
        { statements := [],
          terminator := .call 1 [.copy ⟨4, []⟩, .copy ⟨3, []⟩] ⟨0, []⟩ (some 5) .continue_ },
        { statements := [], terminator := .return_ }
      ]
    }"#
    .to_string()
}

fn lean_prog_unreachable_ub() -> String {
    r#"{
      bodies := [
        {
          argumentCount := 1,
          locals := [.int .i32 false, .int .i32 false],
          basicBlocks := [
            { statements := [],
              terminator := .switchInt (.copy ⟨1, []⟩) ⟨[(BitVec.ofNat 128 0, 1)], 2⟩ },
            { statements := [],
              terminator := .unreachable },
            { statements := [
                .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
                  (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 1)⟩))
              ],
              terminator := .return_ }
          ],
          identity := "unreachable_ub"
        }
      ],
      entryDefId := 0,
      pointerWidthBits := 64,
      mirProfileVersion := 1,
      scope := .unit
    }"#
    .to_string()
}

fn lean_prog_shl_unchecked_ub() -> String {
    r#"{
      bodies := [
        {
          argumentCount := 2,
          locals := [.int .i32 false, .int .i32 false, .int .i32 false],
          basicBlocks := [
            { statements := [
                .assign ⟨0, []⟩ (.binaryOp .shlUnchecked (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
              ],
              terminator := .return_ }
          ],
          identity := "shift_overflow_ub"
        }
      ],
      entryDefId := 0,
      pointerWidthBits := 64,
      mirProfileVersion := 1,
      scope := .unit
    }"#
    .to_string()
}
