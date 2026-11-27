// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Rust source fixtures compiled and captured for each corpus category.

pub(super) const CAT1_SCALAR_SRC: &str = r#"
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

pub(super) const CAT2_ENUM_SRC: &str = r#"
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

pub(super) const CAT2_ENUM_TRACED_SRC: &str = r#"
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

pub(super) const CAT2_PADDED_PURE_SRC: &str = r#"
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

pub(super) const CAT2_PADDED_TRACED_SRC: &str = r#"
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

pub(super) const CAT3_CFG_SRC: &str = r#"
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
pub(super) const CAT3_CFG_TRACED_SRC: &str = r#"
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

pub(super) const CAT4_HELPERS_PURE_SRC: &str = r#"
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

pub(super) const CAT4_MULTICALL_TRACED_SRC: &str = r#"
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

pub(super) const CAT5_HELPERS_PURE_SRC: &str = r#"
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

pub(super) const CAT5_TRACED_SRC: &str = r#"
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

pub(super) const CAT5_INLINED_TWINS_SRC: &str = r#"
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

pub(super) const CAT6_NEG_SRC: &str = r#"
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
