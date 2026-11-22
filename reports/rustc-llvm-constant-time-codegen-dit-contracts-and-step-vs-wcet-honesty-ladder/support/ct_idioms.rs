#![no_std]
#![allow(dead_code)]

use core::hint::{black_box, select_unpredictable};
use core::ptr::read_volatile;

#[inline(always)]
fn ct_eq_u64_bitmath_inner(a: u64, b: u64) -> u64 {
    let d = a ^ b;
    let neq = (d | d.wrapping_neg()) >> 63;
    neq ^ 1
}

#[inline(always)]
fn ct_lt_u64_bitmath_inner(a: u64, b: u64) -> u64 {
    // Classic branchless unsigned less-than (Hacker's Delight / BearSSL / subtle)
    (a ^ ((a ^ b) | (a.wrapping_sub(b) ^ b))) >> 63
}

// ============================================================================
// 1. core::hint::select_unpredictable family
// ============================================================================

#[unsafe(no_mangle)]
pub extern "C" fn ct_select_unpred_u64(c: bool, a: u64, b: u64) -> u64 {
    select_unpredictable(c, a, b)
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_select_unpred_load_arms(c: bool, a: &u64, b: &u64) -> u64 {
    let va = *a;
    let vb = *b;
    select_unpredictable(c, va.wrapping_mul(3).wrapping_add(1), vb)
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Block4 {
    pub limbs: [u64; 4],
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_select_unpred_struct(c: bool, a: Block4, b: Block4) -> Block4 {
    select_unpredictable(c, a, b)
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_select_unpred_in_loop(
    conds: *const u8,
    a: *const u64,
    b: *const u64,
    n: usize,
) -> u64 {
    let mut acc: u64 = 0;
    let mut i = 0;
    while i < n {
        unsafe {
            let c = (*conds.add(i) & 1) != 0;
            let va = (*a.add(i)).wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(acc);
            let vb = (*b.add(i)).wrapping_add(acc);
            acc = select_unpredictable(c, va, vb);
        }
        i += 1;
    }
    acc
}

// ============================================================================
// 2. Wrapping-mask family: ((c as u64).wrapping_neg() & a) | (...)
// ============================================================================

#[unsafe(no_mangle)]
pub extern "C" fn ct_wrap_mask_bool(c: bool, a: u64, b: u64) -> u64 {
    let m = (c as u64).wrapping_neg();
    (m & a) | (!m & b)
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_wrap_mask_u8_masked(c: u8, a: u64, b: u64) -> u64 {
    let m = ((c & 1) as u64).wrapping_neg();
    (m & a) | (!m & b)
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_wrap_mask_load_arms(c: bool, a: &u64, b: &u64) -> u64 {
    let va = (*a).wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(7);
    let vb = *b;
    let m = (c as u64).wrapping_neg();
    (m & va) | (!m & vb)
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_wrap_mask_in_loop(
    conds: *const u8,
    a: *const u64,
    b: *const u64,
    n: usize,
) -> u64 {
    let mut acc: u64 = 0;
    let mut i = 0;
    while i < n {
        unsafe {
            let m = ((*conds.add(i) & 1) as u64).wrapping_neg();
            let va = (*a.add(i)).wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(acc);
            let vb = (*b.add(i)).wrapping_add(acc);
            acc = (m & va) | (!m & vb);
        }
        i += 1;
    }
    acc
}

// ============================================================================
// 3. subtle-style Choice XOR/AND selects (with and without barriers)
// ============================================================================

#[unsafe(no_mangle)]
pub extern "C" fn ct_subtle_xor_no_barrier(c: u8, a: u64, b: u64) -> u64 {
    let mask = ((c & 1) as i64).wrapping_neg() as u64;
    a ^ (mask & (a ^ b))
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_subtle_xor_black_box(c: u8, a: u64, b: u64) -> u64 {
    let choice = black_box(c & 1);
    let mask = (choice as i64).wrapping_neg() as u64;
    a ^ (mask & (a ^ b))
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_subtle_xor_volatile(c: u8, a: u64, b: u64) -> u64 {
    let c_bit = c & 1;
    let choice = unsafe { read_volatile(&c_bit) };
    let mask = (choice as i64).wrapping_neg() as u64;
    a ^ (mask & (a ^ b))
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_subtle_xor_in_loop_no_barrier(
    conds: *const u8,
    a: *const u64,
    b: *const u64,
    n: usize,
) -> u64 {
    let mut acc: u64 = 0;
    let mut i = 0;
    while i < n {
        unsafe {
            let mask = ((*conds.add(i) & 1) as i64).wrapping_neg() as u64;
            let va = (*a.add(i)).wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(acc);
            let vb = (*b.add(i)).wrapping_add(acc);
            acc = vb ^ (mask & (vb ^ va));
        }
        i += 1;
    }
    acc
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_subtle_xor_in_loop_black_box(
    conds: *const u8,
    a: *const u64,
    b: *const u64,
    n: usize,
) -> u64 {
    let mut acc: u64 = 0;
    let mut i = 0;
    while i < n {
        unsafe {
            let choice = black_box(*conds.add(i) & 1);
            let mask = (choice as i64).wrapping_neg() as u64;
            let va = (*a.add(i)).wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(acc);
            let vb = (*b.add(i)).wrapping_add(acc);
            acc = vb ^ (mask & (vb ^ va));
        }
        i += 1;
    }
    acc
}

// ============================================================================
// 4. Constant-time u64 comparisons
// ============================================================================

#[unsafe(no_mangle)]
pub extern "C" fn ct_u64_eq_bitmath(a: u64, b: u64) -> u64 {
    ct_eq_u64_bitmath_inner(a, b)
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_u64_lt_bitmath(a: u64, b: u64) -> u64 {
    ct_lt_u64_bitmath_inner(a, b)
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_u64_lt_bitmath_load_select(a: u64, b: u64, x: &u64, y: &u64) -> u64 {
    let m = ct_lt_u64_bitmath_inner(a, b).wrapping_neg();
    let vx = (*x).wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(13);
    let vy = *y;
    (m & vx) | (!m & vy)
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_u64_eq_bitmath_load_select(a: u64, b: u64, x: &u64, y: &u64) -> u64 {
    let m = ct_eq_u64_bitmath_inner(a, b).wrapping_neg();
    let vx = (*x).wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(13);
    let vy = *y;
    (m & vx) | (!m & vy)
}

// ============================================================================
// 5. Lookup-table masking & .rodata table / jump-table synthesis
// ============================================================================

#[unsafe(no_mangle)]
pub extern "C" fn ct_lut_linear_scan_16(table: &[u64; 16], secret_idx: u8) -> u64 {
    let idx = (secret_idx & 15) as u64;
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    while i < 16 {
        let eq = ct_eq_u64_bitmath_inner(i as u64, idx);
        let mask = eq.wrapping_neg();
        acc |= mask & table[i];
        i += 1;
    }
    acc
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_lut_linear_scan_const_sbox(secret_idx: u8) -> u8 {
    const SBOX: [u8; 16] = [
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5,
        0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    ];
    let idx = (secret_idx & 15) as u64;
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    while i < 16 {
        let eq = ct_eq_u64_bitmath_inner(i as u64, idx);
        let mask = eq.wrapping_neg();
        acc |= mask & (SBOX[i] as u64);
        i += 1;
    }
    acc as u8
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_lut_linear_scan_const_sbox_black_box(secret_idx: u8) -> u8 {
    const SBOX: [u8; 16] = [
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5,
        0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    ];
    let idx = black_box((secret_idx & 15) as u64);
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    while i < 16 {
        let eq = ct_eq_u64_bitmath_inner(i as u64, idx);
        let mask = eq.wrapping_neg();
        acc |= mask & (SBOX[i] as u64);
        i += 1;
    }
    acc as u8
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_match_to_rodata_lut(secret_nibble: u8) -> u32 {
    match secret_nibble & 7 {
        0 => 0x6363_6363,
        1 => 0x7c7c_7c7c,
        2 => 0x7777_7777,
        3 => 0x7b7b_7b7b,
        4 => 0xf2f2_f2f2,
        5 => 0x6b6b_6b6b,
        6 => 0x6f6f_6f6f,
        _ => 0xc5c5_c5c5,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_match_jump_table(secret_nibble: u8, x: u64) -> u64 {
    match secret_nibble & 7 {
        0 => x.wrapping_mul(3).wrapping_add(1),
        1 => x.rotate_left(7) ^ 0x5555_5555,
        2 => x.wrapping_add(x >> 3).wrapping_mul(11),
        3 => (x ^ 0xdead_beef).rotate_right(13),
        4 => x.wrapping_sub(0x1234).wrapping_mul(0x10001),
        5 => (x.wrapping_mul(17) ^ (x >> 5)).wrapping_add(9),
        6 => x.rotate_left(29).wrapping_add(0xcafe_babe),
        _ => (x >> 1) ^ x.wrapping_mul(0x9e37_79b9),
    }
}

// ============================================================================
// 6. black_box barriers: protection vs. sideeffect-induced branches & div
// ============================================================================

#[unsafe(no_mangle)]
pub extern "C" fn ct_black_box_short_circuit_and(c1: bool, c2: bool, a: u64, b: u64) -> u64 {
    let cond = black_box(c1) && black_box(c2);
    let m = (cond as u64).wrapping_neg();
    (m & a) | (!m & b)
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_black_box_div_still_var_time(a: u64, d: u64) -> u64 {
    black_box(a) / (black_box(d) | 1)
}

// ============================================================================
// 7. Variable-latency DIV/IDIV/UDIV & subnormal FP hazards
// ============================================================================

#[unsafe(no_mangle)]
pub extern "C" fn ct_const_div_kyberslash(a: u32) -> u32 {
    (a.wrapping_mul(2).wrapping_add(3329)) / 6658
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_secret_div_u64(a: u64, d: u64) -> u64 {
    a / (d | 1)
}

#[unsafe(no_mangle)]
pub extern "C" fn ct_subnormal_fp_mul(a: f64, b: f64) -> f64 {
    a * b + 1.0
}
