// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(dead_code, unconditional_panic, unused_variables)]

use core::cell::Cell;
use core::marker::PhantomData;
use core::num::NonZeroU64;

// ============================================================================
// Domain Types (eBPF Verifier / Anneal Representative Shapes)
// ============================================================================

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EbpfInstruction(pub u64);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct U64Range {
    pub min: u64,
    pub max: u64,
}

impl U64Range {
    pub const ALL: Self = Self { min: 0, max: u64::MAX };
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct U64ScalarValueData {
    pub unsigned_range: U64Range,
    pub signed_range: U64Range,
    pub known_mask: u64,
    pub known_bits: u64,
}

impl U64ScalarValueData {
    pub const UNINITIALIZED: Self = Self {
        unsigned_range: U64Range::ALL,
        signed_range: U64Range {
            min: i64::MIN as u64,
            max: i64::MAX as u64,
        },
        known_mask: 0,
        known_bits: 0,
    };
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Marker;

#[repr(i8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SimpleEnum {
    Neg = -1,
    Zero = 0,
    Pos = 1,
}

#[derive(Copy, Clone, Debug)]
pub struct NestedRefs<'a> {
    pub label: &'a str,
    pub nums: &'a [u32; 2],
    pub range: &'a U64Range,
}

pub static STATIC_U32: u32 = 0xCAFE_BABE;

pub fn sample_helper_fn(x: u32) -> u32 {
    x + 1
}

// ============================================================================
// Part 1: required_consts, Const::Unevaluated, and ErrorHandled
// ============================================================================

pub struct Fail<T>(PhantomData<T>);

impl<T> Fail<T> {
    pub const UNCOND_FAIL: usize = 1 / 0;
    pub const SIZE_CHECK: () = assert!(core::mem::size_of::<T>() <= 4);
}

pub trait AssocConstTrait {
    const TRAIT_C: usize;
}

pub fn part1_unreachable_if_false_panic() {
    if false {
        let _ = const { panic!("dead if false") };
    }
}

pub fn part1_unreachable_if_false_div_zero() -> usize {
    if false {
        const { 1 / 0 }
    } else {
        42
    }
}

pub fn part1_match_false_deleted_bb_div_zero() -> usize {
    match false {
        true => const { 1 / 0 },
        false => 42,
    }
}

pub fn part1_promoted_if_false_div_zero() {
    if false {
        let _r: &'static usize = &const { 1 / 0 };
    }
}

pub fn part1_post_return_div_zero() {
    return;
    let _ = const { 1 / 0 };
}

pub fn part1_generic_mention_uncond_fail<T>() -> usize {
    Fail::<T>::UNCOND_FAIL
}

pub fn part1_generic_mention_size_check<T>() {
    let () = Fail::<T>::SIZE_CHECK;
}

pub fn part1_generic_mention_trait_const<T: AssocConstTrait>() -> usize {
    <T as AssocConstTrait>::TRAIT_C
}

pub fn part1_concrete_size_check_u32_ok() {
    let () = Fail::<u32>::SIZE_CHECK;
}

pub fn part1_concrete_size_check_u64_err() {
    let () = Fail::<u64>::SIZE_CHECK;
}

pub fn part1_reachable_inline_div_zero() -> usize {
    const { 1 / 0 }
}

// ============================================================================
// Part 2: 20+ Representative Constant Shapes (ConstValue vs ValTree vs Decoder)
// ============================================================================

pub const C_01_PRIM_U64: u64 = 0x1234_5678_9ABC_DEF0;
pub const C_02_PRIM_I32_NEG: i32 = -42;
pub const C_03_NEWTYPE_EBPF_INSN: EbpfInstruction = EbpfInstruction(0x0700_0000_0000_0095);
pub const C_04_STRUCT_U64_RANGE: U64Range = U64Range::ALL;
pub const C_05_TUPLE_PADDED: (u8, u32) = (0xAA, 0x1122_3344);
pub const C_06_NESTED_SCALAR_DATA: U64ScalarValueData = U64ScalarValueData::UNINITIALIZED;
pub const C_07_ARRAY_U32: [u32; 4] = [10, 20, 30, 40];
pub const C_08_ZST_UNIT: () = ();
pub const C_09_ZST_EMPTY_ARRAY: [u8; 0] = [];
pub const C_10_ZST_STRUCT: Marker = Marker;
pub const C_11_ENUM_FIELDLESS_NEG: SimpleEnum = SimpleEnum::Neg;
pub const C_12_NICHE_OPT_BOOL_NONE: Option<bool> = None;
pub const C_13_NICHE_OPT_BOOL_SOME: Option<bool> = Some(true);
pub const C_14_NICHE_OPT_NZ_NONE: Option<NonZeroU64> = None;
pub const C_15_NICHE_OPT_NZ_SOME: Option<NonZeroU64> = NonZeroU64::new(99);
pub const C_16_DIRECT_OPT_U64_NONE: Option<u64> = None;
pub const C_17_DIRECT_OPT_U64_SOME: Option<u64> = Some(0xDEAD_BEEF);
pub const C_18_DIRECT_RESULT_OK: Result<u32, u8> = Ok(0x1234_5678);
pub const C_19_DIRECT_RESULT_ERR: Result<u32, u8> = Err(0xFF);
pub const C_20_SLICE_STR_TRIVIAL: &str = "ebpf_verifier";
pub const C_21_SLICE_STR_COMPUTED: &str = {
    let s = "computed_str";
    s
};
pub const C_22_SLICE_U8_COERCED: &[u8] = &[10, 20, 30];
pub const C_23_REF_SCALAR_U32: &u32 = &0;
pub const C_24_REF_ARRAY_U32: &[u32; 3] = &[1, 2, 3];
pub const C_25_REF_U64_RANGE: &U64Range = &U64Range { min: 1, max: 2 };
pub const C_26_NESTED_REFS: NestedRefs<'static> = NestedRefs {
    label: "r0",
    nums: &[100, 200],
    range: &U64Range { min: 0, max: 255 },
};
pub const C_27_RAW_PTR_INT_CAST: *const u8 = 0x1000usize as *const u8;
pub const C_28_RAW_PTR_STATIC_PROV: *const u32 = &raw const STATIC_U32;
pub const C_29_FN_PTR: fn(u32) -> u32 = sample_helper_fn;

// ============================================================================
// Part 3: Constant Promotion (PromoteTemps, promoted[N])
// ============================================================================

pub struct NeedsDropType(pub u32);
impl Drop for NeedsDropType {
    fn drop(&mut self) {}
}

pub const fn normal_const_fn() -> u32 {
    77
}

pub const fn panicking_const_fn() -> u32 {
    panic!("should not be promoted in dead branch")
}

pub fn promo_accepted_candidates() -> (
    &'static u32,
    &'static EbpfInstruction,
    &'static U64Range,
    &'static U64ScalarValueData,
    &'static [u32; 3],
    &'static mut [u32; 0],
    &'static u32,
) {
    (
        &0u32,
        &EbpfInstruction(7),
        &U64Range { min: 0, max: 1 },
        &U64ScalarValueData::UNINITIALIZED,
        &[1u32, 2, 3],
        &mut [],
        &((10u32 / 2u32) + 3u32),
    )
}

pub fn promo_assert_eq(a: u32) {
    assert_eq!(a, 0u32);
}

pub fn promo_rejected_candidates(runtime_x: u32) -> u32 {
    // 1. Division by zero or runtime variable: not promoted
    let r_div_var = &(runtime_x / 2u32);
    // 2. Checked arithmetic call (not #[rustc_promotable] in normal fn): not promoted
    let r_call = &normal_const_fn();
    // 3. Mutable borrow of non-empty-array: not promoted
    let r_mut = &mut 0u32;
    // 4. Shared borrow of interior-mutable Cell: not promoted
    let r_cell = &Cell::new(0u32);
    // 5. Shared borrow of Drop type: not promoted
    let r_drop = &NeedsDropType(0u32);

    *r_div_var + *r_call + *r_mut + r_cell.get() + r_drop.0
}

pub const PROMO_IN_CONST_CALL: &u32 = &normal_const_fn();
pub static PROMO_IN_STATIC_CALL: &u32 = &normal_const_fn();
pub const PROMO_IN_CONST_DEAD_BRANCH: u32 = {
    if false {
        let _ = &panicking_const_fn();
    }
    0
};

pub fn promo_generic_independent<T>(_x: PhantomData<T>) -> &'static U64Range {
    &U64Range { min: 10, max: 20 }
}

pub fn promo_generic_array_dependent<const N: usize>() -> &'static [u8; N] {
    &[0u8; N]
}

pub fn promo_generic_size_of_dependent<T>() -> &'static usize {
    &core::mem::size_of::<T>()
}
