#![feature(f16, f128, never_type)]
#![allow(dead_code)]

extern crate alloc;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use core::alloc::Layout;
use core::cell::{Cell, UnsafeCell};
use core::cmp::Ordering;
use core::mem::MaybeUninit;
use core::num::{NonZeroU8, NonZeroU32, NonZeroU64, NonZeroU128};
use core::ptr::NonNull;
use core::time::Duration;

pub struct ReprRustStruct {
    pub a: u8,
    pub b: u32,
    pub c: u16,
    pub d: u8,
}

#[repr(C)]
pub struct ReprCStruct {
    pub a: u8,
    pub b: u32,
    pub c: u16,
    pub d: u8,
}

#[repr(C, packed(1))]
pub struct ReprPacked1Struct {
    pub a: u8,
    pub b: u32,
    pub c: u16,
}

#[repr(C, packed(2))]
pub struct ReprPacked2Struct {
    pub a: u8,
    pub b: u32,
    pub c: u16,
}

#[repr(C, align(16))]
pub struct ReprAlign16Struct {
    pub a: u32,
}

#[repr(align(8))]
pub struct Align8Zst;

#[repr(transparent)]
pub struct TransparentWith1Zst {
    pub zst: (),
    pub inner: NonZeroU32,
}

pub struct NewtypeWithAlign8Zst {
    pub zst: Align8Zst,
    pub inner: u32,
}

#[repr(C)]
pub struct I64AlignProbe {
    pub tag: u8,
    pub val: i64,
}

#[repr(C)]
pub struct F64AlignProbe {
    pub tag: u8,
    pub val: f64,
}

#[repr(C)]
pub struct I128AlignProbe {
    pub tag: u8,
    pub val: i128,
}

#[repr(C)]
pub struct F128AlignProbe {
    pub tag: u8,
    pub val: f128,
}

pub struct MultiNicheStruct {
    pub a: bool,
    pub b: NonZeroU32,
    pub c: char,
}

pub enum NicheEnum {
    V1(NonZeroU32),
    V2,
    V3,
}

pub enum DirectTagScalarPairEnum {
    A(u32),
    B(i32),
    C,
}

pub enum DirectTagMemoryEnum {
    A(u64, u64),
    B(u32),
    C,
}

#[repr(C)]
pub enum ReprCEnum {
    A(u32),
    B(u64),
}

#[repr(u8)]
pub enum ReprU8WithPayload {
    A(u32) = 1,
    B(u64) = 2,
}

pub union ScalarUnion {
    pub a: u32,
    pub b: NonZeroU32,
    pub c: i32,
}

pub union MixedAbiUnion {
    pub a: u32,
    pub b: (u16, u16),
}


pub enum NicheCharEnum {
    V1(char),
    V2,
    V3,
}

pub union SameSignScalarUnion {
    pub a: u32,
    pub b: NonZeroU32,
}

pub struct ProbeCatalog {
    pub e_niche_char: NicheCharEnum,
    pub u_same_sign_scalar: SameSignScalarUnion,
    pub p_bool: bool,
    pub p_char: char,
    pub p_i8: i8,
    pub p_i16: i16,
    pub p_i32: i32,
    pub p_i64: i64,
    pub p_i128: i128,
    pub p_isize: isize,
    pub p_u64: u64,
    pub p_u128: u128,
    pub p_usize: usize,
    pub p_f16: f16,
    pub p_f32: f32,
    pub p_f64: f64,
    pub p_f128: f128,
    pub p_unit: (),
    pub p_opt_bool: Option<bool>,
    pub p_opt_opt_bool: Option<Option<bool>>,
    pub p_opt_char: Option<char>,
    pub p_opt_ref_u8: Option<&'static u8>,
    pub p_opt_nonnull: Option<NonNull<u8>>,
    pub p_opt_nzu32: Option<NonZeroU32>,
    pub p_opt_nzu128: Option<NonZeroU128>,
    pub p_res_u32_u32: Result<u32, u32>,
    pub p_res_nonnull_unit: Result<NonNull<u8>, ()>,
    pub p_box_u64: Box<u64>,
    pub p_box_slice: Box<[u8]>,
    pub p_slice_ref: &'static [u8],
    pub p_dyn_debug: &'static dyn core::fmt::Debug,
    pub p_vec_u8: Vec<u8>,
    pub p_string: String,
    pub p_cell_u64: Cell<u64>,
    pub p_unsafecell_u64: UnsafeCell<u64>,
    pub p_maybeuninit_nzu32: MaybeUninit<NonZeroU32>,
    pub p_ordering: Ordering,
    pub p_duration: Duration,
    pub p_layout: Layout,
    pub s_repr_rust: ReprRustStruct,
    pub s_repr_c: ReprCStruct,
    pub s_packed1: ReprPacked1Struct,
    pub s_packed2: ReprPacked2Struct,
    pub s_align16: ReprAlign16Struct,
    pub s_trans_1zst: TransparentWith1Zst,
    pub s_trans_align8zst: NewtypeWithAlign8Zst,
    pub s_i64_align: I64AlignProbe,
    pub s_f64_align: F64AlignProbe,
    pub s_i128_align: I128AlignProbe,
    pub s_f128_align: F128AlignProbe,
    pub s_multi_niche: MultiNicheStruct,
    pub e_niche: NicheEnum,
    pub e_direct_sp: DirectTagScalarPairEnum,
    pub e_direct_mem: DirectTagMemoryEnum,
    pub e_repr_c: ReprCEnum,
    pub e_repr_u8: ReprU8WithPayload,
    pub u_scalar: ScalarUnion,
    pub u_mixed: MixedAbiUnion,
}
