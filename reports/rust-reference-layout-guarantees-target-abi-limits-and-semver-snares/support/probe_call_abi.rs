#![feature(no_core, lang_items, auto_traits, rustc_attrs)]
#![no_core]
#![allow(dead_code, improper_ctypes_definitions)]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}

#[repr(C)]
pub struct WrapU64(pub u64);

#[repr(transparent)]
pub struct TransU64(pub u64);

#[repr(C, align(8))]
pub struct AlignedTwoF32(pub f32, pub f32);

#[repr(C)]
pub struct WrapF32(pub f32);

#[rustc_abi(debug)]
pub type FnU64 = extern "C" fn(u64) -> u64;

#[rustc_abi(debug)]
pub type FnWrapU64 = extern "C" fn(WrapU64) -> WrapU64;

#[rustc_abi(debug)]
pub type FnTransU64 = extern "C" fn(TransU64) -> TransU64;

#[rustc_abi(debug)]
pub type FnAlignedTwoF32 = extern "C" fn(AlignedTwoF32) -> AlignedTwoF32;

#[rustc_abi(debug)]
pub type FnF32 = extern "C" fn(f32) -> f32;

#[rustc_abi(debug)]
pub type FnWrapF32 = extern "C" fn(WrapF32) -> WrapF32;
