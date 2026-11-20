//! Compile-time layout assertions for targets with `c_enum_min_bits = Some(8)`
//! (e.g. `thumbv7m-none-eabi`, `hexagon-unknown-none-elf`), using `#![no_core]` so
//! metadata emission runs without needing a pre-installed target `libcore`.
//!
//! Run:
//!   rustc --edition 2021 --crate-type lib --target thumbv7m-none-eabi --emit=metadata -o /tmp/t.rmeta support/crosscheck_short_enum.rs
//!   rustc --edition 2021 --crate-type lib --target hexagon-unknown-none-elf --emit=metadata -o /tmp/h.rmeta support/crosscheck_short_enum.rs

#![feature(no_core, lang_items, intrinsics)]
#![no_core]
#![allow(internal_features, dead_code)]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}

#[rustc_intrinsic]
const fn size_of<T>() -> usize;
#[rustc_intrinsic]
const fn align_of<T>() -> usize;

#[repr(C)]
pub enum FieldlessC {
    A,
    B,
}

#[repr(C)]
pub enum FieldlessC256 {
    A = 256,
    B,
}

#[repr(C)]
pub enum EnumC {
    Variant0(u8),
    Variant1,
}

// On targets with c_enum_min_bits = 8 (thumbv7m-none-eabi, hexagon-unknown-none-elf):
// small discriminants [0, 1] yield a 1-byte tag (despite 4-byte c_int), while
// discriminants [256, 257] require a 2-byte tag.
const _: [(); 1] = [(); size_of::<FieldlessC>()];
const _: [(); 1] = [(); align_of::<FieldlessC>()];
const _: [(); 2] = [(); size_of::<FieldlessC256>()];
const _: [(); 2] = [(); align_of::<FieldlessC256>()];
const _: [(); 2] = [(); size_of::<EnumC>()];
const _: [(); 1] = [(); align_of::<EnumC>()];
