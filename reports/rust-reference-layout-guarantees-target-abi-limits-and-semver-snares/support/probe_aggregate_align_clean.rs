#![feature(no_core, lang_items, auto_traits)]
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
#[lang = "freeze"]
pub unsafe auto trait Freeze {}

#[repr(C)]
pub struct ReprCU8(pub u8);

#[repr(transparent)]
pub struct TransU8(pub u8);

#[repr(C, packed)]
pub struct PackedReprCU8(pub u8);

pub extern "C" fn take_all(a: ReprCU8, _b: TransU8, _c: PackedReprCU8) -> u8 {
    a.0
}
