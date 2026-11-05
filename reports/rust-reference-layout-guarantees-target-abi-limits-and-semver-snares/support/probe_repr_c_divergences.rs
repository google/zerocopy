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
#[lang = "freeze"]
pub unsafe auto trait Freeze {}

#[lang = "neg"]
pub trait Neg {
    type Output;
    fn neg(self) -> Self::Output;
}
impl Neg for isize {
    type Output = isize;
    fn neg(self) -> isize { self }
}

#[repr(C)]
pub struct Empty {}

#[repr(C)]
pub struct WithUnit {
    pub a: u8,
    pub u: (),
    pub b: u8,
}

#[repr(C)]
pub struct WithAlignedZst {
    pub a: u8,
    pub zst: [u64; 0],
    pub b: u8,
}

#[repr(C)]
pub struct WithU64 {
    pub a: u8,
    pub b: u64,
}

#[repr(C)]
pub struct WithF64 {
    pub a: u8,
    pub b: f64,
}

#[repr(C)]
pub struct AixFloats {
    pub a: f64,
    pub b: u8,
    pub c: f64,
}

#[repr(C)]
pub struct WithU128 {
    pub a: u8,
    pub b: u128,
}

#[repr(C)]
pub enum CEnumSmall {
    A = 0,
    B = 1,
}

#[repr(C)]
pub enum CEnumNeg {
    A = -1,
    B = 1,
}

#[repr(C)]
pub struct WrapU64(pub u64);

#[repr(transparent)]
pub struct TransU64(pub u64);

#[repr(C)]
pub struct TwoU32(pub u32, pub u32);

#[repr(C)]
pub struct TwoF32(pub f32, pub f32);

pub extern "C" fn touch(
    _e: Empty,
    _wu: WithUnit,
    _wz: WithAlignedZst,
    _u64s: WithU64,
    _f64s: WithF64,
    _aix: AixFloats,
    _u128s: WithU128,
    _es: CEnumSmall,
    _en: CEnumNeg,
    _w: WrapU64,
    _t: TransU64,
    _tu: TwoU32,
    _tf: TwoF32,
) {}
