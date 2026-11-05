#![feature(no_core, lang_items)]
#![no_core]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}

#[repr(C)]
pub enum CEnum {
    A = 0,
    B = 1,
}

pub fn use_enum(x: CEnum) -> CEnum {
    x
}
