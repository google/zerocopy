//! Standalone `#![no_core]` Miri probe templates (selected via `--cfg ...`).

#![feature(no_core, lang_items, auto_traits)]
#![allow(internal_features, dead_code, unused_variables, unreachable_code)]
#![no_core]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
#[lang = "freeze"]
pub auto trait Freeze {}
#[lang = "unpin"]
pub auto trait Unpin {}
#[lang = "unsafe_unpin"]
pub trait UnsafeUnpin {}
#[lang = "drop_glue"]
#[allow(unconditional_recursion)]
pub unsafe fn drop_glue<T: ?Sized>(_: *mut T) {}

impl Copy for u8 {}
impl Copy for usize {}
impl Copy for bool {}
impl Copy for isize {}
impl<T: ?Sized> Copy for *const T {}
impl<T: ?Sized> Copy for *mut T {}

enum OptBool {
    None,
    Some(bool),
}

enum Void {}

#[lang = "start"]
fn start<T>(_main: fn() -> T, _argc: isize, _argv: *const *const u8, _sigpipe: u8) -> isize {
    _main();
    0
}

#[cfg(case = "place_mention_invalid_bool")]
fn main() {
    let raw: u8 = 2;
    let p: *const bool = &raw as *const u8 as *const bool;
    unsafe {
        let _ = *p;
    }
}

#[cfg(case = "wildcard_match_invalid_bool")]
fn main() {
    let raw: u8 = 2;
    let p: *const bool = &raw as *const u8 as *const bool;
    unsafe {
        match *p {
            _ => (),
        }
    }
}

#[cfg(case = "let_named_invalid_bool")]
fn main() {
    let raw: u8 = 2;
    let p: *const bool = &raw as *const u8 as *const bool;
    unsafe {
        let _named = *p;
    }
}

#[cfg(case = "place_mention_dangling_thin_ptr")]
fn main() {
    let dangling: *const bool = 4usize as *const bool;
    unsafe {
        let _ = *dangling;
    }
}

#[cfg(case = "place_mention_uninit_double_ptr")]
fn main() {
    #[repr(C)]
    union UninitSlot {
        unit: (),
        ptr: *const bool,
    }
    let slot = UninitSlot { unit: () };
    let pp: *const *const bool = &slot as *const UninitSlot as *const *const bool;
    unsafe {
        let _ = **pp;
    }
}

#[cfg(case = "match_guard_raw_ptr_mutation")]
fn main() {
    let mut x = OptBool::Some(false);
    let p: *mut OptBool = &mut x;
    let _r = match x {
        OptBool::None => 0u8,
        OptBool::Some(true) => 1u8,
        OptBool::Some(_) if {
            unsafe {
                *p = OptBool::None;
            }
            false
        } => 2u8,
        OptBool::Some(false) => 3u8,
    };
}

#[cfg(case = "empty_match_raw_ptr_void")]
fn main() {
    let raw: u8 = 0;
    let p: *const Void = &raw as *const u8 as *const Void;
    unsafe {
        match *p {}
    }
}
