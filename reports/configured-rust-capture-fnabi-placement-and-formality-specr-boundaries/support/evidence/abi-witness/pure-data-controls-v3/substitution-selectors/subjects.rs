// PROPOSED E33 fixture. Not compiled or executed during preparation.
// All defined functions use valid typed values. Foreign calls are compile-only;
// their unresolved callees have no native-run authorization in this plan.
#![no_std]
#![allow(dead_code)]
use core::cell::UnsafeCell;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Pair { pub a: u64, pub b: u32 }
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Big { pub words: [u64; 3] }
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Hfa { pub a: f32, pub b: f32, pub c: f32, pub d: f32 }

#[no_mangle]
#[inline(never)]
pub extern "C" fn abi_c_narrow(x: u8, y: i16, flag: bool) -> u64 {
    (x as u64) ^ (y as i64 as u64) ^ (flag as u64)
}
#[no_mangle]
#[inline(never)]
pub extern "system" fn abi_system_narrow(x: u8, y: i16, flag: bool) -> u64 {
    (x as u64) ^ (y as i64 as u64) ^ (flag as u64)
}
#[no_mangle]
#[inline(never)]
pub fn abi_rust_narrow(x: u8, y: i16, flag: bool) -> u64 {
    (x as u64) ^ (y as i64 as u64) ^ (flag as u64)
}
#[no_mangle]
#[inline(never)]
pub extern "C" fn abi_c_pair(x: Pair) -> Pair { x }
#[no_mangle]
#[inline(never)]
pub extern "system" fn abi_system_pair(x: Pair) -> Pair { x }
#[no_mangle]
#[inline(never)]
pub fn abi_rust_tuple(x: (u64, u32)) -> (u64, u32) { x }
#[no_mangle]
#[inline(never)]
pub extern "C" fn abi_c_big(x: Big) -> Big { x }
#[no_mangle]
#[inline(never)]
pub extern "system" fn abi_system_big(x: Big) -> Big { x }
#[no_mangle]
#[inline(never)]
pub fn abi_rust_big(x: Big) -> Big { x }
#[no_mangle]
#[inline(never)]
pub extern "C" fn abi_c_hfa(x: Hfa) -> Hfa { x }
#[no_mangle]
#[inline(never)]
pub extern "C" fn abi_c_fp(x: f32, y: f64) -> f64 { (x as f64) + y }
#[no_mangle]
#[inline(never)]
pub extern "C" fn abi_c_raw(x: *const u64) -> *const u64 { x }
#[no_mangle]
#[inline(never)]
pub fn abi_shared(x: &u64) -> u64 { *x }
#[no_mangle]
#[inline(never)]
pub fn abi_unique(x: &mut u64) -> u64 { *x = (*x).wrapping_add(1); *x }
#[no_mangle]
#[inline(never)]
pub fn abi_interior(x: &UnsafeCell<u64>) -> *mut u64 { x.get() }
#[no_mangle]
#[inline(never)]
pub fn abi_slice(x: &[u8]) -> usize { x.len() }
#[no_mangle]
#[inline(never)]
pub fn abi_unit(_: ()) { }
#[no_mangle]
#[inline(never)]
#[track_caller]
pub fn abi_track(x: u64) -> u64 { x ^ (core::panic::Location::caller().line() as u64) }
#[inline(never)]
pub fn generic_id<T>(x: T) -> T { x }

pub type TrackFn = fn(u64) -> u64;
pub type VarC = unsafe extern "C" fn(i32, ...) -> u64;
pub type VarSystem = unsafe extern "system" fn(i32, ...) -> u64;

extern "C" {
    fn abi_opaque_twelve(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64,
                         g: u64, h: u64, i: u64, j: u64, k: u64, l: u64) -> u64;
    fn abi_opaque_vararg(tag: i32, ...) -> u64;
}

// Compile-only caller/callee placement observation. The extra computation prevents
// a direct tail-call replacement; actual generated output still needs inspection.
// Safety: a future caller must supply implementations of both opaque foreign
// functions obeying these exact C signatures and the declared call contract.
#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn abi_stack_driver(a: u64, b: u64, c: u64, d: u64,
    e: u64, f: u64, g: u64, h: u64, i: u64, j: u64, k: u64, l: u64) -> u64 {
    unsafe { abi_opaque_twelve(a,b,c,d,e,f,g,h,i,j,k,l).wrapping_add(1) }
}
// This source is never authorized for native execution by the preparation plan.
// Variadic inputs have already undergone the required promotions (i32/f64).
#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn abi_vararg_driver(x: i32, y: f64) -> u64 {
    unsafe { abi_opaque_vararg(1_i32, x, y, core::ptr::null::<u8>()).wrapping_add(1) }
}
