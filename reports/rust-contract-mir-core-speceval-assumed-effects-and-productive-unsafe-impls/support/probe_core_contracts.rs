#![feature(contracts)]
#![allow(unused)]

use core::cell::{Cell, UnsafeCell};
use core::contracts::{ensures, requires};

#[requires(*x > 0)]
pub fn f_shared_ref(x: &u32) -> u32 {
    *x - 1
}

#[requires(*x > 0)]
pub fn f_mut_ref(x: &mut u32) -> u32 {
    *x -= 1;
    *x
}

#[requires(x.get() > 0)]
pub fn f_cell_read(x: &Cell<u32>) -> u32 {
    x.get() - 1
}

#[requires({ x.set(99); true })]
pub fn f_cell_mutates(x: &Cell<u32>) -> u32 {
    x.get()
}

#[requires(unsafe { *x.get() > 0 })]
pub unsafe fn f_unsafe_cell(x: &UnsafeCell<u32>) -> u32 {
    unsafe { *x.get() - 1 }
}

#[requires({ let b = Box::new(x); *b > 0 })]
pub fn f_alloc_in_req(x: u32) -> u32 {
    x - 1
}

#[requires(a / b > 0 && a + b < 100)]
pub fn f_panic_overflow_in_req(a: u32, b: u32) -> u32 {
    a + b
}

#[requires(x < 100)]
#[ensures(move |r| *r == x + 1)]
pub fn f_mut_param_ensures(mut x: u32) -> u32 {
    x += 1;
    x
}

#[ensures(move |r| *r >= x)]
pub fn f_early_ret(x: u32) -> u32 {
    if x == 0 {
        return 1;
    }
    x
}
