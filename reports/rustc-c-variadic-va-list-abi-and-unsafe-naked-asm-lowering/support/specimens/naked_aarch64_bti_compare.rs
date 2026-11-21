#![no_std]
use core::arch::naked_asm;

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn normal_add1(x: u64) -> u64 {
    x.wrapping_add(1)
}

#[unsafe(no_mangle)]
#[unsafe(naked)]
pub extern "C" fn naked_add1(_x: u64) -> u64 {
    naked_asm!("add x0, x0, #1", "ret")
}
