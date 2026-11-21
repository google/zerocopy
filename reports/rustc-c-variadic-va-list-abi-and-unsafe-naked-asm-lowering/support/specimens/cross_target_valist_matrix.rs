#![no_std]
#![allow(stable_features)]
#![feature(c_variadic)]

use core::ffi::VaList;

#[unsafe(no_mangle)]
pub extern "C" fn valist_size() -> usize {
    core::mem::size_of::<VaList<'_>>()
}

#[unsafe(no_mangle)]
pub extern "C" fn valist_align() -> usize {
    core::mem::align_of::<VaList<'_>>()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn takes_valist_reads_i32_f64(mut ap: VaList<'_>) -> u64 {
    let a = unsafe { ap.next_arg::<i32>() } as u64;
    let b = (unsafe { ap.next_arg::<f64>() }) as u64;
    a + b
}
