#![allow(stable_features)]
#![feature(c_variadic)]

use core::ffi::VaList;

unsafe extern "C" {
    fn c_vsum_takes_valist(count: usize, ap: VaList<'_>) -> u64;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rust_vsum_indirect_valist(tag_count: usize, mut ap: VaList<'_>) -> u64 {
    let kind = tag_count & 0xff;
    if kind == 1 {
        let mut sum: u64 = 0;
        sum += unsafe { ap.next_arg::<i32>() } as u64;
        sum += (unsafe { ap.next_arg::<f64>() }) as u64;
        sum += unsafe { ap.next_arg::<i32>() } as u64;
        sum += unsafe { ap.next_arg::<u64>() };
        sum += (unsafe { ap.next_arg::<f64>() }) as u64;
        sum += unsafe { ap.next_arg::<u64>() };
        sum += unsafe { ap.next_arg::<u64>() };
        sum += unsafe { ap.next_arg::<u64>() };
        sum
    } else {
        0
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rust_variadic_mixed(tag_count: usize, ap: ...) -> u64 {
    unsafe { rust_vsum_indirect_valist(tag_count, ap) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rust_calls_c_valist_twice(count: usize, mut ap: ...) -> u64 {
    let c_sum = unsafe { c_vsum_takes_valist(count, ap.clone()) };
    let r_first = unsafe { ap.next_arg::<u64>() };
    c_sum * 1000 + r_first
}
