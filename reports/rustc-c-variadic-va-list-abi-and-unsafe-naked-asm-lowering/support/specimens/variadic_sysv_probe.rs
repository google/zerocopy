#![allow(stable_features)]
#![feature(c_variadic)]

use core::ffi::VaList;

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn rust_vsum_indirect_valist(tag_count: usize, mut ap: VaList<'_>) -> u64 {
    let kind = tag_count & 0xff;
    match kind {
        0 => {
            let a = unsafe { ap.next_arg::<u64>() };
            let b = unsafe { ap.next_arg::<u64>() };
            a + b
        }
        1 => {
            // Reads 6 GP arguments (including fixed `tag_count` => 5 variadic GP args in regs
            // plus 1 variadic GP overflow slot on stack) and 2 XMM f64 arguments.
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
        }
        2 => {
            let mut sum: u64 = 0;
            for _ in 0..9 {
                sum += (unsafe { ap.next_arg::<f64>() }) as u64;
            }
            sum
        }
        _ => 0,
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn rust_variadic_mixed(tag_count: usize, ap: ...) -> u64 {
    unsafe { rust_vsum_indirect_valist(tag_count, ap) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn call_zero_floats() -> u64 {
    unsafe { rust_variadic_mixed(0, 100u64, 100u64) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn call_two_floats_and_overflow() -> u64 {
    // 1 fixed GP + 6 variadic GP args => 7th GP arg (1000u64) overflows to caller stack!
    // Plus 2 variadic f64 args => caller sets %al = 2 (`movb $2, %al`).
    unsafe { rust_variadic_mixed(1, 10i32, 20.0f64, 30i32, 40u64, 50.0f64, 60u64, 10u64, 1000u64) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn call_nine_floats() -> u64 {
    // 9 variadic f64 args => %xmm0..%xmm7 filled (%al = 8) + 9th f64 pushed onto stack.
    unsafe { rust_variadic_mixed(2, 1.0f64, 2.0f64, 3.0f64, 4.0f64, 5.0f64, 6.0f64, 7.0f64, 8.0f64, 9.0f64) }
}

fn main() {
    let z = call_zero_floats();
    let m = call_two_floats_and_overflow();
    let nf = call_nine_floats();
    let sz = core::mem::size_of::<VaList<'_>>();
    let al = core::mem::align_of::<VaList<'_>>();
    println!("ZERO_FP={z} MIXED_OVERFLOW={m} NINE_FP={nf} VALIST_SZ={sz} VALIST_ALIGN={al}");
}
