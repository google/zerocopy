#![feature(thread_local)]
#![allow(dead_code)]

use std::cell::Cell;

#[thread_local]
#[no_mangle]
pub static TLS_MODEL_A: Cell<u64> = Cell::new(0x0102_0304_0506_0708);

#[thread_local]
#[no_mangle]
pub static TLS_MODEL_B: Cell<u64> = Cell::new(0);

#[no_mangle]
#[inline(never)]
pub extern "C" fn read_tls_pair() -> u64 {
    let a = TLS_MODEL_A.get();
    let b = TLS_MODEL_B.get();
    TLS_MODEL_B.set(b + 3);
    a.wrapping_add(b)
}

#[cfg(not(feature_cdylib))]
fn main() {
    let r1 = read_tls_pair();
    let r2 = read_tls_pair();
    println!("TLS_MODEL_OK r1=0x{:x} r2=0x{:x}", r1, r2);
    assert_eq!(r1, 0x0102_0304_0506_0708);
    assert_eq!(r2, 0x0102_0304_0506_070b);
}
