#![feature(thread_local)]
#![allow(dead_code, static_mut_refs)]

use std::cell::Cell;
use std::sync::atomic::{AtomicU64, Ordering};

#[no_mangle]
pub static IMMUT_SCALAR_STATIC: [u8; 64] = [0x42; 64];

#[no_mangle]
pub static ZERO_IMMUT_STATIC: [u8; 64] = [0; 64];

#[repr(C)]
pub struct RelroEntry {
    pub tag: u64,
    pub bytes: &'static [u8; 64],
    pub callback: fn() -> u64,
}

#[inline(never)]
fn relro_cb() -> u64 {
    0xCAFE_BABE_1234_5678
}

#[no_mangle]
pub static RELRO_PTR_STATIC: RelroEntry = RelroEntry {
    tag: 0x5245_4C52_4F00_0001,
    bytes: &IMMUT_SCALAR_STATIC,
    callback: relro_cb,
};

#[no_mangle]
pub static MUT_NONZERO_STATIC: AtomicU64 = AtomicU64::new(0x1122_3344_5566_7788);

#[no_mangle]
pub static MUT_ZERO_STATIC: AtomicU64 = AtomicU64::new(0);

#[thread_local]
#[no_mangle]
pub static TLS_NONZERO_CELL: Cell<u64> = Cell::new(0xDEAD_BEEF_CAFE_BABE);

#[thread_local]
#[no_mangle]
pub static TLS_ZERO_CELL: Cell<u64> = Cell::new(0);

#[thread_local]
#[no_mangle]
pub static TLS_ZERO_FREEZE: u64 = 0;

#[inline(never)]
pub fn promoted_rvalue_ref() -> &'static [u8; 32] {
    &[0x99u8; 32]
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "normal".to_string());
    let ro_addr = (&raw const IMMUT_SCALAR_STATIC) as usize;
    let zero_immut_addr = (&raw const ZERO_IMMUT_STATIC) as usize;
    let relro_addr = (&raw const RELRO_PTR_STATIC) as usize;
    let data_addr = (&raw const MUT_NONZERO_STATIC) as usize;
    let bss_addr = (&raw const MUT_ZERO_STATIC) as usize;
    let promo = promoted_rvalue_ref();

    assert_eq!(IMMUT_SCALAR_STATIC[0], 0x42);
    assert_eq!(ZERO_IMMUT_STATIC[63], 0);
    assert_eq!(RELRO_PTR_STATIC.tag, 0x5245_4C52_4F00_0001);
    assert_eq!(RELRO_PTR_STATIC.bytes.as_ptr() as usize, ro_addr);
    assert_eq!((RELRO_PTR_STATIC.callback)(), 0xCAFE_BABE_1234_5678);
    assert_eq!(promo[0], 0x99);
    assert_eq!(TLS_NONZERO_CELL.get(), 0xDEAD_BEEF_CAFE_BABE);
    assert_eq!(TLS_ZERO_CELL.get(), 0);
    assert_eq!(TLS_ZERO_FREEZE, 0);

    MUT_ZERO_STATIC.store(0xABCD, Ordering::SeqCst);
    assert_eq!(MUT_ZERO_STATIC.load(Ordering::SeqCst), 0xABCD);
    assert_eq!(MUT_NONZERO_STATIC.fetch_add(1, Ordering::SeqCst), 0x1122_3344_5566_7788);

    println!(
        "NORMAL_OK ro_addr=0x{:x} zero_immut_addr=0x{:x} relro_addr=0x{:x} data_addr=0x{:x} bss_addr=0x{:x} promo_addr=0x{:x}",
        ro_addr,
        zero_immut_addr,
        relro_addr,
        data_addr,
        bss_addr,
        promo.as_ptr() as usize
    );

    if mode == "write_rodata" {
        let p = ro_addr as *mut u8;
        unsafe { std::ptr::write_volatile(p, 0x00) };
    } else if mode == "write_relro" {
        let p = relro_addr as *mut usize;
        unsafe { std::ptr::write_volatile(p, 0x1234) };
    }
}
