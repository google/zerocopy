#![allow(dead_code)]
use std::arch::{asm, naked_asm};

#[unsafe(no_mangle)]
pub extern "C" fn rust_add(a: u64, b: u64) -> u64 { a.wrapping_add(b) }

#[unsafe(no_mangle)]
pub extern "C" fn inline_add(a: u64, b: u64) -> u64 {
    let out: u64;
    unsafe { asm!("add {out}, {a}, {b}", out = lateout(reg) out,
                  a = in(reg) a, b = in(reg) b, options(pure, nomem, nostack)); }
    out
}

#[unsafe(naked)]
#[unsafe(no_mangle)]
pub extern "C" fn naked_add(_a: u64, _b: u64) -> u64 {
    naked_asm!("sub x0, x0, x1", "ret");
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn inline_load(p: *const u8) -> u8 {
    let out: u32;
    unsafe { asm!("ldrb {out:w}, [{p}]", out = lateout(reg) out,
                  p = in(reg) p, options(readonly, nostack)); }
    out as u8
}

#[unsafe(naked)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn naked_store(_p: *mut u64, _v: u64) {
    naked_asm!("str x1, [x0]", "ret");
}

#[repr(C)]
pub struct Pair { pub a: u64, pub b: u64 }

#[unsafe(no_mangle)]
pub extern "C" fn c_pair(a: Pair) -> Pair { Pair { a: a.b, b: a.a } }

#[unsafe(no_mangle)]
pub fn rust_pair(a: (u64, u64)) -> (u64, u64) { (a.1, a.0) }

#[repr(C)]
pub struct Triple { pub a: u64, pub b: u64, pub c: u64 }

#[unsafe(no_mangle)]
pub extern "C" fn c_triple(a: Triple) -> Triple { Triple { a: a.c, b: a.b, c: a.a } }

#[unsafe(no_mangle)]
pub fn rust_slice(a: &[u8]) -> usize { a.len() }

#[unsafe(no_mangle)]
pub fn rust_unit(_: ()) -> () {}

fn main() {
    let edges = [0, 1, 255, 256, u32::MAX as u64, 1 << 32,
                 (1 << 63) - 1, 1 << 63, u64::MAX - 1, u64::MAX];
    let mut count = 0;
    for a in edges { for b in edges {
        assert_eq!(inline_add(a,b), rust_add(a,b));
        assert_eq!(naked_add(a,b), rust_add(a,b));
        count += 1;
    }}
    let mut x: u64 = 0x9e3779b97f4a7c15;
    for _ in 0..8192 {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        let y = x.rotate_left(29).wrapping_mul(0xd6e8feb86659fd93);
        assert_eq!(inline_add(x,y), rust_add(x,y));
        assert_eq!(naked_add(x,y), rust_add(x,y));
        count += 1;
    }
    for byte in 0u8..=255 {
        let original = [13u8, byte, 29];
        let loaded = unsafe { inline_load(original.as_ptr().add(1)) };
        assert_eq!(loaded, byte);
        assert_eq!(original, [13u8, byte, 29]);
    }
    for value in edges {
        let mut frame = [17u64, 0, 29];
        unsafe { naked_store(&mut frame[1], value); }
        assert_eq!(frame, [17, value, 29]);
    }
    println!("{{\"arithmetic_inputs\":{count},\"arithmetic_implementations\":2,\"byte_load_inputs\":256,\"store_inputs\":10,\"host\":\"aarch64-apple-darwin\"}}");
}
