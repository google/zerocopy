use core::arch::asm;
use core::hint::black_box;

#[inline(never)]
pub unsafe fn leaf_with_nostack(a: u64, b: u64) -> u64 {
    let mut x = a;
    let mut y = b;
    let px: *const u64 = &x;
    let py: *const u64 = &y;
    unsafe {
        let sentinel: u64 = 0xdeadbeef_00000000u64;
        asm!(
            "push {s}",
            "push {s}",
            "pop {t}",
            "pop {t}",
            s = in(reg) sentinel,
            t = out(reg) _,
            options(nostack),
        );
        core::ptr::read_volatile(px) ^ core::ptr::read_volatile(py)
    }
}

#[inline(never)]
pub unsafe fn leaf_without_nostack(a: u64, b: u64) -> u64 {
    let mut x = a;
    let mut y = b;
    let px: *const u64 = &x;
    let py: *const u64 = &y;
    unsafe {
        let sentinel: u64 = 0xdeadbeef_00000000u64;
        asm!(
            "push {s}",
            "push {s}",
            "pop {t}",
            "pop {t}",
            s = in(reg) sentinel,
            t = out(reg) _,
        );
        core::ptr::read_volatile(px) ^ core::ptr::read_volatile(py)
    }
}

fn main() {
    let a = black_box(0x1111_2222_3333_4444u64);
    let b = black_box(0x5555_6666_7777_8888u64);
    let expected = a ^ b;
    let got_nostack = unsafe { leaf_with_nostack(a, b) };
    let got_safe = unsafe { leaf_without_nostack(a, b) };
    println!(
        "EXPECTED=0x{:x} NOSTACK=0x{:x} WITHOUT_NOSTACK=0x{:x} CLOBBERED={}",
        expected,
        got_nostack,
        got_safe,
        got_nostack != expected
    );
}
