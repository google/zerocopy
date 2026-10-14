#![crate_type = "lib"]
use std::arch::asm;

// These declarations are compiled only. Their false contracts must never be executed.
pub unsafe fn false_nomem(p: *mut u64) {
    unsafe { asm!("str {v}, [{p}]", v = in(reg) 1u64, p = in(reg) p,
                  options(nomem, nostack)); }
}

pub unsafe fn false_preserves_flags(a: u64) {
    unsafe { asm!("cmp {a}, #0", a = in(reg) a,
                  options(nomem, nostack, preserves_flags)); }
}
