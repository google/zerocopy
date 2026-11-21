#![no_std]
#![crate_type = "rlib"]
#![crate_name = "nostd_callee"]

#[used]
#[no_mangle]
pub static NOSTD_CALIBRATION_WORDS: [u64; 4] = [10, 20, 12, 0];

/// Non-inlined cross-crate callee: caller emits `call *nostd_sum_calibration@GOTPCREL(%rip)` (`ff 15`)
/// unless `-Z relax-elf-relocations=yes` upgrades the call relocation to `R_X86_64_GOTPCRELX` (`67 e8`).
#[inline(never)]
#[no_mangle]
pub fn nostd_sum_calibration(seed: u64) -> u64 {
    let p = core::ptr::addr_of!(NOSTD_CALIBRATION_WORDS);
    let arr = unsafe { core::ptr::read_volatile(p) };
    seed.wrapping_add(arr[0]).wrapping_add(arr[1]).wrapping_add(arr[2])
}

/// Inlined cross-crate data reader: eliminates the cross-crate `call *got` so `_start` contains ONLY
/// the cross-crate `mov reg, NOSTD_CALIBRATION_WORDS@GOTPCREL(%rip)` (`48 8b`) data-address load,
/// isolating `GNU ld` (`48 8b -> 48 8d` `lea` relaxation) vs. `rust-lld` (unrelaxed `48 8b` `SIGSEGV`).
#[inline(always)]
pub fn nostd_sum_calibration_inline(seed: u64) -> u64 {
    let p = core::ptr::addr_of!(NOSTD_CALIBRATION_WORDS);
    let arr = unsafe { core::ptr::read_volatile(p) };
    seed.wrapping_add(arr[0]).wrapping_add(arr[1]).wrapping_add(arr[2])
}
