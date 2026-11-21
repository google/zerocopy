#![no_std]
#![no_main]

extern crate nostd_callee;

use core::arch::asm;
use core::panic::PanicInfo;

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    unsafe {
        asm!(
            "mov eax, 60",
            "mov edi, 99",
            "syscall",
            options(noreturn)
        );
    }
}

/// Minimal freestanding `-static-pie` entry point without a `_DYNAMIC` `R_X86_64_RELATIVE` self-relocator.
/// - With `--cfg nostd_inline_data`: `_start` loads `NOSTD_CALIBRATION_WORDS` directly across the crate
///   boundary via `R_X86_64_GOTPCREL` (`mov -> lea` on `GNU ld` => `EXIT_OK`; unrelaxed `mov` on `rust-lld` => `SIGSEGV`).
/// - Without `--cfg nostd_inline_data`: `_start` also performs a cross-crate `call *nostd_sum_calibration@GOTPCREL(%rip)`
///   (`ff 15`), which NEITHER `GNU ld` nor `rust-lld` can relax unless `-Z relax-elf-relocations=yes` emits `R_X86_64_GOTPCRELX` (`67 e8`)!
#[no_mangle]
pub unsafe extern "C" fn _start() -> ! {
    #[cfg(nostd_inline_data)]
    let val = nostd_callee::nostd_sum_calibration_inline(0);

    #[cfg(not(nostd_inline_data))]
    let val = nostd_callee::nostd_sum_calibration(0);

    let code: u64 = if val == 42 { 0 } else { 1 };
    unsafe {
        asm!(
            "mov rax, 60",
            "syscall",
            in("rdi") code,
            options(noreturn)
        );
    }
}
