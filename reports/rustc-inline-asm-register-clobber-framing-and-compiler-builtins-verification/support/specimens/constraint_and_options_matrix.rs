#![no_std]
#![feature(asm_unwind)]

use core::arch::{asm, global_asm, naked_asm};

#[inline(never)]
pub extern "C" fn helper_target(x: u64) -> u64 {
    x.wrapping_add(1)
}

#[unsafe(no_mangle)]
pub unsafe fn probe_out_early_clobber(x: u64) -> u64 {
    let y: u64;
    unsafe {
        asm!(
            "mov {out}, {inp}",
            inp = in(reg) x,
            out = out(reg) y,
            options(pure, nomem, nostack)
        );
    }
    y
}

#[unsafe(no_mangle)]
pub unsafe fn probe_lateout(x: u64) -> u64 {
    let y: u64;
    unsafe {
        asm!(
            "mov {out}, {inp}",
            inp = in(reg) x,
            out = lateout(reg) y,
            options(pure, nomem, nostack)
        );
    }
    y
}

#[unsafe(no_mangle)]
pub unsafe fn probe_inout_reg(mut x: u64) -> u64 {
    unsafe {
        #[cfg(target_arch = "x86_64")]
        asm!("add {0}, 1", inout(reg) x, options(nomem, nostack));
        #[cfg(target_arch = "aarch64")]
        asm!("add {0}, {0}, #1", inout(reg) x, options(nomem, nostack));
    }
    x
}

#[unsafe(no_mangle)]
pub unsafe fn probe_inlateout_reg(mut x: u64) -> u64 {
    unsafe {
        #[cfg(target_arch = "x86_64")]
        asm!("add {0}, 1", inlateout(reg) x, options(nomem, nostack));
        #[cfg(target_arch = "aarch64")]
        asm!("add {0}, {0}, #1", inlateout(reg) x, options(nomem, nostack));
    }
    x
}

#[cfg(target_arch = "x86_64")]
#[unsafe(no_mangle)]
pub unsafe fn probe_inlateout_fixed(mut x: u64) -> u64 {
    unsafe {
        asm!("add rax, 1", inlateout("rax") x, options(nomem, nostack));
    }
    x
}

#[cfg(target_arch = "aarch64")]
#[unsafe(no_mangle)]
pub unsafe fn probe_inlateout_fixed(mut x: u64) -> u64 {
    unsafe {
        asm!("add x0, x0, #1", inlateout("x0") x, options(nomem, nostack));
    }
    x
}

#[unsafe(no_mangle)]
pub unsafe fn probe_sym_and_const() -> u64 {
    let out: u64;
    unsafe {
        #[cfg(target_arch = "x86_64")]
        asm!(
            "lea {out}, [rip + {f}]",
            "add {out}, {c}",
            f = sym helper_target,
            c = const 7u64,
            out = out(reg) out,
            options(pure, nomem, nostack)
        );
        #[cfg(all(target_arch = "aarch64", not(target_vendor = "apple")))]
        asm!(
            "adrp {out}, {f}",
            "add {out}, {out}, :lo12:{f}",
            "add {out}, {out}, #{c}",
            f = sym helper_target,
            c = const 7u64,
            out = out(reg) out,
            options(pure, nomem, nostack)
        );
        #[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
        asm!(
            "adrp {out}, {f}@PAGE",
            "add {out}, {out}, {f}@PAGEOFF",
            "add {out}, {out}, #{c}",
            f = sym helper_target,
            c = const 7u64,
            out = out(reg) out,
            options(pure, nomem, nostack)
        );
    }
    out
}

#[unsafe(no_mangle)]
pub unsafe fn probe_opts_default(x: u64) -> u64 {
    let y: u64;
    unsafe { asm!("mov {0}, {1}", out(reg) y, in(reg) x); }
    y
}

#[unsafe(no_mangle)]
pub unsafe fn probe_opts_nostack(x: u64) -> u64 {
    let y: u64;
    unsafe { asm!("mov {0}, {1}", out(reg) y, in(reg) x, options(nostack)); }
    y
}

#[unsafe(no_mangle)]
pub unsafe fn probe_opts_preserves_flags(x: u64) -> u64 {
    let y: u64;
    unsafe { asm!("mov {0}, {1}", out(reg) y, in(reg) x, options(preserves_flags, nostack)); }
    y
}

#[unsafe(no_mangle)]
pub unsafe fn probe_opts_nomem(x: u64) -> u64 {
    let y: u64;
    unsafe { asm!("mov {0}, {1}", out(reg) y, in(reg) x, options(nomem, nostack)); }
    y
}

#[unsafe(no_mangle)]
pub unsafe fn probe_opts_readonly(x: u64) -> u64 {
    let y: u64;
    unsafe { asm!("mov {0}, {1}", out(reg) y, in(reg) x, options(readonly, nostack)); }
    y
}

#[unsafe(no_mangle)]
pub unsafe fn probe_opts_pure_nomem_dce_cse(x: u64) -> u64 {
    let _dead: u64;
    let a: u64;
    let b: u64;
    unsafe {
        asm!("mov {0}, {1}", out(reg) _dead, in(reg) x, options(pure, nomem, nostack));
        asm!("mov {0}, {1}", out(reg) a, in(reg) x, options(pure, nomem, nostack));
        asm!("mov {0}, {1}", out(reg) b, in(reg) x, options(pure, nomem, nostack));
    }
    a.wrapping_add(b)
}

#[unsafe(no_mangle)]
pub unsafe fn probe_opts_pure_readonly(x: u64) -> u64 {
    let y: u64;
    unsafe { asm!("mov {0}, {1}", out(reg) y, in(reg) x, options(pure, readonly, nostack)); }
    y
}

#[unsafe(no_mangle)]
pub unsafe fn probe_opts_noreturn() -> ! {
    unsafe { asm!("nop", options(noreturn)); }
}

pub struct UnwindDropGuard<'a>(pub &'a mut u64);
impl Drop for UnwindDropGuard<'_> {
    #[inline(never)]
    fn drop(&mut self) {
        *self.0 = self.0.wrapping_add(1);
    }
}

#[unsafe(no_mangle)]
pub unsafe fn probe_opts_may_unwind(flag: &mut u64) {
    let _g = UnwindDropGuard(flag);
    unsafe {
        asm!("nop", options(may_unwind, nostack));
    }
}

#[unsafe(no_mangle)]
pub unsafe fn probe_clobber_abi_c() {
    unsafe {
        asm!("nop", clobber_abi("C"));
    }
}

#[cfg(target_arch = "x86_64")]
#[unsafe(no_mangle)]
pub unsafe fn probe_clobber_abi_sysv64() {
    unsafe { asm!("nop", clobber_abi("sysv64")); }
}

#[cfg(target_arch = "x86_64")]
#[unsafe(no_mangle)]
pub unsafe fn probe_clobber_abi_win64() {
    unsafe { asm!("nop", clobber_abi("win64")); }
}

#[cfg(target_arch = "x86_64")]
#[unsafe(naked)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_naked_identity(x: usize) -> usize {
    naked_asm!("mov rax, rdi", "ret")
}

#[cfg(target_arch = "aarch64")]
#[unsafe(naked)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_naked_identity(x: usize) -> usize {
    naked_asm!("ret")
}

#[cfg(all(target_arch = "x86_64", not(target_os = "windows")))]
global_asm!(
    ".globl probe_global_asm_add42",
    ".type probe_global_asm_add42, @function",
    "probe_global_asm_add42:",
    "lea rax, [rdi + 42]",
    "ret",
);

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
global_asm!(
    ".globl probe_global_asm_add42",
    "probe_global_asm_add42:",
    "lea rax, [rcx + 42]",
    "ret",
);

#[cfg(all(target_arch = "aarch64", not(target_vendor = "apple")))]
global_asm!(
    ".globl probe_global_asm_add42",
    ".type probe_global_asm_add42, @function",
    "probe_global_asm_add42:",
    "add x0, x0, #42",
    "ret",
);

#[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
global_asm!(
    ".globl _probe_global_asm_add42",
    "_probe_global_asm_add42:",
    "add x0, x0, #42",
    "ret",
);
